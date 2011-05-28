require "pp"
require "test/unit"
require "cgi"

# (C) Thomas Fritzsche May, 2011
module Parser
  
  class Match
    attr_accessor :token,:name,:children
    def initialize( token="", children = nil , name = nil)
      @token = token
      @children = children
      @name = name
    end

    def compact
      # leaves of the tree
      if children.nil? || children.length == 0
        return name.nil? ? token : { name => token }
      end
      # compact sub-tree
      comp_list = children.collect { |c| c.compact }
      comp_list.compact!
      if comp_list.length == 1
        return name.nil? ? comp_list[0] : { name => comp_list[0]}
      end
      if comp_list.any?{|l| l.instance_of?(Hash) or l.instance_of?(Array) }
        comp_list = comp_list.delete_if do
          |l| not (l.instance_of?(Hash) or l.instance_of?(Array))
        end
        if comp_list.length == 1
          return name.nil? ? comp_list[0] : { name => comp_list[0]}
        end
        return name.nil? ?  comp_list : { name => comp_list }
      else
        return name.nil? ? comp_list.join : { name => comp_list.join }

      end
    end
  end

  def match(reg,&block)
    if reg.class == Symbol
      lambda{ |str|
        return nil if block && block.call == false
        self.send(reg,str)
      }
    else
      lambda{ |str|
        return nil if block && block.call == false
        if (str=~reg) == 0
          Match.new $~.to_s
        else
          return nil
        end
      }
    end
  end

  def seq(*lb,&block)
    lambda{ |str|
      return nil if block && block.call == false
      tmp = str
      children = []
      token = ""
      result = lb.each{ |l|
        match = l.call(tmp)
        break nil if match.nil?
        children << match
        token += match.token
        tmp = str[token.length..-1]
      }
      return nil if result == nil
      Match.new(token,children)
    }
  end

  def choice(*lb,&block)
    lambda{ |str|
      return nil if block && block.call == false
      match = nil
      lb.each{ |l|
        match = l.call(str)
        break unless match.nil?
      }
      return match
    }
  end

  def repeat(rep,min=0,max=nil,&block)
    lambda{ |str|      
      return nil if block && block.call == false
      if str.nil? || str.length == 0
        if min == 0
          return Match.new("")
        else
          return nil
        end
      end
      tmp = str
      n = 0
      children = []
      token = ""
      loop do
        match = rep.call(tmp)
        break if match.nil?
        token += match.token
        children << match
        n = n+1
        break if(!max.nil? && max <= n)
        tmp = str[token.length..-1]
      end
      if  ( min != 0 && n < min ) || ( max != nil && n > max)
        return nil
      end
      Match.new(token,children)
    }
  end

  def present?(exp,&block)
    lambda{ |str|
      return nil if block && block.call == false
      match = exp.call(str)
      return nil if match.nil?
      match.token = ""
      return match
    }
  end

  def absent?(exp,&block)
    lambda{ |str|
      return nil if block && block.call == false
      match = exp.call(str)
      return nil unless match.nil?
      return Match.new("")
    }
  end

  def as(name,exp,&block)
    lambda{ |str|
      return nil if block && block.call == false
      match = exp.call(str)
      return nil if match.nil?
      match.name = name
      return match
    }
  end

  def matched?(pr,&block)
    lambda{ |str|
      m = pr.call(str)
      block.call(m) if block
      m
    }
  end

  def eof(&block)
    lambda{ |str|
      return nil if block && block.call == false
      return Match.new if str.nil? or str == ""
      return nil
    }
  end

  def transform(ast,trans = self)
    if ast.instance_of?(String)
      return ast
    end

    if ast.instance_of?(Hash)
      list = []
      ast.each_pair{|key,value|
        before_method = ("before_"+key.to_s).to_sym
        if trans.respond_to?(before_method)
          trans.send(before_method,ast)
        end
        val_str = transform(value,trans)
        if trans.respond_to?(key)
          no_par = trans.method(key).arity
          if no_par == 2
            list << trans.send(key,val_str,ast)
          else
            if no_par == 1
              list << trans.send(key,val_str)
            else
              list << trans.send(key)
            end
          end
        end
      }
      return list.join
    end
    if ast.instance_of?(Array)
      list = ast.collect{|value|
        val_str = transform(value,trans)
      }
      return list.join
    end
  end
end

#===============================================

class TextileScanner

  class HtmlCoverter
    module HtmlCoverterModule
      def block(str,ast)
        begin
          block_modifier = ast[:block].find{|h| h[:block_modifier]}[:block_modifier]
        rescue
          block_modifier = "p"
        end
        case block_modifier
        when "bq"
          block_modifier = "blockquote"
        end

        "<#{block_modifier}>#{str}</#{block_modifier}>"
      end

      def block_modifier
        ""
      end

      def newline
        "<br />"
      end

      def em_dash
        "&#8212;"
      end
      def en_dash
        " &#8211; "
      end
      def ellipsis
        "&#8230;"
      end
      def copyright
        "&#169;"
      end
      def trademark
        "&#8482;"
      end
      def registered
        "&#174;"
      end
      def dimension
        "&#215;"
      end

      def inline_text(str)
        str
      end
      def strong_phrase(str)
        "<strong>#{str}</strong>"
      end
      def emphasis_phrase(str)
        "<em>#{str}</em>"
      end
      def italic_phrase(str)
        "<i>#{str}</i>"
      end
      def inline_char(str)
        str
      end

      def escape(str)
        CGI.escapeHTML(str)
      end

      def before_bullet_list(ast)
        @@list_tag = 'ul'
        @@list_depth = 0
      end
      def bullet_list(str)
        return str+"</li></#{@@list_tag}>"*@@list_depth
      end

      def bullet(str)
        @@list_delta = str.length - @@list_depth
        @@list_depth = str.length
        ""
      end

      def before_ordered_list(ast)
        @@list_tag = 'ol'
        @@list_depth = 0
      end
      def ordered_list(str)
        return str+"</li></#{@@list_tag}>"*@@list_depth
      end
      def list_item(str)
        if @@list_delta > 0
          result = "<#{@@list_tag}><li>"*@@list_delta+str
        end
        if @@list_delta == 0
          result = "</li><li>#{str}"
        end
        if @@list_delta < 0
          result = "</li>"+("</#{@@list_tag}></li>"*(@@list_delta * -1))+"<li>"+str
        end
        result
      end
    end
    extend HtmlCoverterModule
  end

  extend Parser

  NEWLINE           = match(/\n/)
  DOUBLE_NEWLINE    = repeat(NEWLINE,2,2)
  SPACE             = match(/\s/)
  DOT               = match(/\./)
  DOUBLE_DOT        = match(/\.\./)

  BULLET            = as(:bullet,repeat(match(/\*/),1))
  COUNTER           = as(:bullet,repeat(match(/\#/),1))

  HEADER_BLOCK      = match(/h[1-6]/)
  PARAGRAPH_BLOCK   = match(/p/)
  BLOCKQUOTE        = as(:blockquote, match(/bq/))

  BLOCK_TAG         = choice(BLOCKQUOTE, HEADER_BLOCK, PARAGRAPH_BLOCK)
  INLINE_CHAR_END   = absent?(choice(repeat(NEWLINE,2,2){ @@extended ? false : true },
                      seq(DOUBLE_NEWLINE,BLOCK_TAG,DOT,repeat(SPACE,1)){@@extended ? true : false }))

  INLINE_CHAR       = seq(INLINE_CHAR_END,choice(as(:escape,match(/./)),seq(as(:newline,NEWLINE),absent?(choice(BULLET,COUNTER)))))

  STRONG_PHRASE     = seq(match(/\*/),as(:strong_phrase,repeat(seq(absent?(match(/\*/)),match(:inline_element)))),match(/\*/))
  EMPHASIS_PHRASE   = seq(match(/\_/),as(:emphasis_phrase,repeat(seq(absent?(match(/\_/)),match(:inline_element)))),match(/\_/))
  ITALIC_PHRASE     = seq(match(/__/),as(:italic_phrase,repeat(seq(absent?(match(/__/)),match(:inline_element)))),match(/__/))

  INLINE_TEXT       = as(:inline_text,repeat(match(:inline_element),1))


  EXTENDED_BLOCK    = matched?(DOUBLE_DOT){ |m| m.nil? ? @@extended = false : @@extended = true  }
  BLOCK_MODIFIER    = repeat(seq(as(:block_modifier, BLOCK_TAG), choice( EXTENDED_BLOCK, DOT),repeat(SPACE,1)),0,1)


  BULLET_LIST_ITEM  = seq( repeat(NEWLINE), BULLET ,repeat(SPACE,1), as(:list_item, INLINE_TEXT ))
  BULLET_LIST       = as(:bullet_list,repeat(BULLET_LIST_ITEM,1))

  ORDERED_LIST_ITEM = seq( repeat(NEWLINE), COUNTER ,repeat(SPACE,1), as(:list_item, INLINE_TEXT ))
  ORDERED_LIST      = as(:ordered_list,repeat(ORDERED_LIST_ITEM,1))

  EM_DASH           = as(:em_dash, match(/\-\-/))
  EN_DASH           = as(:en_dash, match(/ \- /))
  ELLIPSIS          = as(:ellipsis, match(/\.\.\./))
  TRADEMARK         = as(:trademark, match(/\(tm\)/))
  REGISTERED        = as(:registered, match(/\(r\)/))
  COPYRIGHT         = as(:copyright, match(/\(c\)/))
  DIMENSION         = seq(as(:inline_text,seq(match(/\d/),repeat(SPACE))),as(:dimension,match(/x/)),present?(seq(repeat(SPACE),match(/\d/))))
 
  def self.inline_element(str)
    choice(DIMENSION,COPYRIGHT,REGISTERED,TRADEMARK,ELLIPSIS,EM_DASH,EN_DASH,ITALIC_PHRASE,STRONG_PHRASE,EMPHASIS_PHRASE,as(:inline_char,INLINE_CHAR)).call(str)
  end

  def self.block(str)
    @@extended = false
    seq(repeat(DOUBLE_NEWLINE),choice(ORDERED_LIST,BULLET_LIST,
        as(:block,seq(BLOCK_MODIFIER,INLINE_TEXT))),
      repeat(DOUBLE_NEWLINE)).call(str)
  end

  def self.root(str)
    repeat(match(:block)).call(str)
  end

  def self.to_html(str)
    r = root(str).compact
    transform(r,HtmlCoverter)
  end
end
#================================



class TestTextileScanner < Test::Unit::TestCase
  def test_simple
    assert_equal("<p>123</p>",TextileScanner.to_html("123"))
    assert_equal("<p>a</p><p>b</p>",TextileScanner.to_html("a\n\nb"))
    assert_equal("<p>a<br />b</p>",TextileScanner.to_html("a\nb"))
    assert_equal("<p>a</p><p>b</p><p>c</p>",TextileScanner.to_html("a\n\nb\n\nc"))
    assert_equal("<p>123</p>",TextileScanner.to_html("\n\n123"))
  end

  def test_phrase
    assert_equal("<p><strong>12</strong></p>",TextileScanner.to_html("*12*"))
    assert_equal("<p>a<strong>12</strong>b</p>",TextileScanner.to_html("a*12*b"))
    assert_equal("<p>a*12</p>",TextileScanner.to_html("a*12"))
    assert_equal("<p><em>emphasis</em></p>",TextileScanner.to_html("_emphasis_"))
    assert_equal("<p><em><strong>12</strong></em></p>",TextileScanner.to_html("_*12*_"))
    assert_equal("<p>_<strong>12_</strong></p>",TextileScanner.to_html("_*12_*"))
    assert_equal("<p><i>italic</i></p>",TextileScanner.to_html("__italic__"))
  end

  def test_block
    assert_equal("<h1>test</h1>",TextileScanner.to_html("h1. test"))
    assert_equal("<h1>test</h1><p>test2</p>",TextileScanner.to_html("h1. test\n\ntest2"))
    assert_equal("<p>test</p>",TextileScanner.to_html("p. test"))
    assert_equal("<blockquote>test</blockquote>",TextileScanner.to_html("bq. test"))
    assert_equal("<p>123</p>",TextileScanner.to_html("\n\n123"))
    assert_equal("<p>a</p><p>b</p><p>c</p>",TextileScanner.to_html("a\n\nb\n\nc"))
  end

  def test_extended_block
    assert_equal("<h1>test<br /><br />test2</h1>",TextileScanner.to_html("h1.. test\n\ntest2"))
  end

  def test_escape
    assert_equal("<p>&lt;br /&gt;</p>",TextileScanner.to_html("<br />"))
  end

  def test_punctuation
    assert_equal("<p>a &#8212; b</p>",TextileScanner.to_html("a -- b"))
    assert_equal("<p>a &#8211; b</p>",TextileScanner.to_html("a - b"))
    assert_equal("<p>a-b</p>",TextileScanner.to_html("a-b"))
    assert_equal("<p>Meanwhile&#8230;</p>",TextileScanner.to_html("Meanwhile..."))
    assert_equal("<p>Registered&#174; Trademark&#8482; Copyright &#169;.</p>",TextileScanner.to_html("Registered(r) Trademark(tm) Copyright (c)."))
    assert_equal("<p>1 &#215; 2 &#215; 3 = 6</p>",TextileScanner.to_html("1 x 2 x 3 = 6"))
    assert_equal("<p>1&#215;2&#215;3 = 6</p>",TextileScanner.to_html("1x2x3 = 6"))
  end

  def test_list
    assert_equal("<ul><li>one</li><li>two</li></ul>",TextileScanner.to_html("* one\n* two"))
    assert_equal("<ul><li>one<ul><li>two</li></ul></li></ul>",TextileScanner.to_html("* one\n** two"))
    assert_equal("<ul><li>one</li><li>two</li><li>tree</li></ul>",TextileScanner.to_html("* one\n* two\n* tree"))
    assert_equal("<ul><li>one<ul><li>two</li></ul></li><li>tree</li></ul>",TextileScanner.to_html("* one\n** two\n* tree"))

    assert_equal("<ol><li>one</li><li>two</li></ol>",TextileScanner.to_html("# one\n# two"))
    test = TextileScanner.to_html("# Item one\n## Item one-A\n## Item one-B\n### Item one-B-a\n# Item two")
    assert_equal("<ol><li>Item one<ol><li>Item one-A</li><li>Item one-B<ol><li>Item one-B-a</li></ol></li></ol></li><li>Item two</li></ol>",test)
  end
end


class SimpleScanner
  extend Parser

  def self.last_part
    lambda{ |str|
      match(/c/).call(str)
    }
  end

  def self.node(str)
    match(/c/).call(str)
  end

  def self.root(str)
    seq(match(/a/),match(/b/),last_part)
  end

  def self.simple(str)
    match(:node).call(str)
  end

  def self.test_seq(str)
    seq(match(/a/),match(/b/)).call(str)
  end

  def self.test_choice(str)
    choice(match(/a/),match(/b/)).call(str)
  end

  def self.test_block(str)
    i = 0
    result = repeat(as(:name,match(/a/)){
        if i == 3
          false
        else
          i += 1
          true
        end
      }).call(str)      
    result
  end
end


class TestParser < Test::Unit::TestCase
  include Parser

  def show(str)
    "<#{str}>"
  end

  def test_basic
    assert_equal("aaa",repeat(match(/a/)).call("aaa").compact)
    assert_equal({:test=>"aaa"},as(:test,repeat(match(/a/))).call("aaa").compact)
    assert_equal([{:name=>"a"}, {:name=>"a"}, {:name=>"a"}],repeat(as(:name,match(/a/))).call("aaa").compact)
    s = seq(match(/a/),as(:test,match(/b/)),match(/c/))
    assert_equal({:test=>"b"},s.call("abc").compact)
  end

  def test_transform
    test1 = as(:show,repeat(match(/a/))).call("aaa").compact
    assert_equal("<aaa>",transform(test1))
    test2 = repeat(as(:show,match(/a/))).call("aaa").compact
    assert_equal("<a><a><a>",transform(test2))
    test3 =  seq(match(/a/),as(:show,match(/b/)),match(/c/)).call("abc").compact
    assert_equal("<b>",transform(test3))
  end
end

class TestScanner < Test::Unit::TestCase
  def test_simple
    SimpleScanner.root("ab")
    SimpleScanner.simple("a")
    assert_equal("ab",SimpleScanner.test_seq("ab").token)
    assert_equal(nil,SimpleScanner.test_seq("ac"))
    assert_equal("b",SimpleScanner.test_choice("b").token)
    assert_equal(nil,SimpleScanner.test_choice("c"))
    assert_equal("aaa",SimpleScanner.test_block("aaaa").token)    
  end
end