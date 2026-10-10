import Mathlib
import OAI.Geometry.CubicTorus.Profiles.ValueEnclosures726To944

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape
lemma b944 : Encl e944 (6 : ℝ) (6 : ℝ) := by
  exact Encl.exact (6 : ℝ)

def e945 : ℝ := e944 * e942
lemma b945 : Encl e945 (26662851 / 31250000 : ℝ) (26662851 / 31250000 : ℝ) := by
  exact Encl.mul_nonneg b944 b942 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e946 : ℝ := e937 ^ 2
lemma b946 : Encl e946 (388259022273 / 200000000000 : ℝ) (1941295111377 / 1000000000000 : ℝ) := by
  exact Encl.pow b937 (by norm_num) 2 (by norm_num) (by norm_num)

def e947 : ℝ := e945 * e946
lemma b947 : Encl e947 (1656334793643 / 1000000000000 : ℝ) (828167396827 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b945 b946 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e948 : ℝ := e947 * e931
lemma b948 : Encl e948 (162396750433 / 500000000000 : ℝ) (162396750437 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b947 b931 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e949 : ℝ := e948 / e9
lemma b949 : Encl e949 (1159976788807 / 1000000000000 : ℝ) (289994197209 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b948 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e950 : ℝ := e5 + e949
lemma b950 : Encl e950 (2159976788807 / 1000000000000 : ℝ) (539994197209 / 250000000000 : ℝ) := by
  exact Encl.add b5 b949 (by norm_num) (by norm_num)

def e951 : ℝ := Real.sqrt e950
lemma b951 : Encl e951 (18371074363 / 12500000000 : ℝ) (1469685949051 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b950 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e952 : ℝ := e5 + e951
lemma b952 : Encl e952 (30871074363 / 12500000000 : ℝ) (2469685949051 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b951 (by norm_num) (by norm_num)

def e953 : ℝ := e943 / e952
lemma b953 : Encl e953 (1270391143 / 8000000000 : ℝ) (158798892879 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b943 b952 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e954 : ℝ := e10 ^ 3
lemma b954 : Encl e954 (9261 / 1000000 : ℝ) (9261 / 1000000 : ℝ) := by
  exact Encl.pow b10 (by norm_num) 3 (by norm_num) (by norm_num)

def e955 : ℝ := e942 * e954
lemma b955 : Encl e955 (82308221 / 62500000000 : ℝ) (1316931537 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b942 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e956 : ℝ := e931 - e953
lemma b956 : Encl e956 (37292804351 / 1000000000000 : ℝ) (18646402179 / 500000000000 : ℝ) := by
  exact Encl.sub b931 b953 (by norm_num) (by norm_num)

def e957 : ℝ := e956 / e937
lemma b957 : Encl e957 (26765740453 / 1000000000000 : ℝ) (26765740459 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b956 b937 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e958 : ℝ := e957 ^ 2
lemma b958 : Encl e958 (716404861 / 1000000000000 : ℝ) (716404863 / 1000000000000 : ℝ) := by
  exact Encl.pow b957 (by norm_num) 2 (by norm_num) (by norm_num)

def e959 : ℝ := e9 * e958
lemma b959 : Encl e959 (200593361 / 1000000000000 : ℝ) (100296681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b958 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e960 : ℝ := e953 ^ 3
lemma b960 : Encl e960 (1001111429 / 250000000000 : ℝ) (4004445717 / 1000000000000 : ℝ) := by
  exact Encl.pow b953 (by norm_num) 3 (by norm_num) (by norm_num)

def e961 : ℝ := e942 * e960
lemma b961 : Encl e961 (569439677 / 1000000000000 : ℝ) (284719839 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b942 b960 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e962 : ℝ := e959 + e961
lemma b962 : Encl e962 (385016519 / 500000000000 : ℝ) (9625413 / 12500000000 : ℝ) := by
  exact Encl.add b959 b961 (by norm_num) (by norm_num)

def e963 : ℝ := min e955 e962
lemma b963 : Encl e963 (385016519 / 500000000000 : ℝ) (9625413 / 12500000000 : ℝ) := by
  exact Encl.min b955 b962 (by norm_num) (by norm_num)

def e964 : ℝ := (53 / 50 : ℝ)
lemma b964 : Encl e964 (53 / 50 : ℝ) (53 / 50 : ℝ) := by
  exact Encl.exact (53 / 50 : ℝ)

def e965 : ℝ := e964 / e0
lemma b965 : Encl e965 (168704239677 / 500000000000 : ℝ) (67481695871 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b964 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e966 : ℝ := e964 * e7
lemma b966 : Encl e966 (180647880161 / 250000000000 : ℝ) (722591520647 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b964 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e967 : ℝ := e8 * e964
lemma b967 : Encl e967 (2597 / 2500 : ℝ) (2597 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b964 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e968 : ℝ := e967 / e0
lemma b968 : Encl e968 (330660309767 / 1000000000000 : ℝ) (41332538721 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b967 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e969 : ℝ := e964 ^ 2
lemma b969 : Encl e969 (2809 / 2500 : ℝ) (2809 / 2500 : ℝ) := by
  exact Encl.pow b964 (by norm_num) 2 (by norm_num) (by norm_num)

def e970 : ℝ := e17 * e969
lemma b970 : Encl e970 (2809 / 625 : ℝ) (2809 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b969 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e971 : ℝ := e970 / e0
lemma b971 : Encl e971 (89413247029 / 62500000000 : ℝ) (286122390493 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b970 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e972 : ℝ := e5 + e971
lemma b972 : Encl e972 (151913247029 / 62500000000 : ℝ) (486122390493 / 200000000000 : ℝ) := by
  exact Encl.add b5 b971 (by norm_num) (by norm_num)

def e973 : ℝ := Real.sqrt e972
lemma b973 : Encl e973 (15590419983 / 10000000000 : ℝ) (1559041998301 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b972 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e974 : ℝ := e5 + e973
lemma b974 : Encl e974 (25590419983 / 10000000000 : ℝ) (2559041998301 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b973 (by norm_num) (by norm_num)

def e975 : ℝ := e23 / e974
lemma b975 : Encl e975 (195385617091 / 250000000000 : ℝ) (156308493673 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b974 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e976 : ℝ := e9 * e975
lemma b976 : Encl e976 (218831891141 / 1000000000000 : ℝ) (218831891143 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b975 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e977 : ℝ := e968 + e976
lemma b977 : Encl e977 (137373050227 / 250000000000 : ℝ) (549492200911 / 1000000000000 : ℝ) := by
  exact Encl.add b968 b976 (by norm_num) (by norm_num)

def e978 : ℝ := e977 - e5
lemma b978 : Encl e978 (-112626949773 / 250000000000 : ℝ) (-450507799089 / 1000000000000 : ℝ) := by
  exact Encl.sub b977 b5 (by norm_num) (by norm_num)

def e979 : ℝ := e0 / e969
lemma b979 : Encl e979 (2796006277669 / 1000000000000 : ℝ) (279600627767 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b969 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e980 : ℝ := e965 ^ 2
lemma b980 : Encl e980 (113844481939 / 1000000000000 : ℝ) (113844481941 / 1000000000000 : ℝ) := by
  exact Encl.pow b965 (by norm_num) 2 (by norm_num) (by norm_num)

def e981 : ℝ := e5 - e980
lemma b981 : Encl e981 (886155518059 / 1000000000000 : ℝ) (886155518061 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b980 (by norm_num) (by norm_num)

def e982 : ℝ := Real.sqrt e981
lemma b982 : Encl e982 (941358336691 / 1000000000000 : ℝ) (941358336693 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b981 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e983 : ℝ := e29 - e982
lemma b983 : Encl e983 (-274691670027 / 1000000000000 : ℝ) (-34336458753 / 125000000000 : ℝ) := by
  exact Encl.sub b29 b982 (by norm_num) (by norm_num)

def e984 : ℝ := e982 ^ 3
lemma b984 : Encl e984 (52136867783 / 62500000000 : ℝ) (417094942267 / 500000000000 : ℝ) := by
  exact Encl.pow b982 (by norm_num) 3 (by norm_num) (by norm_num)

def e985 : ℝ := e984 / e35
lemma b985 : Encl e985 (139031647421 / 500000000000 : ℝ) (55612658969 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b984 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e986 : ℝ := e983 + e985
lemma b986 : Encl e986 (674324963 / 200000000000 : ℝ) (3371624821 / 1000000000000 : ℝ) := by
  exact Encl.add b983 b985 (by norm_num) (by norm_num)

def e987 : ℝ := e8 * e986
lemma b987 : Encl e987 (1652096159 / 500000000000 : ℝ) (132167693 / 40000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b986 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e988 : ℝ := e980 / e982
lemma b988 : Encl e988 (12093639319 / 100000000000 : ℝ) (120936393193 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b980 b982 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e989 : ℝ := e988 - e23
lemma b989 : Encl e989 (-187906360681 / 100000000000 : ℝ) (-1879063606807 / 1000000000000 : ℝ) := by
  exact Encl.sub b988 b23 (by norm_num) (by norm_num)

def e990 : ℝ := e23 * e982
lemma b990 : Encl e990 (941358336691 / 500000000000 : ℝ) (941358336693 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b982 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e991 : ℝ := e989 + e990
lemma b991 : Encl e991 (913266643 / 250000000000 : ℝ) (3653066579 / 1000000000000 : ℝ) := by
  exact Encl.add b989 b990 (by norm_num) (by norm_num)

def e992 : ℝ := e991 / e43
lemma b992 : Encl e992 (73061331 / 1000000000000 : ℝ) (18265333 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b991 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e993 : ℝ := e987 - e992
lemma b993 : Encl e993 (1615565493 / 500000000000 : ℝ) (1615565497 / 500000000000 : ℝ) := by
  exact Encl.sub b987 b992 (by norm_num) (by norm_num)

def e994 : ℝ := e979 * e993
lemma b994 : Encl e994 (225856563 / 25000000000 : ℝ) (564641409 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b979 b993 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e995 : ℝ := e978 + e994
lemma b995 : Encl e995 (-110368384143 / 250000000000 : ℝ) (-88294707309 / 200000000000 : ℝ) := by
  exact Encl.add b978 b994 (by norm_num) (by norm_num)

def e996 : ℝ := e966 ^ 2
lemma b996 : Encl e996 (261069252853 / 500000000000 : ℝ) (522138505711 / 1000000000000 : ℝ) := by
  exact Encl.pow b966 (by norm_num) 2 (by norm_num) (by norm_num)

def e997 : ℝ := e5 - e996
lemma b997 : Encl e997 (477861494289 / 1000000000000 : ℝ) (238930747147 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b996 (by norm_num) (by norm_num)

def e998 : ℝ := Real.sqrt e997
lemma b998 : Encl e998 (138255053331 / 200000000000 : ℝ) (691275266659 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b997 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e999 : ℝ := e5 + e998
lemma b999 : Encl e999 (338255053331 / 200000000000 : ℝ) (1691275266659 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b998 (by norm_num) (by norm_num)

def e1000 : ℝ := e966 / e999
lemma b1000 : Encl e1000 (1668931831 / 3906250000 : ℝ) (21362327437 / 50000000000 : ℝ) := by
  exact Encl.div_nonneg b966 b999 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1001 : ℝ := e1000 ^ 2
lemma b1001 : Encl e1001 (91269806703 / 500000000000 : ℝ) (182539613411 / 1000000000000 : ℝ) := by
  exact Encl.pow b1000 (by norm_num) 2 (by norm_num) (by norm_num)

def e1002 : ℝ := e5 + e1001
lemma b1002 : Encl e1002 (591269806703 / 500000000000 : ℝ) (1182539613411 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1001 (by norm_num) (by norm_num)

def e1003 : ℝ := Real.sqrt e1002
lemma b1003 : Encl e1003 (1087446372657 / 1000000000000 : ℝ) (54372318633 / 50000000000 : ℝ) := by
  exact Encl.sqrt b1002 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1004 : ℝ := e5 + e1003
lemma b1004 : Encl e1004 (2087446372657 / 1000000000000 : ℝ) (104372318633 / 50000000000 : ℝ) := by
  exact Encl.add b5 b1003 (by norm_num) (by norm_num)

def e1005 : ℝ := e1000 / e1004
lemma b1005 : Encl e1005 (204674263411 / 1000000000000 : ℝ) (40934852683 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b1000 b1004 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1006 : ℝ := Real.arcsin e966
lemma b1006 : Encl e1006 (807543909073 / 1000000000000 : ℝ) (807543909089 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e966) (a := (204674263411 / 1000000000000 : ℝ)) (b := (40934852683 / 200000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (180647880161 / 250000000000 : ℝ) by norm_num).trans b966.1
        exact b966.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e966) (204674263411 / 1000000000000 : ℝ) (40934852683 / 200000000000 : ℝ) from b1005) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e1007 : ℝ := e59 * e1006
lemma b1007 : Encl e1007 (411847393627 / 1000000000000 : ℝ) (102961848409 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1006 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1008 : ℝ := e61 * e966
lemma b1008 : Encl e1008 (70813969023 / 200000000000 : ℝ) (177034922559 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b966 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1009 : ℝ := e1008 * e998
lemma b1009 : Encl e1009 (61189931649 / 250000000000 : ℝ) (1223798633 / 5000000000 : ℝ) := by
  exact Encl.mul_nonneg b1008 b998 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1010 : ℝ := e1007 - e1009
lemma b1010 : Encl e1010 (167087667027 / 1000000000000 : ℝ) (1044297919 / 6250000000 : ℝ) := by
  exact Encl.sub b1007 b1009 (by norm_num) (by norm_num)

def e1011 : ℝ := e43 * e998
lemma b1011 : Encl e1011 (138255053331 / 4000000000 : ℝ) (691275266659 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b998 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1012 : ℝ := e966 / e1011
lemma b1012 : Encl e1012 (10453021473 / 500000000000 : ℝ) (5226510737 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b966 b1011 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1013 : ℝ := e1010 - e1012
lemma b1013 : Encl e1013 (146181624079 / 1000000000000 : ℝ) (73090812047 / 500000000000 : ℝ) := by
  exact Encl.sub b1010 b1012 (by norm_num) (by norm_num)

def e1014 : ℝ := e5 + e982
lemma b1014 : Encl e1014 (1941358336691 / 1000000000000 : ℝ) (1941358336693 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b982 (by norm_num) (by norm_num)

def e1015 : ℝ := e965 / e1014
lemma b1015 : Encl e1015 (86900103133 / 500000000000 : ℝ) (173800206267 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b965 b1014 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1016 : ℝ := e1015 ^ 2
lemma b1016 : Encl e1016 (15103255849 / 500000000000 : ℝ) (30206511699 / 1000000000000 : ℝ) := by
  exact Encl.pow b1015 (by norm_num) 2 (by norm_num) (by norm_num)

def e1017 : ℝ := e5 + e1016
lemma b1017 : Encl e1017 (515103255849 / 500000000000 : ℝ) (1030206511699 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1016 (by norm_num) (by norm_num)

def e1018 : ℝ := Real.sqrt e1017
lemma b1018 : Encl e1018 (1014990892421 / 1000000000000 : ℝ) (507495446211 / 500000000000 : ℝ) := by
  exact Encl.sqrt b1017 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1019 : ℝ := e5 + e1018
lemma b1019 : Encl e1019 (2014990892421 / 1000000000000 : ℝ) (1007495446211 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1018 (by norm_num) (by norm_num)

def e1020 : ℝ := e1015 / e1019
lemma b1020 : Encl e1020 (43126796979 / 500000000000 : ℝ) (2156339849 / 25000000000 : ℝ) := by
  exact Encl.div_nonneg b1015 b1019 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1021 : ℝ := Real.arcsin e965
lemma b1021 : Encl e1021 (344162575749 / 1000000000000 : ℝ) (172081287879 / 500000000000 : ℝ) := by
  apply Encl.arcsin (z := e965) (a := (43126796979 / 500000000000 : ℝ)) (b := (2156339849 / 25000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (168704239677 / 500000000000 : ℝ) by norm_num).trans b965.1
        exact b965.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e965) (43126796979 / 500000000000 : ℝ) (2156339849 / 25000000000 : ℝ) from b1020) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e1022 : ℝ := e59 * e1021
lemma b1022 : Encl e1022 (175522913631 / 1000000000000 : ℝ) (175522913637 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1021 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1023 : ℝ := e61 * e965
lemma b1023 : Encl e1023 (165330154883 / 1000000000000 : ℝ) (41332538721 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b965 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1024 : ℝ := e1023 * e982
lemma b1024 : Encl e1024 (31126983921 / 200000000000 : ℝ) (155634919607 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1023 b982 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1025 : ℝ := e1022 - e1024
lemma b1025 : Encl e1025 (2485999253 / 125000000000 : ℝ) (1242999627 / 62500000000 : ℝ) := by
  exact Encl.sub b1022 b1024 (by norm_num) (by norm_num)

def e1026 : ℝ := e43 * e982
lemma b1026 : Encl e1026 (941358336691 / 20000000000 : ℝ) (941358336693 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b982 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1027 : ℝ := e965 / e1026
lemma b1027 : Encl e1027 (1792136247 / 250000000000 : ℝ) (7168544989 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b965 b1026 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1028 : ℝ := e1025 - e1027
lemma b1028 : Encl e1028 (2543889807 / 200000000000 : ℝ) (3179862261 / 250000000000 : ℝ) := by
  exact Encl.sub b1025 b1027 (by norm_num) (by norm_num)

def e1029 : ℝ := e1013 - e1028
lemma b1029 : Encl e1029 (26692435007 / 200000000000 : ℝ) (133462175059 / 1000000000000 : ℝ) := by
  exact Encl.sub b1013 b1028 (by norm_num) (by norm_num)

def e1030 : ℝ := e1029 / e964
lemma b1030 : Encl e1030 (125907712297 / 1000000000000 : ℝ) (393461601 / 3125000000 : ℝ) := by
  exact Encl.div_nonneg b1029 b964 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1031 : ℝ := e995 + e1030
lemma b1031 : Encl e1031 (-12622632971 / 40000000000 : ℝ) (-12622632969 / 40000000000 : ℝ) := by
  exact Encl.add b995 b1030 (by norm_num) (by norm_num)

def e1032 : ℝ := e966 + e4
lemma b1032 : Encl e1032 (856167419627 / 500000000000 : ℝ) (856167419629 / 500000000000 : ℝ) := by
  exact Encl.add b966 b4 (by norm_num) (by norm_num)

def e1033 : ℝ := e1032 / e23
lemma b1033 : Encl e1033 (856167419627 / 1000000000000 : ℝ) (856167419629 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1032 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1034 : ℝ := e966 / e964
lemma b1034 : Encl e1034 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b966 b964 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1035 : ℝ := e89 * e1034
lemma b1035 : Encl e1035 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1034 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1036 : ℝ := e1034 ^ 2
lemma b1036 : Encl e1036 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b1034 (by norm_num) 2 (by norm_num) (by norm_num)

def e1037 : ℝ := e91 * e1036
lemma b1037 : Encl e1037 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1036 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1038 : ℝ := e5 + e1037
lemma b1038 : Encl e1038 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1037 (by norm_num) (by norm_num)

def e1039 : ℝ := Real.sqrt e1038
lemma b1039 : Encl e1039 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1038 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1040 : ℝ := e1035 * e1039
lemma b1040 : Encl e1040 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1035 b1039 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1041 : ℝ := e97 * e1036
lemma b1041 : Encl e1041 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1036 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1042 : ℝ := e1040 - e1041
lemma b1042 : Encl e1042 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b1040 b1041 (by norm_num) (by norm_num)

def e1043 : ℝ := e1033 * e1042
lemma b1043 : Encl e1043 (583640865721 / 1000000000000 : ℝ) (583640865743 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1033 b1042 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1044 : ℝ := e1033 / e964
lemma b1044 : Encl e1044 (161541022571 / 200000000000 : ℝ) (403852556429 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1033 b964 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1045 : ℝ := e89 * e1044
lemma b1045 : Encl e1045 (57264801507 / 40000000000 : ℝ) (715810018841 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1044 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1046 : ℝ := e1044 ^ 2
lemma b1046 : Encl e1046 (163096887333 / 250000000000 : ℝ) (652387549337 / 1000000000000 : ℝ) := by
  exact Encl.pow b1044 (by norm_num) 2 (by norm_num) (by norm_num)

def e1047 : ℝ := e91 * e1046
lemma b1047 : Encl e1047 (128095995767 / 250000000000 : ℝ) (256191991537 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1046 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1048 : ℝ := e5 + e1047
lemma b1048 : Encl e1048 (378095995767 / 250000000000 : ℝ) (756191991537 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1047 (by norm_num) (by norm_num)

def e1049 : ℝ := Real.sqrt e1048
lemma b1049 : Encl e1049 (122979021913 / 100000000000 : ℝ) (1229790219133 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1048 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1050 : ℝ := e1045 * e1049
lemma b1050 : Encl e1050 (1760592319843 / 1000000000000 : ℝ) (1760592319857 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1045 b1049 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1051 : ℝ := e97 * e1046
lemma b1051 : Encl e1051 (128095995767 / 125000000000 : ℝ) (512383983073 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1046 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1052 : ℝ := e1050 - e1051
lemma b1052 : Encl e1052 (735824353697 / 1000000000000 : ℝ) (735824353721 / 1000000000000 : ℝ) := by
  exact Encl.sub b1050 b1051 (by norm_num) (by norm_num)

def e1053 : ℝ := e966 * e1052
lemma b1053 : Encl e1053 (66462554833 / 125000000000 : ℝ) (106340087737 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b966 b1052 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1054 : ℝ := e1043 - e1053
lemma b1054 : Encl e1054 (12985106759 / 250000000000 : ℝ) (51940427079 / 1000000000000 : ℝ) := by
  exact Encl.sub b1043 b1053 (by norm_num) (by norm_num)

def e1055 : ℝ := e1033 ^ 2
lemma b1055 : Encl e1055 (73302265043 / 100000000000 : ℝ) (146604530087 / 200000000000 : ℝ) := by
  exact Encl.pow b1033 (by norm_num) 2 (by norm_num) (by norm_num)

def e1056 : ℝ := e8 * e1055
lemma b1056 : Encl e1056 (718362197421 / 1000000000000 : ℝ) (718362197427 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1055 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1057 : ℝ := e5 - e1056
lemma b1057 : Encl e1057 (281637802573 / 1000000000000 : ℝ) (281637802579 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1056 (by norm_num) (by norm_num)

def e1058 : ℝ := e5 - e1055
lemma b1058 : Encl e1058 (53395469913 / 200000000000 : ℝ) (26697734957 / 100000000000 : ℝ) := by
  exact Encl.sub b5 b1055 (by norm_num) (by norm_num)

def e1059 : ℝ := Real.sqrt e1058
lemma b1059 : Encl e1059 (10333970187 / 20000000000 : ℝ) (129174627339 / 250000000000 : ℝ) := by
  exact Encl.sqrt b1058 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1060 : ℝ := e1057 / e1059
lemma b1060 : Encl e1060 (272535915503 / 500000000000 : ℝ) (21802873241 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b1057 b1059 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1061 : ℝ := e5 - e1060
lemma b1061 : Encl e1061 (18197126759 / 40000000000 : ℝ) (227464084497 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b1060 (by norm_num) (by norm_num)

def e1062 : ℝ := e8 * e996
lemma b1062 : Encl e1062 (511695735591 / 1000000000000 : ℝ) (511695735597 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b996 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1063 : ℝ := e5 - e1062
lemma b1063 : Encl e1063 (488304264403 / 1000000000000 : ℝ) (488304264409 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1062 (by norm_num) (by norm_num)

def e1064 : ℝ := e1063 / e998
lemma b1064 : Encl e1064 (353190898007 / 500000000000 : ℝ) (176595449007 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b1063 b998 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1065 : ℝ := e5 - e1064
lemma b1065 : Encl e1065 (73404550993 / 250000000000 : ℝ) (146809101993 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b1064 (by norm_num) (by norm_num)

def e1066 : ℝ := e1061 - e1065
lemma b1066 : Encl e1066 (161309964989 / 1000000000000 : ℝ) (80654982511 / 500000000000 : ℝ) := by
  exact Encl.sub b1061 b1065 (by norm_num) (by norm_num)

def e1067 : ℝ := e1054 * e1066
lemma b1067 : Encl e1067 (4189254233 / 500000000000 : ℝ) (2094627119 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b1054 b1066 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1068 : ℝ := e1052 - e1042
lemma b1068 : Encl e1068 (54134239869 / 1000000000000 : ℝ) (13533559979 / 250000000000 : ℝ) := by
  exact Encl.sub b1052 b1042 (by norm_num) (by norm_num)

def e1069 : ℝ := e5 + e1059
lemma b1069 : Encl e1069 (30333970187 / 20000000000 : ℝ) (379174627339 / 250000000000 : ℝ) := by
  exact Encl.add b5 b1059 (by norm_num) (by norm_num)

def e1070 : ℝ := e1033 / e1069
lemma b1070 : Encl e1070 (282247069653 / 500000000000 : ℝ) (564494139311 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1033 b1069 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1071 : ℝ := e1070 ^ 2
lemma b1071 : Encl e1071 (31865363331 / 100000000000 : ℝ) (318653633317 / 1000000000000 : ℝ) := by
  exact Encl.pow b1070 (by norm_num) 2 (by norm_num) (by norm_num)

def e1072 : ℝ := e5 + e1071
lemma b1072 : Encl e1072 (131865363331 / 100000000000 : ℝ) (1318653633317 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1071 (by norm_num) (by norm_num)

def e1073 : ℝ := Real.sqrt e1072
lemma b1073 : Encl e1073 (1148326448929 / 1000000000000 : ℝ) (1148326448933 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1072 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1074 : ℝ := e5 + e1073
lemma b1074 : Encl e1074 (2148326448929 / 1000000000000 : ℝ) (2148326448933 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1073 (by norm_num) (by norm_num)

def e1075 : ℝ := e1070 / e1074
lemma b1075 : Encl e1075 (3284499311 / 12500000000 : ℝ) (262759944883 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1070 b1074 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1076 : ℝ := Real.arcsin e1033
lemma b1076 : Encl e1076 (256951502631 / 250000000000 : ℝ) (128475751317 / 125000000000 : ℝ) := by
  apply Encl.arcsin (z := e1033) (a := (3284499311 / 12500000000 : ℝ)) (b := (262759944883 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (856167419627 / 1000000000000 : ℝ) by norm_num).trans b1033.1
        exact b1033.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1033) (3284499311 / 12500000000 : ℝ) (262759944883 / 1000000000000 : ℝ) from b1075) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e1077 : ℝ := e59 * e1076
lemma b1077 : Encl e1077 (524181065367 / 1000000000000 : ℝ) (262090532687 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1076 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1078 : ℝ := e61 * e1033
lemma b1078 : Encl e1078 (419522035617 / 1000000000000 : ℝ) (419522035619 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1033 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1079 : ℝ := e1078 * e1059
lemma b1079 : Encl e1079 (108383205221 / 500000000000 : ℝ) (216766410447 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1078 b1059 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1080 : ℝ := e1077 - e1079
lemma b1080 : Encl e1080 (7685366373 / 25000000000 : ℝ) (76853663733 / 250000000000 : ℝ) := by
  exact Encl.sub b1077 b1079 (by norm_num) (by norm_num)

def e1081 : ℝ := e43 * e1059
lemma b1081 : Encl e1081 (10333970187 / 400000000 : ℝ) (129174627339 / 5000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1059 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1082 : ℝ := e1033 / e1081
lemma b1082 : Encl e1082 (33139922183 / 1000000000000 : ℝ) (6627984437 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b1033 b1081 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1083 : ℝ := e1080 - e1082
lemma b1083 : Encl e1083 (54854946547 / 200000000000 : ℝ) (274274732749 / 1000000000000 : ℝ) := by
  exact Encl.sub b1080 b1082 (by norm_num) (by norm_num)

def e1084 : ℝ := e1083 - e1013
lemma b1084 : Encl e1084 (128093108641 / 1000000000000 : ℝ) (12809310867 / 100000000000 : ℝ) := by
  exact Encl.sub b1083 b1013 (by norm_num) (by norm_num)

def e1085 : ℝ := e1068 * e1084
lemma b1085 : Encl e1085 (1733555767 / 250000000000 : ℝ) (6934223077 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1068 b1084 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1086 : ℝ := e1067 + e1085
lemma b1086 : Encl e1086 (7656365767 / 500000000000 : ℝ) (15312731553 / 1000000000000 : ℝ) := by
  exact Encl.add b1067 b1085 (by norm_num) (by norm_num)

def e1087 : ℝ := e1033 - e966
lemma b1087 : Encl e1087 (6678794949 / 50000000000 : ℝ) (26715179797 / 200000000000 : ℝ) := by
  exact Encl.sub b1033 b966 (by norm_num) (by norm_num)

def e1088 : ℝ := e1086 / e1087
lemma b1088 : Encl e1088 (22927386827 / 200000000000 : ℝ) (57318467141 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1086 b1087 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1089 : ℝ := e1031 + e1088
lemma b1089 : Encl e1089 (-10046444507 / 50000000000 : ℝ) (-200928889943 / 1000000000000 : ℝ) := by
  exact Encl.add b1031 b1088 (by norm_num) (by norm_num)

def e1090 : ℝ := e4 * e1052
lemma b1090 : Encl e1090 (364138618871 / 500000000000 : ℝ) (728277237767 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b1052 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1091 : ℝ := e4 / e964
lemma b1091 : Encl e1091 (116715013987 / 125000000000 : ℝ) (466860055949 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b964 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1092 : ℝ := e89 * e1091
lemma b1092 : Encl e1092 (1654975807997 / 1000000000000 : ℝ) (827487904001 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1091 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1093 : ℝ := e1091 ^ 2
lemma b1093 : Encl e1093 (871833247359 / 1000000000000 : ℝ) (871833247363 / 1000000000000 : ℝ) := by
  exact Encl.pow b1091 (by norm_num) 2 (by norm_num) (by norm_num)

def e1094 : ℝ := e91 * e1093
lemma b1094 : Encl e1094 (21398007227 / 31250000000 : ℝ) (684736231269 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1093 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1095 : ℝ := e5 + e1094
lemma b1095 : Encl e1095 (52648007227 / 31250000000 : ℝ) (1684736231269 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1094 (by norm_num) (by norm_num)

def e1096 : ℝ := Real.sqrt e1095
lemma b1096 : Encl e1096 (1297973894677 / 1000000000000 : ℝ) (32449347367 / 25000000000 : ℝ) := by
  exact Encl.sqrt b1095 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1097 : ℝ := e1092 * e1096
lemma b1097 : Encl e1097 (1074057697551 / 500000000000 : ℝ) (1074057697557 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1092 b1096 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1098 : ℝ := e97 * e1093
lemma b1098 : Encl e1098 (21398007227 / 15625000000 : ℝ) (171184057817 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1093 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1099 : ℝ := e1097 - e1098
lemma b1099 : Encl e1099 (389321466283 / 500000000000 : ℝ) (389321466293 / 500000000000 : ℝ) := by
  exact Encl.sub b1097 b1098 (by norm_num) (by norm_num)

def e1100 : ℝ := e1033 * e1099
lemma b1100 : Encl e1100 (133329742077 / 200000000000 : ℝ) (133329742081 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b1033 b1099 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1101 : ℝ := e1090 - e1100
lemma b1101 : Encl e1101 (61628527337 / 1000000000000 : ℝ) (30814263691 / 500000000000 : ℝ) := by
  exact Encl.sub b1090 b1100 (by norm_num) (by norm_num)

def e1102 : ℝ := e165 - e1061
lemma b1102 : Encl e1102 (265071830981 / 1000000000000 : ℝ) (265071831053 / 1000000000000 : ℝ) := by
  exact Encl.sub b165 b1061 (by norm_num) (by norm_num)

def e1103 : ℝ := e1101 * e1102
lemma b1103 : Encl e1103 (16335986581 / 1000000000000 : ℝ) (16335986599 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1101 b1102 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1104 : ℝ := e1099 - e1052
lemma b1104 : Encl e1104 (8563715769 / 200000000000 : ℝ) (42818578889 / 1000000000000 : ℝ) := by
  exact Encl.sub b1099 b1052 (by norm_num) (by norm_num)

def e1105 : ℝ := e183 - e1083
lemma b1105 : Encl e1105 (245878036763 / 1000000000000 : ℝ) (61469509227 / 250000000000 : ℝ) := by
  exact Encl.sub b183 b1083 (by norm_num) (by norm_num)

def e1106 : ℝ := e1104 * e1105
lemma b1106 : Encl e1106 (10528148103 / 1000000000000 : ℝ) (10528148121 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1104 b1105 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1107 : ℝ := e1103 + e1106
lemma b1107 : Encl e1107 (6716033671 / 250000000000 : ℝ) (83950421 / 3125000000 : ℝ) := by
  exact Encl.add b1103 b1106 (by norm_num) (by norm_num)

def e1108 : ℝ := e4 - e1033
lemma b1108 : Encl e1108 (133575898981 / 1000000000000 : ℝ) (16696987373 / 125000000000 : ℝ) := by
  exact Encl.sub b4 b1033 (by norm_num) (by norm_num)

def e1109 : ℝ := e1107 / e1108
lemma b1109 : Encl e1109 (50278783239 / 250000000000 : ℝ) (201115133231 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1107 b1108 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1110 : ℝ := e1089 + e1109
lemma b1110 : Encl e1110 (727511 / 3906250000 : ℝ) (23280411 / 125000000000 : ℝ) := by
  exact Encl.add b1089 b1109 (by norm_num) (by norm_num)

def e1111 : ℝ := e924 / e964
lemma b1111 : Encl e1111 (452830188679 / 500000000000 : ℝ) (905660377359 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b924 b964 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1112 : ℝ := min e7 e1111
lemma b1112 : Encl e1112 (85211264227 / 125000000000 : ℝ) (681690113817 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b1111 (by norm_num) (by norm_num)

def e1113 : ℝ := e1112 - e5
lemma b1113 : Encl e1113 (-39788735773 / 125000000000 : ℝ) (-318309886183 / 1000000000000 : ℝ) := by
  exact Encl.sub b1112 b5 (by norm_num) (by norm_num)

def e1114 : ℝ := e23 * e964
lemma b1114 : Encl e1114 (53 / 25 : ℝ) (53 / 25 : ℝ) := by
  exact Encl.mul_nonneg b23 b964 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1115 : ℝ := e1114 * e975
lemma b1115 : Encl e1115 (1656870032931 / 1000000000000 : ℝ) (828435016467 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1114 b975 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1116 : ℝ := e1115 / e0
lemma b1116 : Encl e1116 (527398111603 / 1000000000000 : ℝ) (105479622321 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b1115 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1117 : ℝ := e1113 + e1116
lemma b1117 : Encl e1117 (209088225419 / 1000000000000 : ℝ) (104544112711 / 500000000000 : ℝ) := by
  exact Encl.add b1113 b1116 (by norm_num) (by norm_num)

def e1118 : ℝ := e23 * e969
lemma b1118 : Encl e1118 (2809 / 1250 : ℝ) (2809 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b23 b969 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1119 : ℝ := e1118 * e975
lemma b1119 : Encl e1119 (1756282234907 / 1000000000000 : ℝ) (175628223491 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b1118 b975 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1120 : ℝ := e0 + e1119
lemma b1120 : Encl e1120 (306117180531 / 62500000000 : ℝ) (9795749777 / 2000000000 : ℝ) := by
  exact Encl.add b0 b1119 (by norm_num) (by norm_num)

def e1121 : ℝ := Real.sqrt e1120
lemma b1121 : Encl e1121 (2213114296301 / 1000000000000 : ℝ) (2213114296303 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1120 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1122 : ℝ := e932 * e1121
lemma b1122 : Encl e1122 (1408912319533 / 1000000000000 : ℝ) (1408912319537 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b1121 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1123 : ℝ := e964 ^ 3
lemma b1123 : Encl e1123 (148877 / 125000 : ℝ) (148877 / 125000 : ℝ) := by
  exact Encl.pow b964 (by norm_num) 3 (by norm_num) (by norm_num)

def e1124 : ℝ := e939 * e1123
lemma b1124 : Encl e1124 (9974759 / 62500000 : ℝ) (9974759 / 62500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b1123 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1125 : ℝ := min e1124 e941
lemma b1125 : Encl e1125 (9974759 / 62500000 : ℝ) (9974759 / 62500000 : ℝ) := by
  exact Encl.min b1124 b941 (by norm_num) (by norm_num)

def e1126 : ℝ := e23 * e1117
lemma b1126 : Encl e1126 (209088225419 / 500000000000 : ℝ) (104544112711 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b1117 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1127 : ℝ := e944 * e1125
lemma b1127 : Encl e1127 (29924277 / 31250000 : ℝ) (29924277 / 31250000 : ℝ) := by
  exact Encl.mul_nonneg b944 b1125 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1128 : ℝ := e1122 ^ 2
lemma b1128 : Encl e1128 (1985033924131 / 1000000000000 : ℝ) (124064620259 / 62500000000 : ℝ) := by
  exact Encl.pow b1122 (by norm_num) 2 (by norm_num) (by norm_num)

def e1129 : ℝ := e1127 * e1128
lemma b1129 : Encl e1129 (950411280001 / 500000000000 : ℝ) (118801410001 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b1127 b1128 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1130 : ℝ := e1129 * e1117
lemma b1130 : Encl e1130 (397439615907 / 1000000000000 : ℝ) (99359903979 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b1129 b1117 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1131 : ℝ := e1130 / e9
lemma b1131 : Encl e1131 (1419427199667 / 1000000000000 : ℝ) (14194271997 / 10000000000 : ℝ) := by
  exact Encl.div_nonneg b1130 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1132 : ℝ := e5 + e1131
lemma b1132 : Encl e1132 (2419427199667 / 1000000000000 : ℝ) (24194271997 / 10000000000 : ℝ) := by
  exact Encl.add b5 b1131 (by norm_num) (by norm_num)

def e1133 : ℝ := Real.sqrt e1132
lemma b1133 : Encl e1133 (311090160543 / 200000000000 : ℝ) (777725401363 / 500000000000 : ℝ) := by
  exact Encl.sqrt b1132 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1134 : ℝ := e5 + e1133
lemma b1134 : Encl e1134 (511090160543 / 200000000000 : ℝ) (1277725401363 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1133 (by norm_num) (by norm_num)

def e1135 : ℝ := e1126 / e1134
lemma b1135 : Encl e1135 (163640971053 / 1000000000000 : ℝ) (163640971057 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1126 b1134 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1136 : ℝ := e1125 * e954
lemma b1136 : Encl e1136 (1478019889 / 1000000000000 : ℝ) (147801989 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b1125 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1137 : ℝ := e1117 - e1135
lemma b1137 : Encl e1137 (22723627181 / 500000000000 : ℝ) (45447254369 / 1000000000000 : ℝ) := by
  exact Encl.sub b1117 b1135 (by norm_num) (by norm_num)

def e1138 : ℝ := e1137 / e1122
lemma b1138 : Encl e1138 (32256978473 / 1000000000000 : ℝ) (32256978479 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1137 b1122 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1139 : ℝ := e1138 ^ 2
lemma b1139 : Encl e1139 (52025633 / 50000000000 : ℝ) (1040512661 / 1000000000000 : ℝ) := by
  exact Encl.pow b1138 (by norm_num) 2 (by norm_num) (by norm_num)

def e1140 : ℝ := e9 * e1139
lemma b1140 : Encl e1140 (36417943 / 125000000000 : ℝ) (145671773 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b1139 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1141 : ℝ := e1135 ^ 3
lemma b1141 : Encl e1141 (876407609 / 200000000000 : ℝ) (4382038047 / 1000000000000 : ℝ) := by
  exact Encl.pow b1135 (by norm_num) 3 (by norm_num) (by norm_num)

def e1142 : ℝ := e1125 * e1141
lemma b1142 : Encl e1142 (349678187 / 500000000000 : ℝ) (87419547 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b1125 b1141 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1143 : ℝ := e1140 + e1142
lemma b1143 : Encl e1143 (495349959 / 500000000000 : ℝ) (495349961 / 500000000000 : ℝ) := by
  exact Encl.add b1140 b1142 (by norm_num) (by norm_num)

def e1144 : ℝ := min e1136 e1143
lemma b1144 : Encl e1144 (495349959 / 500000000000 : ℝ) (495349961 / 500000000000 : ℝ) := by
  exact Encl.min b1136 b1143 (by norm_num) (by norm_num)

def e1145 : ℝ := (11 / 10 : ℝ)
lemma b1145 : Encl e1145 (11 / 10 : ℝ) (11 / 10 : ℝ) := by
  exact Encl.exact (11 / 10 : ℝ)

def e1146 : ℝ := e1145 / e0
lemma b1146 : Encl e1146 (175070437401 / 500000000000 : ℝ) (350140874803 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1145 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1147 : ℝ := e1145 * e7
lemma b1147 : Encl e1147 (749859125197 / 1000000000000 : ℝ) (749859125199 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1145 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1148 : ℝ := e8 * e1145
lemma b1148 : Encl e1148 (539 / 500 : ℝ) (539 / 500 : ℝ) := by
  exact Encl.mul_nonneg b8 b1145 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1149 : ℝ := e1148 / e0
lemma b1149 : Encl e1149 (171569028653 / 500000000000 : ℝ) (343138057307 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1148 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1150 : ℝ := e1145 ^ 2
lemma b1150 : Encl e1150 (121 / 100 : ℝ) (121 / 100 : ℝ) := by
  exact Encl.pow b1145 (by norm_num) 2 (by norm_num) (by norm_num)

def e1151 : ℝ := e17 * e1150
lemma b1151 : Encl e1151 (121 / 25 : ℝ) (121 / 25 : ℝ) := by
  exact Encl.mul_nonneg b17 b1150 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1152 : ℝ := e1151 / e0
lemma b1152 : Encl e1152 (1540619849129 / 1000000000000 : ℝ) (154061984913 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b1151 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1153 : ℝ := e5 + e1152
lemma b1153 : Encl e1153 (2540619849129 / 1000000000000 : ℝ) (254061984913 / 100000000000 : ℝ) := by
  exact Encl.add b5 b1152 (by norm_num) (by norm_num)

def e1154 : ℝ := Real.sqrt e1153
lemma b1154 : Encl e1154 (318786439431 / 200000000000 : ℝ) (398483049289 / 250000000000 : ℝ) := by
  exact Encl.sqrt b1153 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1155 : ℝ := e5 + e1154
lemma b1155 : Encl e1155 (518786439431 / 200000000000 : ℝ) (648483049289 / 250000000000 : ℝ) := by
  exact Encl.add b5 b1154 (by norm_num) (by norm_num)

def e1156 : ℝ := e23 / e1155
lemma b1156 : Encl e1156 (12047346509 / 15625000000 : ℝ) (771030176577 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b1155 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1157 : ℝ := e9 * e1156
lemma b1157 : Encl e1157 (215888449441 / 1000000000000 : ℝ) (107944224721 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b1156 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1158 : ℝ := e1149 + e1157
lemma b1158 : Encl e1158 (559026506747 / 1000000000000 : ℝ) (559026506749 / 1000000000000 : ℝ) := by
  exact Encl.add b1149 b1157 (by norm_num) (by norm_num)

def e1159 : ℝ := e1158 - e5
lemma b1159 : Encl e1159 (-440973493253 / 1000000000000 : ℝ) (-440973493251 / 1000000000000 : ℝ) := by
  exact Encl.sub b1158 b5 (by norm_num) (by norm_num)

def e1160 : ℝ := e0 / e1150
lemma b1160 : Encl e1160 (51927151299 / 20000000000 : ℝ) (2596357564951 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b1150 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1161 : ℝ := e1146 ^ 2
lemma b1161 : Encl e1161 (122598632207 / 1000000000000 : ℝ) (7662414513 / 62500000000 : ℝ) := by
  exact Encl.pow b1146 (by norm_num) 2 (by norm_num) (by norm_num)

def e1162 : ℝ := e5 - e1161
lemma b1162 : Encl e1162 (54837585487 / 62500000000 : ℝ) (877401367793 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1161 (by norm_num) (by norm_num)

def e1163 : ℝ := Real.sqrt e1162
lemma b1163 : Encl e1163 (468348526151 / 500000000000 : ℝ) (936697052303 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1162 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1164 : ℝ := e29 - e1163
lemma b1164 : Encl e1164 (-270030385637 / 1000000000000 : ℝ) (-54006077127 / 200000000000 : ℝ) := by
  exact Encl.sub b29 b1163 (by norm_num) (by norm_num)

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
