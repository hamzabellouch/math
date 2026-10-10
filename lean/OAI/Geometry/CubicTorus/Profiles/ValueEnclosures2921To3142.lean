import Mathlib
import OAI.Geometry.CubicTorus.Profiles.ValueEnclosures2701To2920

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

def e2921 : ℝ := e23 * e2912
lemma b2921 : Encl e2921 (283937769911 / 500000000000 : ℝ) (141968884957 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2912 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2922 : ℝ := e944 * e2920
lemma b2922 : Encl e2922 (54 / 25 : ℝ) (54 / 25 : ℝ) := by
  exact Encl.mul_nonneg b944 b2920 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2923 : ℝ := e2917 ^ 2
lemma b2923 : Encl e2923 (1251535047113 / 500000000000 : ℝ) (2503070094243 / 1000000000000 : ℝ) := by
  exact Encl.pow b2917 (by norm_num) 2 (by norm_num) (by norm_num)

def e2924 : ℝ := e2922 * e2923
lemma b2924 : Encl e2924 (675828925441 / 125000000000 : ℝ) (1081326280713 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b2922 b2923 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2925 : ℝ := e2924 * e2912
lemma b2925 : Encl e2925 (191893357931 / 125000000000 : ℝ) (383786715869 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b2924 b2912 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2926 : ℝ := e2925 / e9
lemma b2926 : Encl e2926 (5482667369457 / 1000000000000 : ℝ) (2741333684779 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2925 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2927 : ℝ := e5 + e2926
lemma b2927 : Encl e2927 (6482667369457 / 1000000000000 : ℝ) (3241333684779 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2926 (by norm_num) (by norm_num)

def e2928 : ℝ := Real.sqrt e2927
lemma b2928 : Encl e2928 (2546108279209 / 1000000000000 : ℝ) (2546108279229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2927 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2929 : ℝ := e5 + e2928
lemma b2929 : Encl e2929 (3546108279209 / 1000000000000 : ℝ) (3546108279229 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2928 (by norm_num) (by norm_num)

def e2930 : ℝ := e2921 / e2929
lemma b2930 : Encl e2930 (80070248157 / 500000000000 : ℝ) (80070248159 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2921 b2929 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2931 : ℝ := e2920 * e954
lemma b2931 : Encl e2931 (83349 / 25000000 : ℝ) (83349 / 25000000 : ℝ) := by
  exact Encl.mul_nonneg b2920 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2932 : ℝ := e2912 - e2930
lemma b2932 : Encl e2932 (123797273593 / 1000000000000 : ℝ) (4835831 / 39062500 : ℝ) := by
  exact Encl.sub b2912 b2930 (by norm_num) (by norm_num)

def e2933 : ℝ := e2932 / e2917
lemma b2933 : Encl e2933 (39124119691 / 500000000000 : ℝ) (78248239387 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2932 b2917 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2934 : ℝ := e2933 ^ 2
lemma b2934 : Encl e2934 (3061393483 / 500000000000 : ℝ) (765348371 / 125000000000 : ℝ) := by
  exact Encl.pow b2933 (by norm_num) 2 (by norm_num) (by norm_num)

def e2935 : ℝ := e9 * e2934
lemma b2935 : Encl e2935 (34287607 / 20000000000 : ℝ) (26787193 / 15625000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2934 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2936 : ℝ := e2930 ^ 3
lemma b2936 : Encl e2936 (2053399797 / 500000000000 : ℝ) (821359919 / 200000000000 : ℝ) := by
  exact Encl.pow b2930 (by norm_num) 3 (by norm_num) (by norm_num)

def e2937 : ℝ := e2920 * e2936
lemma b2937 : Encl e2937 (1478447853 / 1000000000000 : ℝ) (295689571 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b2920 b2936 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2938 : ℝ := e2935 + e2937
lemma b2938 : Encl e2938 (3192828203 / 1000000000000 : ℝ) (3192828207 / 1000000000000 : ℝ) := by
  exact Encl.add b2935 b2937 (by norm_num) (by norm_num)

def e2939 : ℝ := min e2931 e2938
lemma b2939 : Encl e2939 (3192828203 / 1000000000000 : ℝ) (3192828207 / 1000000000000 : ℝ) := by
  exact Encl.min b2931 b2938 (by norm_num) (by norm_num)

def e2940 : ℝ := (77 / 50 : ℝ)
lemma b2940 : Encl e2940 (77 / 50 : ℝ) (77 / 50 : ℝ) := by
  exact Encl.exact (77 / 50 : ℝ)

def e2941 : ℝ := e2940 / e0
lemma b2941 : Encl e2941 (490197224723 / 1000000000000 : ℝ) (122549306181 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2940 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2942 : ℝ := e8 * e2940
lemma b2942 : Encl e2942 (3773 / 2500 : ℝ) (3773 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b2940 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2943 : ℝ := e2942 / e0
lemma b2943 : Encl e2943 (120098320057 / 250000000000 : ℝ) (480393280229 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2942 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2944 : ℝ := e2940 ^ 2
lemma b2944 : Encl e2944 (5929 / 2500 : ℝ) (5929 / 2500 : ℝ) := by
  exact Encl.pow b2940 (by norm_num) 2 (by norm_num) (by norm_num)

def e2945 : ℝ := e17 * e2944
lemma b2945 : Encl e2945 (5929 / 625 : ℝ) (5929 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b2944 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2946 : ℝ := e2945 / e0
lemma b2946 : Encl e2946 (3019614904293 / 1000000000000 : ℝ) (1509807452147 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2945 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2947 : ℝ := e5 + e2946
lemma b2947 : Encl e2947 (4019614904293 / 1000000000000 : ℝ) (2009807452147 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2946 (by norm_num) (by norm_num)

def e2948 : ℝ := Real.sqrt e2947
lemma b2948 : Encl e2948 (400979545827 / 200000000000 : ℝ) (125306108071 / 62500000000 : ℝ) := by
  exact Encl.sqrt b2947 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2949 : ℝ := e5 + e2948
lemma b2949 : Encl e2949 (600979545827 / 200000000000 : ℝ) (187806108071 / 62500000000 : ℝ) := by
  exact Encl.add b5 b2948 (by norm_num) (by norm_num)

def e2950 : ℝ := e23 / e2949
lemma b2950 : Encl e2950 (166395014097 / 250000000000 : ℝ) (665580056389 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b2949 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2951 : ℝ := e9 * e2950
lemma b2951 : Encl e2951 (46590603947 / 250000000000 : ℝ) (186362415789 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2950 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2952 : ℝ := e2943 + e2951
lemma b2952 : Encl e2952 (41672231001 / 62500000000 : ℝ) (333377848009 / 500000000000 : ℝ) := by
  exact Encl.add b2943 b2951 (by norm_num) (by norm_num)

def e2953 : ℝ := e2952 - e5
lemma b2953 : Encl e2953 (-20827768999 / 62500000000 : ℝ) (-166622151991 / 500000000000 : ℝ) := by
  exact Encl.sub b2952 b5 (by norm_num) (by norm_num)

def e2954 : ℝ := e0 / e2944
lemma b2954 : Encl e2954 (264934445403 / 200000000000 : ℝ) (165584028377 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b2944 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2955 : ℝ := e2941 ^ 2
lemma b2955 : Encl e2955 (120146659563 / 500000000000 : ℝ) (30036664891 / 125000000000 : ℝ) := by
  exact Encl.pow b2941 (by norm_num) 2 (by norm_num) (by norm_num)

def e2956 : ℝ := e5 - e2955
lemma b2956 : Encl e2956 (94963335109 / 125000000000 : ℝ) (379853340437 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b2955 (by norm_num) (by norm_num)

def e2957 : ℝ := Real.sqrt e2956
lemma b2957 : Encl e2957 (174322308483 / 200000000000 : ℝ) (871611542417 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2956 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2958 : ℝ := e29 - e2957
lemma b2958 : Encl e2958 (-204944875751 / 1000000000000 : ℝ) (-51236218937 / 250000000000 : ℝ) := by
  exact Encl.sub b29 b2957 (by norm_num) (by norm_num)

def e2959 : ℝ := e2957 ^ 3
lemma b2959 : Encl e2959 (662169111897 / 1000000000000 : ℝ) (331084555951 / 500000000000 : ℝ) := by
  exact Encl.pow b2957 (by norm_num) 3 (by norm_num) (by norm_num)

def e2960 : ℝ := e2959 / e35
lemma b2960 : Encl e2960 (220723037299 / 1000000000000 : ℝ) (220723037301 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2959 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2961 : ℝ := e2958 + e2960
lemma b2961 : Encl e2961 (3944540387 / 250000000000 : ℝ) (15778161553 / 1000000000000 : ℝ) := by
  exact Encl.add b2958 b2960 (by norm_num) (by norm_num)

def e2962 : ℝ := e8 * e2961
lemma b2962 : Encl e2962 (15462598317 / 1000000000000 : ℝ) (7731299161 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2961 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2963 : ℝ := e2955 / e2957
lemma b2963 : Encl e2963 (275688546367 / 1000000000000 : ℝ) (275688546371 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2955 b2957 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2964 : ℝ := e2963 - e23
lemma b2964 : Encl e2964 (-1724311453633 / 1000000000000 : ℝ) (-1724311453629 / 1000000000000 : ℝ) := by
  exact Encl.sub b2963 b23 (by norm_num) (by norm_num)

def e2965 : ℝ := e23 * e2957
lemma b2965 : Encl e2965 (174322308483 / 100000000000 : ℝ) (871611542417 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2957 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2966 : ℝ := e2964 + e2965
lemma b2966 : Encl e2966 (18911631197 / 1000000000000 : ℝ) (3782326241 / 200000000000 : ℝ) := by
  exact Encl.add b2964 b2965 (by norm_num) (by norm_num)

def e2967 : ℝ := e2966 / e43
lemma b2967 : Encl e2967 (378232623 / 1000000000000 : ℝ) (3025861 / 8000000000 : ℝ) := by
  exact Encl.div_nonneg b2966 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2968 : ℝ := e2962 - e2967
lemma b2968 : Encl e2968 (3771091423 / 250000000000 : ℝ) (15084365699 / 1000000000000 : ℝ) := by
  exact Encl.sub b2962 b2967 (by norm_num) (by norm_num)

def e2969 : ℝ := e2954 * e2968
lemma b2969 : Encl e2969 (9990920147 / 500000000000 : ℝ) (1248865019 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b2954 b2968 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2970 : ℝ := e2953 + e2969
lemma b2970 : Encl e2970 (-31326246369 / 100000000000 : ℝ) (-156631231839 / 500000000000 : ℝ) := by
  exact Encl.add b2953 b2969 (by norm_num) (by norm_num)

def e2971 : ℝ := e5 + e2957
lemma b2971 : Encl e2971 (374322308483 / 200000000000 : ℝ) (1871611542417 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2957 (by norm_num) (by norm_num)

def e2972 : ℝ := e2941 / e2971
lemma b2972 : Encl e2972 (130955920503 / 500000000000 : ℝ) (16369490063 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b2941 b2971 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2973 : ℝ := e2972 ^ 2
lemma b2973 : Encl e2973 (68597812459 / 1000000000000 : ℝ) (68597812461 / 1000000000000 : ℝ) := by
  exact Encl.pow b2972 (by norm_num) 2 (by norm_num) (by norm_num)

def e2974 : ℝ := e5 + e2973
lemma b2974 : Encl e2974 (1068597812459 / 1000000000000 : ℝ) (1068597812461 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2973 (by norm_num) (by norm_num)

def e2975 : ℝ := Real.sqrt e2974
lemma b2975 : Encl e2975 (206746009631 / 200000000000 : ℝ) (1033730048157 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2974 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2976 : ℝ := e5 + e2975
lemma b2976 : Encl e2976 (406746009631 / 200000000000 : ℝ) (2033730048157 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2975 (by norm_num) (by norm_num)

def e2977 : ℝ := e2972 / e2976
lemma b2977 : Encl e2977 (32195993913 / 250000000000 : ℝ) (64391987827 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2972 b2976 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2978 : ℝ := Real.arcsin e2941
lemma b2978 : Encl e2978 (256158007239 / 500000000000 : ℝ) (512316014487 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e2941) (a := (32195993913 / 250000000000 : ℝ)) (b := (64391987827 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (490197224723 / 1000000000000 : ℝ) by norm_num).trans b2941.1
        exact b2941.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2941) (32195993913 / 250000000000 : ℝ) (64391987827 / 500000000000 : ℝ) from b2977) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e2979 : ℝ := e59 * e2978
lemma b2979 : Encl e2979 (261281167383 / 1000000000000 : ℝ) (261281167389 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2978 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2980 : ℝ := e61 * e2941
lemma b2980 : Encl e2980 (120098320057 / 500000000000 : ℝ) (48039328023 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2941 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2981 : ℝ := e2980 * e2957
lemma b2981 : Encl e2981 (52339540993 / 250000000000 : ℝ) (8374326559 / 40000000000 : ℝ) := by
  exact Encl.mul_nonneg b2980 b2957 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2982 : ℝ := e2979 - e2981
lemma b2982 : Encl e2982 (3245187713 / 62500000000 : ℝ) (51923003417 / 1000000000000 : ℝ) := by
  exact Encl.sub b2979 b2981 (by norm_num) (by norm_num)

def e2983 : ℝ := e43 * e2957
lemma b2983 : Encl e2983 (174322308483 / 4000000000 : ℝ) (871611542417 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2957 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2984 : ℝ := e2941 / e2983
lemma b2984 : Encl e2984 (2812016597 / 250000000000 : ℝ) (11248066389 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2941 b2983 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2985 : ℝ := e2982 - e2984
lemma b2985 : Encl e2985 (40674937019 / 1000000000000 : ℝ) (40674937029 / 1000000000000 : ℝ) := by
  exact Encl.sub b2982 b2984 (by norm_num) (by norm_num)

def e2986 : ℝ := e183 - e2985
lemma b2986 : Encl e2986 (479477832483 / 1000000000000 : ℝ) (29967364539 / 62500000000 : ℝ) := by
  exact Encl.sub b183 b2985 (by norm_num) (by norm_num)

def e2987 : ℝ := e2986 / e2940
lemma b2987 : Encl e2987 (19459327617 / 62500000000 : ℝ) (77837310491 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2986 b2940 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2988 : ℝ := e2970 + e2987
lemma b2988 : Encl e2988 (-956610909 / 500000000000 : ℝ) (-956610857 / 500000000000 : ℝ) := by
  exact Encl.add b2970 b2987 (by norm_num) (by norm_num)

def e2989 : ℝ := e924 / e2940
lemma b2989 : Encl e2989 (38961038961 / 62500000000 : ℝ) (623376623377 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b924 b2940 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2990 : ℝ := min e7 e2989
lemma b2990 : Encl e2990 (38961038961 / 62500000000 : ℝ) (623376623377 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b2989 (by norm_num) (by norm_num)

def e2991 : ℝ := e2990 - e5
lemma b2991 : Encl e2991 (-23538961039 / 62500000000 : ℝ) (-376623376623 / 1000000000000 : ℝ) := by
  exact Encl.sub b2990 b5 (by norm_num) (by norm_num)

def e2992 : ℝ := e23 * e2940
lemma b2992 : Encl e2992 (77 / 25 : ℝ) (77 / 25 : ℝ) := by
  exact Encl.mul_nonneg b23 b2940 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2993 : ℝ := e2992 * e2950
lemma b2993 : Encl e2993 (81999462947 / 40000000000 : ℝ) (2049986573679 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2992 b2950 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2994 : ℝ := e2993 / e0
lemma b2994 : Encl e2994 (40783187059 / 62500000000 : ℝ) (652530992947 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2993 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2995 : ℝ := e2991 + e2994
lemma b2995 : Encl e2995 (862211301 / 3125000000 : ℝ) (68976904081 / 250000000000 : ℝ) := by
  exact Encl.add b2991 b2994 (by norm_num) (by norm_num)

def e2996 : ℝ := e23 * e2944
lemma b2996 : Encl e2996 (5929 / 1250 : ℝ) (5929 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b23 b2944 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2997 : ℝ := e2996 * e2950
lemma b2997 : Encl e2997 (3156979323459 / 1000000000000 : ℝ) (631395864693 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b2996 b2950 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2998 : ℝ := e0 + e2997
lemma b2998 : Encl e2998 (787321497131 / 125000000000 : ℝ) (1259714395411 / 200000000000 : ℝ) := by
  exact Encl.add b0 b2997 (by norm_num) (by norm_num)

def e2999 : ℝ := Real.sqrt e2998
lemma b2999 : Encl e2999 (2509695594499 / 1000000000000 : ℝ) (2509695594501 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2998 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3000 : ℝ := e932 * e2999
lemma b3000 : Encl e3000 (624110093 / 390625000 : ℝ) (319544367617 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b2999 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3001 : ℝ := e2940 ^ 3
lemma b3001 : Encl e3001 (456533 / 125000 : ℝ) (456533 / 125000 : ℝ) := by
  exact Encl.pow b2940 (by norm_num) 3 (by norm_num) (by norm_num)

def e3002 : ℝ := e939 * e3001
lemma b3002 : Encl e3002 (30587711 / 62500000 : ℝ) (30587711 / 62500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b3001 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3003 : ℝ := min e3002 e941
lemma b3003 : Encl e3003 (9 / 25 : ℝ) (9 / 25 : ℝ) := by
  exact Encl.min b3002 b941 (by norm_num) (by norm_num)

def e3004 : ℝ := e23 * e2995
lemma b3004 : Encl e3004 (862211301 / 1562500000 : ℝ) (68976904081 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2995 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3005 : ℝ := e944 * e3003
lemma b3005 : Encl e3005 (54 / 25 : ℝ) (54 / 25 : ℝ) := by
  exact Encl.mul_nonneg b944 b3003 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3006 : ℝ := e3000 ^ 2
lemma b3006 : Encl e3006 (2552715071877 / 1000000000000 : ℝ) (1276357535947 / 500000000000 : ℝ) := by
  exact Encl.pow b3000 (by norm_num) 2 (by norm_num) (by norm_num)

def e3007 : ℝ := e3005 * e3006
lemma b3007 : Encl e3007 (2756932277627 / 500000000000 : ℝ) (1378466138823 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b3005 b3006 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3008 : ℝ := e3007 * e2995
lemma b3008 : Encl e3008 (1521317226151 / 1000000000000 : ℝ) (304263445237 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b3007 b2995 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3009 : ℝ := e3008 / e9
lemma b3009 : Encl e3009 (2716637903841 / 500000000000 : ℝ) (1358318951951 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b3008 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3010 : ℝ := e5 + e3009
lemma b3010 : Encl e3010 (3216637903841 / 500000000000 : ℝ) (1608318951951 / 250000000000 : ℝ) := by
  exact Encl.add b5 b3009 (by norm_num) (by norm_num)

def e3011 : ℝ := Real.sqrt e3010
lemma b3011 : Encl e3011 (507278062119 / 200000000000 : ℝ) (126819515531 / 50000000000 : ℝ) := by
  exact Encl.sqrt b3010 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3012 : ℝ := e5 + e3011
lemma b3012 : Encl e3012 (707278062119 / 200000000000 : ℝ) (176819515531 / 50000000000 : ℝ) := by
  exact Encl.add b5 b3011 (by norm_num) (by norm_num)

def e3013 : ℝ := e3004 / e3012
lemma b3013 : Encl e3013 (19504890021 / 125000000000 : ℝ) (39009780043 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b3004 b3012 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3014 : ℝ := e3003 * e954
lemma b3014 : Encl e3014 (83349 / 25000000 : ℝ) (83349 / 25000000 : ℝ) := by
  exact Encl.mul_nonneg b3003 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3015 : ℝ := e2995 - e3013
lemma b3015 : Encl e3015 (29967124037 / 250000000000 : ℝ) (29967124039 / 250000000000 : ℝ) := by
  exact Encl.sub b2995 b3013 (by norm_num) (by norm_num)

def e3016 : ℝ := e3015 / e3000
lemma b3016 : Encl e3016 (75024634007 / 1000000000000 : ℝ) (75024634013 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3015 b3000 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3017 : ℝ := e3016 ^ 2
lemma b3017 : Encl e3017 (5628695707 / 1000000000000 : ℝ) (5628695709 / 1000000000000 : ℝ) := by
  exact Encl.pow b3016 (by norm_num) 2 (by norm_num) (by norm_num)

def e3018 : ℝ := e9 * e3017
lemma b3018 : Encl e3018 (1576034797 / 1000000000000 : ℝ) (1576034799 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b3017 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3019 : ℝ := e3013 ^ 3
lemma b3019 : Encl e3019 (3799272801 / 1000000000000 : ℝ) (1899636401 / 500000000000 : ℝ) := by
  exact Encl.pow b3013 (by norm_num) 3 (by norm_num) (by norm_num)

def e3020 : ℝ := e3003 * e3019
lemma b3020 : Encl e3020 (42741819 / 31250000000 : ℝ) (1367738209 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b3003 b3019 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3021 : ℝ := e3018 + e3020
lemma b3021 : Encl e3021 (588754601 / 200000000000 : ℝ) (183985813 / 62500000000 : ℝ) := by
  exact Encl.add b3018 b3020 (by norm_num) (by norm_num)

def e3022 : ℝ := min e3014 e3021
lemma b3022 : Encl e3022 (588754601 / 200000000000 : ℝ) (183985813 / 62500000000 : ℝ) := by
  exact Encl.min b3014 b3021 (by norm_num) (by norm_num)

def e3023 : ℝ := (79 / 50 : ℝ)
lemma b3023 : Encl e3023 (79 / 50 : ℝ) (79 / 50 : ℝ) := by
  exact Encl.exact (79 / 50 : ℝ)

def e3024 : ℝ := e3023 / e0
lemma b3024 : Encl e3024 (50292962017 / 100000000000 : ℝ) (502929620171 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3023 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3025 : ℝ := e8 * e3023
lemma b3025 : Encl e3025 (3871 / 2500 : ℝ) (3871 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b3023 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3026 : ℝ := e3025 / e0
lemma b3026 : Encl e3026 (246435513883 / 500000000000 : ℝ) (492871027767 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3025 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3027 : ℝ := e3023 ^ 2
lemma b3027 : Encl e3027 (6241 / 2500 : ℝ) (6241 / 2500 : ℝ) := by
  exact Encl.pow b3023 (by norm_num) 2 (by norm_num) (by norm_num)

def e3028 : ℝ := e17 * e3027
lemma b3028 : Encl e3028 (6241 / 625 : ℝ) (6241 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b3027 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3029 : ℝ := e3028 / e0
lemma b3029 : Encl e3029 (794628799869 / 250000000000 : ℝ) (3178515199477 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3028 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3030 : ℝ := e5 + e3029
lemma b3030 : Encl e3030 (1044628799869 / 250000000000 : ℝ) (4178515199477 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3029 (by norm_num) (by norm_num)

def e3031 : ℝ := Real.sqrt e3030
lemma b3031 : Encl e3031 (127758854871 / 62500000000 : ℝ) (2044141677937 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b3030 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3032 : ℝ := e5 + e3031
lemma b3032 : Encl e3032 (190258854871 / 62500000000 : ℝ) (3044141677937 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3031 (by norm_num) (by norm_num)

def e3033 : ℝ := e23 / e3032
lemma b3033 : Encl e3033 (65699964443 / 100000000000 : ℝ) (656999644431 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b3032 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3034 : ℝ := e9 * e3033
lemma b3034 : Encl e3034 (4598997511 / 25000000000 : ℝ) (183959900441 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b3033 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3035 : ℝ := e3026 + e3034
lemma b3035 : Encl e3035 (338415464103 / 500000000000 : ℝ) (42301933013 / 62500000000 : ℝ) := by
  exact Encl.add b3026 b3034 (by norm_num) (by norm_num)

def e3036 : ℝ := e3035 - e5
lemma b3036 : Encl e3036 (-161584535897 / 500000000000 : ℝ) (-20198066987 / 62500000000 : ℝ) := by
  exact Encl.sub b3035 b5 (by norm_num) (by norm_num)

def e3037 : ℝ := e0 / e3027
lemma b3037 : Encl e3037 (314612307081 / 250000000000 : ℝ) (50337969133 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b3027 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3038 : ℝ := e3024 ^ 2
lemma b3038 : Encl e3038 (63234550711 / 250000000000 : ℝ) (126469101423 / 500000000000 : ℝ) := by
  exact Encl.pow b3024 (by norm_num) 2 (by norm_num) (by norm_num)

def e3039 : ℝ := e5 - e3038
lemma b3039 : Encl e3039 (373530898577 / 500000000000 : ℝ) (186765449289 / 250000000000 : ℝ) := by
  exact Encl.sub b5 b3038 (by norm_num) (by norm_num)

def e3040 : ℝ := Real.sqrt e3039
lemma b3040 : Encl e3040 (864327366889 / 1000000000000 : ℝ) (864327366891 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b3039 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3041 : ℝ := e29 - e3040
lemma b3041 : Encl e3041 (-7906428009 / 40000000000 : ℝ) (-98830350111 / 500000000000 : ℝ) := by
  exact Encl.sub b29 b3040 (by norm_num) (by norm_num)

def e3042 : ℝ := e3040 ^ 3
lemma b3042 : Encl e3042 (161426489009 / 250000000000 : ℝ) (322852978021 / 500000000000 : ℝ) := by
  exact Encl.pow b3040 (by norm_num) 3 (by norm_num) (by norm_num)

def e3043 : ℝ := e3042 / e35
lemma b3043 : Encl e3043 (107617659339 / 500000000000 : ℝ) (215235318681 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3042 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3044 : ℝ := e3041 + e3043
lemma b3044 : Encl e3044 (17574618453 / 1000000000000 : ℝ) (17574618459 / 1000000000000 : ℝ) := by
  exact Encl.add b3041 b3043 (by norm_num) (by norm_num)

def e3045 : ℝ := e8 * e3044
lemma b3045 : Encl e3045 (17223126083 / 1000000000000 : ℝ) (1722312609 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b3044 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3046 : ℝ := e3038 / e3040
lemma b3046 : Encl e3046 (292641668577 / 1000000000000 : ℝ) (292641668581 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3038 b3040 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3047 : ℝ := e3046 - e23
lemma b3047 : Encl e3047 (-1707358331423 / 1000000000000 : ℝ) (-1707358331419 / 1000000000000 : ℝ) := by
  exact Encl.sub b3046 b23 (by norm_num) (by norm_num)

def e3048 : ℝ := e23 * e3040
lemma b3048 : Encl e3048 (864327366889 / 500000000000 : ℝ) (864327366891 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b3040 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3049 : ℝ := e3047 + e3048
lemma b3049 : Encl e3049 (4259280471 / 200000000000 : ℝ) (21296402363 / 1000000000000 : ℝ) := by
  exact Encl.add b3047 b3048 (by norm_num) (by norm_num)

def e3050 : ℝ := e3049 / e43
lemma b3050 : Encl e3050 (425928047 / 1000000000000 : ℝ) (26620503 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b3049 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3051 : ℝ := e3045 - e3050
lemma b3051 : Encl e3051 (3359439607 / 200000000000 : ℝ) (16797198043 / 1000000000000 : ℝ) := by
  exact Encl.sub b3045 b3050 (by norm_num) (by norm_num)

def e3052 : ℝ := e3037 * e3051
lemma b3052 : Encl e3052 (4227684181 / 200000000000 : ℝ) (5284605229 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b3037 b3051 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3053 : ℝ := e3036 + e3052
lemma b3053 : Encl e3053 (-302030650889 / 1000000000000 : ℝ) (-75507662719 / 250000000000 : ℝ) := by
  exact Encl.add b3036 b3052 (by norm_num) (by norm_num)

def e3054 : ℝ := e5 + e3040
lemma b3054 : Encl e3054 (1864327366889 / 1000000000000 : ℝ) (1864327366891 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3040 (by norm_num) (by norm_num)

def e3055 : ℝ := e3024 / e3054
lemma b3055 : Encl e3055 (269764650297 / 1000000000000 : ℝ) (269764650299 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3024 b3054 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3056 : ℝ := e3055 ^ 2
lemma b3056 : Encl e3056 (72772966549 / 1000000000000 : ℝ) (72772966551 / 1000000000000 : ℝ) := by
  exact Encl.pow b3055 (by norm_num) 2 (by norm_num) (by norm_num)

def e3057 : ℝ := e5 + e3056
lemma b3057 : Encl e3057 (1072772966549 / 1000000000000 : ℝ) (1072772966551 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3056 (by norm_num) (by norm_num)

def e3058 : ℝ := Real.sqrt e3057
lemma b3058 : Encl e3058 (1035747539967 / 1000000000000 : ℝ) (1035747539969 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b3057 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3059 : ℝ := e5 + e3058
lemma b3059 : Encl e3059 (2035747539967 / 1000000000000 : ℝ) (2035747539969 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3058 (by norm_num) (by norm_num)

def e3060 : ℝ := e3055 / e3059
lemma b3060 : Encl e3060 (132513803897 / 1000000000000 : ℝ) (132513803899 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3055 b3059 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3061 : ℝ := Real.arcsin e3024
lemma b3061 : Encl e3061 (526984926001 / 1000000000000 : ℝ) (52698492601 / 100000000000 : ℝ) := by
  apply Encl.arcsin (z := e3024) (a := (132513803897 / 1000000000000 : ℝ)) (b := (132513803899 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (50292962017 / 100000000000 : ℝ) by norm_num).trans b3024.1
        exact b3024.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e3024) (132513803897 / 1000000000000 : ℝ) (132513803899 / 1000000000000 : ℝ) from b3060) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e3062 : ℝ := e59 * e3061
lemma b3062 : Encl e3062 (13438115613 / 50000000000 : ℝ) (134381156133 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b3061 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3063 : ℝ := e61 * e3024
lemma b3063 : Encl e3063 (246435513883 / 1000000000000 : ℝ) (61608878471 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b3024 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3064 : ℝ := e3063 * e3040
lemma b3064 : Encl e3064 (106500479411 / 500000000000 : ℝ) (26625119853 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b3063 b3040 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3065 : ℝ := e3062 - e3064
lemma b3065 : Encl e3065 (13940338359 / 250000000000 : ℝ) (13940338361 / 250000000000 : ℝ) := by
  exact Encl.sub b3062 b3064 (by norm_num) (by norm_num)

def e3066 : ℝ := e43 * e3040
lemma b3066 : Encl e3066 (864327366889 / 20000000000 : ℝ) (864327366891 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b3040 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3067 : ℝ := e3024 / e3066
lemma b3067 : Encl e3067 (11637479951 / 1000000000000 : ℝ) (727342497 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b3024 b3066 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3068 : ℝ := e3065 - e3067
lemma b3068 : Encl e3068 (11030968371 / 250000000000 : ℝ) (44123873493 / 1000000000000 : ℝ) := by
  exact Encl.sub b3065 b3067 (by norm_num) (by norm_num)

def e3069 : ℝ := e183 - e3068
lemma b3069 : Encl e3069 (476028896019 / 1000000000000 : ℝ) (476028896159 / 1000000000000 : ℝ) := by
  exact Encl.sub b183 b3068 (by norm_num) (by norm_num)

def e3070 : ℝ := e3069 / e3023
lemma b3070 : Encl e3070 (75321027851 / 250000000000 : ℝ) (150642055747 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b3069 b3023 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3071 : ℝ := e3053 + e3070
lemma b3071 : Encl e3071 (-149307897 / 200000000000 : ℝ) (-373269691 / 500000000000 : ℝ) := by
  exact Encl.add b3053 b3070 (by norm_num) (by norm_num)

def e3072 : ℝ := e924 / e3023
lemma b3072 : Encl e3072 (151898734177 / 250000000000 : ℝ) (607594936709 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b924 b3023 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3073 : ℝ := min e7 e3072
lemma b3073 : Encl e3073 (151898734177 / 250000000000 : ℝ) (607594936709 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b3072 (by norm_num) (by norm_num)

def e3074 : ℝ := e3073 - e5
lemma b3074 : Encl e3074 (-98101265823 / 250000000000 : ℝ) (-392405063291 / 1000000000000 : ℝ) := by
  exact Encl.sub b3073 b5 (by norm_num) (by norm_num)

def e3075 : ℝ := e23 * e3023
lemma b3075 : Encl e3075 (79 / 25 : ℝ) (79 / 25 : ℝ) := by
  exact Encl.mul_nonneg b23 b3023 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3076 : ℝ := e3075 * e3033
lemma b3076 : Encl e3076 (1038059438199 / 500000000000 : ℝ) (1038059438201 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b3075 b3033 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3077 : ℝ := e3076 / e0
lemma b3077 : Encl e3077 (2643396653 / 4000000000 : ℝ) (165212290813 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b3076 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3078 : ℝ := e3074 + e3077
lemma b3078 : Encl e3078 (134222049979 / 500000000000 : ℝ) (268444099961 / 1000000000000 : ℝ) := by
  exact Encl.add b3074 b3077 (by norm_num) (by norm_num)

def e3079 : ℝ := e23 * e3027
lemma b3079 : Encl e3079 (6241 / 1250 : ℝ) (6241 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b23 b3027 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3080 : ℝ := e3079 * e3033
lemma b3080 : Encl e3080 (328026782471 / 100000000000 : ℝ) (820066956179 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b3079 b3033 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3081 : ℝ := e0 + e3080
lemma b3081 : Encl e3081 (6421860478299 / 1000000000000 : ℝ) (3210930239153 / 500000000000 : ℝ) := by
  exact Encl.add b0 b3080 (by norm_num) (by norm_num)

def e3082 : ℝ := Real.sqrt e3081
lemma b3082 : Encl e3082 (79191843793 / 31250000000 : ℝ) (2534139001379 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b3081 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3083 : ℝ := e932 * e3082
lemma b3083 : Encl e3083 (806641497101 / 500000000000 : ℝ) (1613282994207 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b3082 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3084 : ℝ := e3023 ^ 3
lemma b3084 : Encl e3084 (493039 / 125000 : ℝ) (493039 / 125000 : ℝ) := by
  exact Encl.pow b3023 (by norm_num) 3 (by norm_num) (by norm_num)

def e3085 : ℝ := e939 * e3084
lemma b3085 : Encl e3085 (33033613 / 62500000 : ℝ) (33033613 / 62500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b3084 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3086 : ℝ := min e3085 e941
lemma b3086 : Encl e3086 (9 / 25 : ℝ) (9 / 25 : ℝ) := by
  exact Encl.min b3085 b941 (by norm_num) (by norm_num)

def e3087 : ℝ := e23 * e3078
lemma b3087 : Encl e3087 (134222049979 / 250000000000 : ℝ) (268444099961 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b3078 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3088 : ℝ := e944 * e3086
lemma b3088 : Encl e3088 (54 / 25 : ℝ) (54 / 25 : ℝ) := by
  exact Encl.mul_nonneg b944 b3086 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3089 : ℝ := e3083 ^ 2
lemma b3089 : Encl e3089 (2602682019381 / 1000000000000 : ℝ) (1301341009699 / 500000000000 : ℝ) := by
  exact Encl.pow b3083 (by norm_num) 2 (by norm_num) (by norm_num)

def e3090 : ℝ := e3088 * e3089
lemma b3090 : Encl e3090 (2810896580931 / 500000000000 : ℝ) (56217931619 / 10000000000 : ℝ) := by
  exact Encl.mul_nonneg b3088 b3089 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3091 : ℝ := e3090 * e3078
lemma b3091 : Encl e3091 (754568602743 / 500000000000 : ℝ) (754568602757 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b3090 b3078 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3092 : ℝ := e3091 / e9
lemma b3092 : Encl e3092 (2694887866939 / 500000000000 : ℝ) (5389775733979 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3091 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3093 : ℝ := e5 + e3092
lemma b3093 : Encl e3093 (3194887866939 / 500000000000 : ℝ) (6389775733979 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3092 (by norm_num) (by norm_num)

def e3094 : ℝ := Real.sqrt e3093
lemma b3094 : Encl e3094 (252780057241 / 100000000000 : ℝ) (2527800572431 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b3093 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3095 : ℝ := e5 + e3094
lemma b3095 : Encl e3095 (352780057241 / 100000000000 : ℝ) (3527800572431 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3094 (by norm_num) (by norm_num)

def e3096 : ℝ := e3087 / e3095
lemma b3096 : Encl e3096 (3804694943 / 25000000000 : ℝ) (38046949431 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b3087 b3095 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3097 : ℝ := e3086 * e954
lemma b3097 : Encl e3097 (83349 / 25000000 : ℝ) (83349 / 25000000 : ℝ) := by
  exact Encl.mul_nonneg b3086 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3098 : ℝ := e3078 - e3096
lemma b3098 : Encl e3098 (58128151117 / 500000000000 : ℝ) (116256302241 / 1000000000000 : ℝ) := by
  exact Encl.sub b3078 b3096 (by norm_num) (by norm_num)

def e3099 : ℝ := e3098 / e3083
lemma b3099 : Encl e3099 (72061939939 / 1000000000000 : ℝ) (14412387989 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b3098 b3083 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3100 : ℝ := e3099 ^ 2
lemma b3100 : Encl e3100 (5192923187 / 1000000000000 : ℝ) (5192923189 / 1000000000000 : ℝ) := by
  exact Encl.pow b3099 (by norm_num) 2 (by norm_num) (by norm_num)

def e3101 : ℝ := e9 * e3100
lemma b3101 : Encl e3101 (363504623 / 250000000000 : ℝ) (1454018493 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b3100 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3102 : ℝ := e3096 ^ 3
lemma b3102 : Encl e3102 (881210181 / 250000000000 : ℝ) (140993629 / 40000000000 : ℝ) := by
  exact Encl.pow b3096 (by norm_num) 3 (by norm_num) (by norm_num)

def e3103 : ℝ := e3086 * e3102
lemma b3103 : Encl e3103 (63447133 / 50000000000 : ℝ) (1268942661 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b3086 b3102 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3104 : ℝ := e3101 + e3103
lemma b3104 : Encl e3104 (10636567 / 3906250000 : ℝ) (1361480577 / 500000000000 : ℝ) := by
  exact Encl.add b3101 b3103 (by norm_num) (by norm_num)

def e3105 : ℝ := min e3097 e3104
lemma b3105 : Encl e3105 (10636567 / 3906250000 : ℝ) (1361480577 / 500000000000 : ℝ) := by
  exact Encl.min b3097 b3104 (by norm_num) (by norm_num)

def e3106 : ℝ := (81 / 50 : ℝ)
lemma b3106 : Encl e3106 (81 / 50 : ℝ) (81 / 50 : ℝ) := by
  exact Encl.exact (81 / 50 : ℝ)

def e3107 : ℝ := e3106 / e0
lemma b3107 : Encl e3107 (515662015617 / 1000000000000 : ℝ) (257831007809 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b3106 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3108 : ℝ := e8 * e3106
lemma b3108 : Encl e3108 (3969 / 2500 : ℝ) (3969 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b3106 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3109 : ℝ := e3108 / e0
lemma b3109 : Encl e3109 (101069755061 / 200000000000 : ℝ) (252674387653 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b3108 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3110 : ℝ := e3106 ^ 2
lemma b3110 : Encl e3110 (6561 / 2500 : ℝ) (6561 / 2500 : ℝ) := by
  exact Encl.pow b3106 (by norm_num) 2 (by norm_num) (by norm_num)

def e3111 : ℝ := e17 * e3110
lemma b3111 : Encl e3111 (6561 / 625 : ℝ) (6561 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b3110 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3112 : ℝ := e3111 / e0
lemma b3112 : Encl e3112 (1670744930601 / 500000000000 : ℝ) (3341489861203 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3111 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3113 : ℝ := e5 + e3112
lemma b3113 : Encl e3113 (2170744930601 / 500000000000 : ℝ) (4341489861203 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3112 (by norm_num) (by norm_num)

def e3114 : ℝ := Real.sqrt e3113
lemma b3114 : Encl e3114 (260453026631 / 125000000000 : ℝ) (2083624213049 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b3113 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3115 : ℝ := e5 + e3114
lemma b3115 : Encl e3115 (385453026631 / 125000000000 : ℝ) (3083624213049 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3114 (by norm_num) (by norm_num)

def e3116 : ℝ := e23 / e3115
lemma b3116 : Encl e3116 (648587461317 / 1000000000000 : ℝ) (648587461319 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b3115 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3117 : ℝ := e9 * e3116
lemma b3117 : Encl e3117 (11350280573 / 62500000000 : ℝ) (18160448917 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b3116 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3118 : ℝ := e3109 + e3117
lemma b3118 : Encl e3118 (686953264473 / 1000000000000 : ℝ) (171738316119 / 250000000000 : ℝ) := by
  exact Encl.add b3109 b3117 (by norm_num) (by norm_num)

def e3119 : ℝ := e3118 - e5
lemma b3119 : Encl e3119 (-313046735527 / 1000000000000 : ℝ) (-78261683881 / 250000000000 : ℝ) := by
  exact Encl.sub b3118 b5 (by norm_num) (by norm_num)

def e3120 : ℝ := e0 / e3110
lemma b3120 : Encl e3120 (598535408777 / 500000000000 : ℝ) (239414163511 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b3110 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3121 : ℝ := e3107 ^ 2
lemma b3121 : Encl e3121 (5318146287 / 20000000000 : ℝ) (16619207147 / 62500000000 : ℝ) := by
  exact Encl.pow b3107 (by norm_num) 2 (by norm_num) (by norm_num)

def e3122 : ℝ := e5 - e3121
lemma b3122 : Encl e3122 (45880792853 / 62500000000 : ℝ) (14681853713 / 20000000000 : ℝ) := by
  exact Encl.sub b5 b3121 (by norm_num) (by norm_num)

def e3123 : ℝ := Real.sqrt e3122
lemma b3123 : Encl e3123 (428396045047 / 500000000000 : ℝ) (53549505631 / 62500000000 : ℝ) := by
  exact Encl.sqrt b3122 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3124 : ℝ := e29 - e3123
lemma b3124 : Encl e3124 (-19012542343 / 100000000000 : ℝ) (-190125423427 / 1000000000000 : ℝ) := by
  exact Encl.sub b29 b3123 (by norm_num) (by norm_num)

def e3125 : ℝ := e3123 ^ 3
lemma b3125 : Encl e3125 (314482403229 / 500000000000 : ℝ) (9827575101 / 15625000000 : ℝ) := by
  exact Encl.pow b3123 (by norm_num) 3 (by norm_num) (by norm_num)

def e3126 : ℝ := e3125 / e35
lemma b3126 : Encl e3126 (104827467743 / 500000000000 : ℝ) (3275858367 / 15625000000 : ℝ) := by
  exact Encl.div_nonneg b3125 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3127 : ℝ := e3124 + e3126
lemma b3127 : Encl e3127 (2441189007 / 125000000000 : ℝ) (19529512061 / 1000000000000 : ℝ) := by
  exact Encl.add b3124 b3126 (by norm_num) (by norm_num)

def e3128 : ℝ := e8 * e3127
lemma b3128 : Encl e3128 (9569460907 / 500000000000 : ℝ) (956946091 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b3127 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3129 : ℝ := e3121 / e3123
lemma b3129 : Encl e3129 (62070440991 / 200000000000 : ℝ) (310352204959 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3121 b3123 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3130 : ℝ := e3129 - e23
lemma b3130 : Encl e3130 (-337929559009 / 200000000000 : ℝ) (-1689647795041 / 1000000000000 : ℝ) := by
  exact Encl.sub b3129 b23 (by norm_num) (by norm_num)

def e3131 : ℝ := e23 * e3123
lemma b3131 : Encl e3131 (428396045047 / 250000000000 : ℝ) (53549505631 / 31250000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b3123 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3132 : ℝ := e3130 + e3131
lemma b3132 : Encl e3132 (23936385143 / 1000000000000 : ℝ) (23936385151 / 1000000000000 : ℝ) := by
  exact Encl.add b3130 b3131 (by norm_num) (by norm_num)

def e3133 : ℝ := e3132 / e43
lemma b3133 : Encl e3133 (239363851 / 500000000000 : ℝ) (59840963 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b3132 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3134 : ℝ := e3128 - e3133
lemma b3134 : Encl e3134 (1866019411 / 100000000000 : ℝ) (9330097059 / 500000000000 : ℝ) := by
  exact Encl.sub b3128 b3133 (by norm_num) (by norm_num)

def e3135 : ℝ := e3120 * e3134
lemma b3135 : Encl e3135 (11168786909 / 500000000000 : ℝ) (22337573829 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b3120 b3134 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3136 : ℝ := e3119 + e3135
lemma b3136 : Encl e3136 (-290709161709 / 1000000000000 : ℝ) (-58141832339 / 200000000000 : ℝ) := by
  exact Encl.add b3119 b3135 (by norm_num) (by norm_num)

def e3137 : ℝ := e5 + e3123
lemma b3137 : Encl e3137 (928396045047 / 500000000000 : ℝ) (116049505631 / 62500000000 : ℝ) := by
  exact Encl.add b5 b3123 (by norm_num) (by norm_num)

def e3138 : ℝ := e3107 / e3137
lemma b3138 : Encl e3138 (277716615859 / 1000000000000 : ℝ) (277716615861 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3107 b3137 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3139 : ℝ := e3138 ^ 2
lemma b3139 : Encl e3139 (19281629681 / 250000000000 : ℝ) (38563259363 / 500000000000 : ℝ) := by
  exact Encl.pow b3138 (by norm_num) 2 (by norm_num) (by norm_num)

def e3140 : ℝ := e5 + e3139
lemma b3140 : Encl e3140 (269281629681 / 250000000000 : ℝ) (538563259363 / 500000000000 : ℝ) := by
  exact Encl.add b5 b3139 (by norm_num) (by norm_num)

def e3141 : ℝ := Real.sqrt e3140
lemma b3141 : Encl e3141 (1037847059409 / 1000000000000 : ℝ) (1037847059411 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b3140 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3142 : ℝ := e5 + e3141
lemma b3142 : Encl e3142 (2037847059409 / 1000000000000 : ℝ) (2037847059411 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3141 (by norm_num) (by norm_num)

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
