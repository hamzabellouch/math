import OAI.Analysis.PlanarPacking.Certificate.LowBlock13_0
import OAI.Analysis.PlanarPacking.Certificate.LowBlock13_1
import OAI.Analysis.PlanarPacking.Certificate.LowBlock13_10
import OAI.Analysis.PlanarPacking.Certificate.LowBlock13_11
import OAI.Analysis.PlanarPacking.Certificate.CoarseBound13

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein13
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 29821224063817276671137623802, hi := 29821224063989662876308108665}
lemma t0_checked : ((hm13_0_0_2.realAnswer).add hm13_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 13 (1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_0_0_2.realContains hm13_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 22083628749871870953822056461, hi := 22083628750005079269001806055}
lemma t1_checked : ((hm13_0_0_3.realAnswer).add hm13_1_1_3.realAnswer).scale (-1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 13 (1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_0_0_3.realContains hm13_1_1_3.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -39549591852473639695565740161, hi := -39549591852395356995595025794}
lemma t2_checked : ((hm13_0_0_4.realAnswer).add hm13_1_1_4.realAnswer).scale (-1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 13 (1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_0_0_4.realContains hm13_1_1_4.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -16287987057975874090764622194, hi := -16287987057938847631614690962}
lemma t3_checked : ((hm13_0_0_5.realAnswer).add hm13_1_1_5.realAnswer).scale (-1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 13 (1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_0_0_5.realContains hm13_1_1_5.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 21959161406173820862327710701, hi := 21959161406188463670297247761}
lemma t4_checked : ((hm13_0_0_6.realAnswer).add hm13_1_1_6.realAnswer).scale (-1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 13 (1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_0_0_6.realContains hm13_1_1_6.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 2080229291790070133000241838, hi := 2080229291795045662057462032}
lemma t5_checked : ((hm13_0_0_7.realAnswer).add hm13_1_1_7.realAnswer).scale (-1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 13 (1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_0_0_7.realContains hm13_1_1_7.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -4849327652081585517855136652, hi := -4849327652080103035441991903}
lemma t6_checked : ((hm13_0_0_8.realAnswer).add hm13_1_1_8.realAnswer).scale (-1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 13 (1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_0_0_8.realContains hm13_1_1_8.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 70417611179575556189134935, hi := 70417611179969016957147313}
lemma t7_checked : ((hm13_0_0_9.realAnswer).add hm13_1_1_9.realAnswer).scale (-1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 13 (1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_0_0_9.realContains hm13_1_1_9.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 568327665836439860746004599, hi := 568327665836534054320712239}
lemma t8_checked : ((hm13_0_0_10.realAnswer).add hm13_1_1_10.realAnswer).scale (-1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 13 (1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_0_0_10.realContains hm13_1_1_10.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := -39105720212374332738407046, hi := -39105720212353781625172406}
lemma t9_checked : ((hm13_0_0_11.realAnswer).add hm13_1_1_11.realAnswer).scale (-1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 13 (1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_0_0_11.realContains hm13_1_1_11.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -40204387991544782970317224, hi := -40204387991540660187315315}
lemma t10_checked : ((hm13_0_0_12.realAnswer).add hm13_1_1_12.realAnswer).scale (-1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 13 (1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_0_0_12.realContains hm13_1_1_12.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -2531115368513107029833780037, hi := 2531115368513107029833780037}
lemma t11_contains : t11.Contains (sourcePower false 13 (1/1) 2 11) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (1/1) 2 11 coarse_13_13) <;> norm_num [t11,precision]
noncomputable def t12 : RBox := {lo := -617291382224693317143528265, hi := 617291382224693317143528265}
lemma t12_contains : t12.Contains (sourcePower false 13 (1/1) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (1/1) 2 12 coarse_13_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -144478140411823014312463399, hi := 144478140411823014312463399}
lemma t13_contains : t13.Contains (sourcePower false 13 (1/1) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (1/1) 2 13 coarse_13_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -32567611871130225775617023, hi := 32567611871130225775617023}
lemma t14_contains : t14.Contains (sourcePower false 13 (1/1) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (1/1) 2 14 coarse_13_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -7086462145518744700765859, hi := 7086462145518744700765859}
lemma t15_contains : t15.Contains (sourcePower false 13 (1/1) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (1/1) 2 15 coarse_13_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -1490272985556831369284206, hi := 1490272985556831369284206}
lemma t16_contains : t16.Contains (sourcePower false 13 (1/1) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (1/1) 2 16 coarse_13_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -303042818377332642491714, hi := 303042818377332642491714}
lemma t17_contains : t17.Contains (sourcePower false 13 (1/1) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (1/1) 2 17 coarse_13_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -59589010613871900078267, hi := 59589010613871900078267}
lemma t18_contains : t18.Contains (sourcePower false 13 (1/1) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (1/1) 2 18 coarse_13_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -11329372415748521439348, hi := 11329372415748521439348}
lemma t19_contains : t19.Contains (sourcePower false 13 (1/1) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (1/1) 2 19 coarse_13_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -2082539517045679030472, hi := 2082539517045679030472}
lemma t20_contains : t20.Contains (sourcePower false 13 (1/1) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (1/1) 2 20 coarse_13_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -370140407122910181103, hi := 370140407122910181103}
lemma t21_contains : t21.Contains (sourcePower false 13 (1/1) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (1/1) 2 21 coarse_13_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -63628917450002357168, hi := 63628917450002357168}
lemma t22_contains : t22.Contains (sourcePower false 13 (1/1) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (1/1) 2 22 coarse_13_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -10584744548565259465, hi := 10584744548565259465}
lemma t23_contains : t23.Contains (sourcePower false 13 (1/1) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (1/1) 2 23 coarse_13_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -1705111562507517738, hi := 1705111562507517738}
lemma t24_contains : t24.Contains (sourcePower false 13 (1/1) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (1/1) 2 24 coarse_13_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -266227122488009142, hi := 266227122488009142}
lemma t25_contains : t25.Contains (sourcePower false 13 (1/1) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (1/1) 2 25 coarse_13_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -40328799510286982, hi := 40328799510286982}
lemma t26_contains : t26.Contains (sourcePower false 13 (1/1) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (1/1) 2 26 coarse_13_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -5933603166316064, hi := 5933603166316064}
lemma t27_contains : t27.Contains (sourcePower false 13 (1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (1/1) 2 27 coarse_13_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -848915492766886, hi := 848915492766886}
lemma t28_contains : t28.Contains (sourcePower false 13 (1/1) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (1/1) 2 28 coarse_13_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 13 (1/1) 2 r.val) := by
  fin_cases r
  · exact t0_contains
  · exact t1_contains
  · exact t2_contains
  · exact t3_contains
  · exact t4_contains
  · exact t5_contains
  · exact t6_contains
  · exact t7_contains
  · exact t8_contains
  · exact t9_contains
  · exact t10_contains
  · exact t11_contains
  · exact t12_contains
  · exact t13_contains
  · exact t14_contains
  · exact t15_contains
  · exact t16_contains
  · exact t17_contains
  · exact t18_contains
  · exact t19_contains
  · exact t20_contains
  · exact t21_contains
  · exact t22_contains
  · exact t23_contains
  · exact t24_contains
  · exact t25_contains
  · exact t26_contains
  · exact t27_contains
  · exact t28_contains
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (1/1) 2) k.val := by
  fin_cases k
  · exact bound0
  · exact bound1
  · exact bound2
  · exact bound3
  · exact bound4
  · exact bound5
  · exact bound6
  · exact bound7
  · exact bound8
  · exact bound9
  · exact bound10
  · exact bound11
  · exact bound12
  · exact bound13
  · exact bound14
  · exact bound15
  · exact bound16
  · exact bound17
  · exact bound18
  · exact bound19
  · exact bound20
  · exact bound21
  · exact bound22
  · exact bound23
  · exact bound24
  · exact bound25
  · exact bound26
  · exact bound27
  · exact bound28
end N0_right
namespace N1_right
noncomputable def t0 : RBox := {lo := 27223491618073330399183537660, hi := 27223491618214876053585952206}
lemma t0_checked : ((hm13_1_0_2.realAnswer).add hm13_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 13 (1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_1_0_2.realContains hm13_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 19729896933860661043685660522, hi := 19729896933970032198365550671}
lemma t1_checked : ((hm13_1_0_3.realAnswer).add hm13_0_1_3.realAnswer).scale (1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 13 (1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_1_0_3.realContains hm13_0_1_3.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -36342515520849776680311370050, hi := -36342515520785500491121131397}
lemma t2_checked : ((hm13_1_0_4.realAnswer).add hm13_0_1_4.realAnswer).scale (1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 13 (1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_1_0_4.realContains hm13_0_1_4.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -14219450044092494594679345116, hi := -14219450044062091017583973631}
lemma t3_checked : ((hm13_1_0_5.realAnswer).add hm13_0_1_5.realAnswer).scale (1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 13 (1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_1_0_5.realContains hm13_0_1_5.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 20187768107909957201160455486, hi := 20187768107921981948148537922}
lemma t4_checked : ((hm13_1_0_6.realAnswer).add hm13_0_1_6.realAnswer).scale (1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 13 (1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_1_0_6.realContains hm13_0_1_6.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 1510198691851033269263384770, hi := 1510198691855119706691150416}
lemma t5_checked : ((hm13_1_0_7.realAnswer).add hm13_0_1_7.realAnswer).scale (1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 13 (1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_1_0_7.realContains hm13_0_1_7.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -4407077813198705281040618902, hi := -4407077813197487485882322444}
lemma t6_checked : ((hm13_1_0_8.realAnswer).add hm13_0_1_8.realAnswer).scale (1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 13 (1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_1_0_8.realContains hm13_0_1_8.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 156355683435983820654671470, hi := 156355683436307124120191272}
lemma t7_checked : ((hm13_1_0_9.realAnswer).add hm13_0_1_9.realAnswer).scale (1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 13 (1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_1_0_9.realContains hm13_0_1_9.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 505401686124750801873813659, hi := 505401686124828236400194270}
lemma t8_checked : ((hm13_1_0_10.realAnswer).add hm13_0_1_10.realAnswer).scale (1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 13 (1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_1_0_10.realContains hm13_0_1_10.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := -47651784141944797773798389, hi := -47651784141927889600352125}
lemma t9_checked : ((hm13_1_0_11.realAnswer).add hm13_0_1_11.realAnswer).scale (1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 13 (1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_1_0_11.realContains hm13_0_1_11.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -34368228429466291474973984, hi := -34368228429462894776612165}
lemma t10_checked : ((hm13_1_0_12.realAnswer).add hm13_0_1_12.realAnswer).scale (1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 13 (1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_1_0_12.realContains hm13_0_1_12.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -2531115368513107029833780037, hi := 2531115368513107029833780037}
lemma t11_contains : t11.Contains (sourcePower true 13 (1/1) 2 11) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (1/1) 2 11 coarse_13_13) <;> norm_num [t11,precision]
noncomputable def t12 : RBox := {lo := -617291382224693317143528265, hi := 617291382224693317143528265}
lemma t12_contains : t12.Contains (sourcePower true 13 (1/1) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (1/1) 2 12 coarse_13_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -144478140411823014312463399, hi := 144478140411823014312463399}
lemma t13_contains : t13.Contains (sourcePower true 13 (1/1) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (1/1) 2 13 coarse_13_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -32567611871130225775617023, hi := 32567611871130225775617023}
lemma t14_contains : t14.Contains (sourcePower true 13 (1/1) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (1/1) 2 14 coarse_13_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -7086462145518744700765859, hi := 7086462145518744700765859}
lemma t15_contains : t15.Contains (sourcePower true 13 (1/1) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (1/1) 2 15 coarse_13_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -1490272985556831369284206, hi := 1490272985556831369284206}
lemma t16_contains : t16.Contains (sourcePower true 13 (1/1) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (1/1) 2 16 coarse_13_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -303042818377332642491714, hi := 303042818377332642491714}
lemma t17_contains : t17.Contains (sourcePower true 13 (1/1) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (1/1) 2 17 coarse_13_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -59589010613871900078267, hi := 59589010613871900078267}
lemma t18_contains : t18.Contains (sourcePower true 13 (1/1) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (1/1) 2 18 coarse_13_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -11329372415748521439348, hi := 11329372415748521439348}
lemma t19_contains : t19.Contains (sourcePower true 13 (1/1) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (1/1) 2 19 coarse_13_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -2082539517045679030472, hi := 2082539517045679030472}
lemma t20_contains : t20.Contains (sourcePower true 13 (1/1) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (1/1) 2 20 coarse_13_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -370140407122910181103, hi := 370140407122910181103}
lemma t21_contains : t21.Contains (sourcePower true 13 (1/1) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (1/1) 2 21 coarse_13_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -63628917450002357168, hi := 63628917450002357168}
lemma t22_contains : t22.Contains (sourcePower true 13 (1/1) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (1/1) 2 22 coarse_13_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -10584744548565259465, hi := 10584744548565259465}
lemma t23_contains : t23.Contains (sourcePower true 13 (1/1) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (1/1) 2 23 coarse_13_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -1705111562507517738, hi := 1705111562507517738}
lemma t24_contains : t24.Contains (sourcePower true 13 (1/1) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (1/1) 2 24 coarse_13_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -266227122488009142, hi := 266227122488009142}
lemma t25_contains : t25.Contains (sourcePower true 13 (1/1) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (1/1) 2 25 coarse_13_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -40328799510286982, hi := 40328799510286982}
lemma t26_contains : t26.Contains (sourcePower true 13 (1/1) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (1/1) 2 26 coarse_13_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -5933603166316064, hi := 5933603166316064}
lemma t27_contains : t27.Contains (sourcePower true 13 (1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (1/1) 2 27 coarse_13_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -848915492766886, hi := 848915492766886}
lemma t28_contains : t28.Contains (sourcePower true 13 (1/1) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (1/1) 2 28 coarse_13_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 13 (1/1) 2 r.val) := by
  fin_cases r
  · exact t0_contains
  · exact t1_contains
  · exact t2_contains
  · exact t3_contains
  · exact t4_contains
  · exact t5_contains
  · exact t6_contains
  · exact t7_contains
  · exact t8_contains
  · exact t9_contains
  · exact t10_contains
  · exact t11_contains
  · exact t12_contains
  · exact t13_contains
  · exact t14_contains
  · exact t15_contains
  · exact t16_contains
  · exact t17_contains
  · exact t18_contains
  · exact t19_contains
  · exact t20_contains
  · exact t21_contains
  · exact t22_contains
  · exact t23_contains
  · exact t24_contains
  · exact t25_contains
  · exact t26_contains
  · exact t27_contains
  · exact t28_contains
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (1/1) 2) k.val := by
  fin_cases k
  · exact bound0
  · exact bound1
  · exact bound2
  · exact bound3
  · exact bound4
  · exact bound5
  · exact bound6
  · exact bound7
  · exact bound8
  · exact bound9
  · exact bound10
  · exact bound11
  · exact bound12
  · exact bound13
  · exact bound14
  · exact bound15
  · exact bound16
  · exact bound17
  · exact bound18
  · exact bound19
  · exact bound20
  · exact bound21
  · exact bound22
  · exact bound23
  · exact bound24
  · exact bound25
  · exact bound26
  · exact bound27
  · exact bound28
end N1_right
namespace N0_left
noncomputable def t0 : RBox := {lo := 29821224063817276671137623802, hi := 29821224063989662876308108665}
lemma t0_checked : ((hm13_0_0_2.realAnswer).add hm13_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 13 (-1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_0_0_2.realContains hm13_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -11041814375002539634500903028, hi := -11041814374935935476911028230}
lemma t1_checked : ((hm13_0_0_3.realAnswer).add hm13_1_1_3.realAnswer).scale (1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 13 (-1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_0_0_3.realContains hm13_1_1_3.realContains) (1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -9887397963118409923891435041, hi := -9887397963098839248898756448}
lemma t2_checked : ((hm13_0_0_4.realAnswer).add hm13_1_1_4.realAnswer).scale (-1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 13 (-1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_0_0_4.realContains hm13_1_1_4.realContains) (-1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 2035998382242355953951836370, hi := 2035998382246984261345577775}
lemma t3_checked : ((hm13_0_0_5.realAnswer).add hm13_1_1_5.realAnswer).scale (1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 13 (-1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_0_0_5.realContains hm13_1_1_5.realContains) (1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 1372447587885863803895481918, hi := 1372447587886778979393577986}
lemma t4_checked : ((hm13_0_0_6.realAnswer).add hm13_1_1_6.realAnswer).scale (-1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 13 (-1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_0_0_6.realContains hm13_1_1_6.realContains) (-1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -65007165368595176939295689, hi := -65007165368439691656257557}
lemma t5_checked : ((hm13_0_0_7.realAnswer).add hm13_1_1_7.realAnswer).scale (1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 13 (-1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_0_0_7.realContains hm13_1_1_7.realContains) (1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -75770744563774773716486511, hi := -75770744563751609928781123}
lemma t6_checked : ((hm13_0_0_8.realAnswer).add hm13_1_1_8.realAnswer).scale (-1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 13 (-1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_0_0_8.realContains hm13_1_1_8.realContains) (-1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -550137587343507944977714, hi := -550137587340434032727616}
lemma t7_checked : ((hm13_0_0_9.realAnswer).add hm13_1_1_9.realAnswer).scale (1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 13 (-1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_0_0_9.realContains hm13_1_1_9.realContains) (1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 2220029944673593206039080, hi := 2220029944673961149690283}
lemma t8_checked : ((hm13_0_0_10.realAnswer).add hm13_1_1_10.realAnswer).scale (-1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 13 (-1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_0_0_10.realContains hm13_1_1_10.realContains) (-1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := 76378359789753479736664, hi := 76378359789793618629702}
lemma t9_checked : ((hm13_0_0_11.realAnswer).add hm13_1_1_11.realAnswer).scale (1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 13 (-1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_0_0_11.realContains hm13_1_1_11.realContains) (1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -39262097647992952119451, hi := -39262097647988925964175}
lemma t10_checked : ((hm13_0_0_12.realAnswer).add hm13_1_1_12.realAnswer).scale (-1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 13 (-1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_0_0_12.realContains hm13_1_1_12.realContains) (-1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -1235896176031790541911026, hi := 1235896176031790541911026}
lemma t11_contains : t11.Contains (sourcePower false 13 (-1/2) 2 11) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (-1/2) 2 11 coarse_13_13) <;> norm_num [t11,precision]
noncomputable def t12 : RBox := {lo := -150705903863450516880745, hi := 150705903863450516880745}
lemma t12_contains : t12.Contains (sourcePower false 13 (-1/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (-1/2) 2 12 coarse_13_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -17636491749490114051815, hi := 17636491749490114051815}
lemma t13_contains : t13.Contains (sourcePower false 13 (-1/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (-1/2) 2 13 coarse_13_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -1987769279243788194313, hi := 1987769279243788194313}
lemma t14_contains : t14.Contains (sourcePower false 13 (-1/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (-1/2) 2 14 coarse_13_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -216261662155723410058, hi := 216261662155723410058}
lemma t15_contains : t15.Contains (sourcePower false 13 (-1/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (-1/2) 2 15 coarse_13_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -22739761132153798970, hi := 22739761132153798970}
lemma t16_contains : t16.Contains (sourcePower false 13 (-1/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (-1/2) 2 16 coarse_13_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -2312033221262608662, hi := 2312033221262608662}
lemma t17_contains : t17.Contains (sourcePower false 13 (-1/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (-1/2) 2 17 coarse_13_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -227314035850036240, hi := 227314035850036240}
lemma t18_contains : t18.Contains (sourcePower false 13 (-1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (-1/2) 2 18 coarse_13_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -21609062987801593, hi := 21609062987801593}
lemma t19_contains : t19.Contains (sourcePower false 13 (-1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (-1/2) 2 19 coarse_13_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -1986064450307540, hi := 1986064450307540}
lemma t20_contains : t20.Contains (sourcePower false 13 (-1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (-1/2) 2 20 coarse_13_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -176496699868637, hi := 176496699868637}
lemma t21_contains : t21.Contains (sourcePower false 13 (-1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (-1/2) 2 21 coarse_13_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -15170316088201, hi := 15170316088201}
lemma t22_contains : t22.Contains (sourcePower false 13 (-1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (-1/2) 2 22 coarse_13_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -1261799877711, hi := 1261799877711}
lemma t23_contains : t23.Contains (sourcePower false 13 (-1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (-1/2) 2 23 coarse_13_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -101632568986, hi := 101632568986}
lemma t24_contains : t24.Contains (sourcePower false 13 (-1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (-1/2) 2 24 coarse_13_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -7934186533, hi := 7934186533}
lemma t25_contains : t25.Contains (sourcePower false 13 (-1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (-1/2) 2 25 coarse_13_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -600945943, hi := 600945943}
lemma t26_contains : t26.Contains (sourcePower false 13 (-1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (-1/2) 2 26 coarse_13_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -44208789, hi := 44208789}
lemma t27_contains : t27.Contains (sourcePower false 13 (-1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (-1/2) 2 27 coarse_13_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -3162457, hi := 3162457}
lemma t28_contains : t28.Contains (sourcePower false 13 (-1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 13 (-1/2) 2 28 coarse_13_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 13 (-1/2) 2 r.val) := by
  fin_cases r
  · exact t0_contains
  · exact t1_contains
  · exact t2_contains
  · exact t3_contains
  · exact t4_contains
  · exact t5_contains
  · exact t6_contains
  · exact t7_contains
  · exact t8_contains
  · exact t9_contains
  · exact t10_contains
  · exact t11_contains
  · exact t12_contains
  · exact t13_contains
  · exact t14_contains
  · exact t15_contains
  · exact t16_contains
  · exact t17_contains
  · exact t18_contains
  · exact t19_contains
  · exact t20_contains
  · exact t21_contains
  · exact t22_contains
  · exact t23_contains
  · exact t24_contains
  · exact t25_contains
  · exact t26_contains
  · exact t27_contains
  · exact t28_contains
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 13 (-1/2) 2) k.val := by
  fin_cases k
  · exact bound0
  · exact bound1
  · exact bound2
  · exact bound3
  · exact bound4
  · exact bound5
  · exact bound6
  · exact bound7
  · exact bound8
  · exact bound9
  · exact bound10
  · exact bound11
  · exact bound12
  · exact bound13
  · exact bound14
  · exact bound15
  · exact bound16
  · exact bound17
  · exact bound18
  · exact bound19
  · exact bound20
  · exact bound21
  · exact bound22
  · exact bound23
  · exact bound24
  · exact bound25
  · exact bound26
  · exact bound27
  · exact bound28
end N0_left
namespace N1_left
noncomputable def t0 : RBox := {lo := 27223491618073330399183537660, hi := 27223491618214876053585952206}
lemma t0_checked : ((hm13_1_0_2.realAnswer).add hm13_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 13 (-1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_1_0_2.realContains hm13_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -9864948466985016099182775336, hi := -9864948466930330521842830261}
lemma t1_checked : ((hm13_1_0_3.realAnswer).add hm13_0_1_3.realAnswer).scale (-1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 13 (-1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_1_0_3.realContains hm13_0_1_3.realContains) (-1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -9085628880212444170077842513, hi := -9085628880196375122780282849}
lemma t2_checked : ((hm13_1_0_4.realAnswer).add hm13_0_1_4.realAnswer).scale (1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 13 (-1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_1_0_4.realContains hm13_0_1_4.realContains) (1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 1777431255507761377197996703, hi := 1777431255511561824334918140}
lemma t3_checked : ((hm13_1_0_5.realAnswer).add hm13_0_1_5.realAnswer).scale (-1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 13 (-1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_1_0_5.realContains hm13_0_1_5.realContains) (-1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 1261735506744372325072528467, hi := 1261735506745123871759283621}
lemma t4_checked : ((hm13_1_0_6.realAnswer).add hm13_0_1_6.realAnswer).scale (1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 13 (-1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_1_0_6.realContains hm13_0_1_6.realContains) (1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -47193709120472490834098451, hi := -47193709120344789664480774}
lemma t5_checked : ((hm13_1_0_7.realAnswer).add hm13_0_1_7.realAnswer).scale (-1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 13 (-1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_1_0_7.realContains hm13_0_1_7.realContains) (-1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -68860590831229770016259671, hi := -68860590831210741966911288}
lemma t6_checked : ((hm13_1_0_8.realAnswer).add hm13_0_1_8.realAnswer).scale (1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 13 (-1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_1_0_8.realContains hm13_0_1_8.realContains) (1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -1221528776846149407188995, hi := -1221528776843623598864620}
lemma t7_checked : ((hm13_1_0_9.realAnswer).add hm13_0_1_9.realAnswer).scale (-1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 13 (-1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_1_0_9.realContains hm13_0_1_9.realContains) (-1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 1974225336424807819819584, hi := 1974225336425110298438259}
lemma t8_checked : ((hm13_1_0_10.realAnswer).add hm13_0_1_10.realAnswer).scale (1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 13 (-1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_1_0_10.realContains hm13_0_1_10.realContains) (1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := 93069890902202909375687, hi := 93069890902235933151950}
lemma t9_checked : ((hm13_1_0_11.realAnswer).add hm13_0_1_11.realAnswer).scale (-1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 13 (-1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_1_0_11.realContains hm13_0_1_11.realContains) (-1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -33562723075650675268530, hi := -33562723075647358180285}
lemma t10_checked : ((hm13_1_0_12.realAnswer).add hm13_0_1_12.realAnswer).scale (1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 13 (-1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm13_1_0_12.realContains hm13_0_1_12.realContains) (1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -1235896176031790541911026, hi := 1235896176031790541911026}
lemma t11_contains : t11.Contains (sourcePower true 13 (-1/2) 2 11) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (-1/2) 2 11 coarse_13_13) <;> norm_num [t11,precision]
noncomputable def t12 : RBox := {lo := -150705903863450516880745, hi := 150705903863450516880745}
lemma t12_contains : t12.Contains (sourcePower true 13 (-1/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (-1/2) 2 12 coarse_13_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -17636491749490114051815, hi := 17636491749490114051815}
lemma t13_contains : t13.Contains (sourcePower true 13 (-1/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (-1/2) 2 13 coarse_13_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -1987769279243788194313, hi := 1987769279243788194313}
lemma t14_contains : t14.Contains (sourcePower true 13 (-1/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (-1/2) 2 14 coarse_13_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -216261662155723410058, hi := 216261662155723410058}
lemma t15_contains : t15.Contains (sourcePower true 13 (-1/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (-1/2) 2 15 coarse_13_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -22739761132153798970, hi := 22739761132153798970}
lemma t16_contains : t16.Contains (sourcePower true 13 (-1/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (-1/2) 2 16 coarse_13_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -2312033221262608662, hi := 2312033221262608662}
lemma t17_contains : t17.Contains (sourcePower true 13 (-1/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (-1/2) 2 17 coarse_13_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -227314035850036240, hi := 227314035850036240}
lemma t18_contains : t18.Contains (sourcePower true 13 (-1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (-1/2) 2 18 coarse_13_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -21609062987801593, hi := 21609062987801593}
lemma t19_contains : t19.Contains (sourcePower true 13 (-1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (-1/2) 2 19 coarse_13_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -1986064450307540, hi := 1986064450307540}
lemma t20_contains : t20.Contains (sourcePower true 13 (-1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (-1/2) 2 20 coarse_13_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -176496699868637, hi := 176496699868637}
lemma t21_contains : t21.Contains (sourcePower true 13 (-1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (-1/2) 2 21 coarse_13_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -15170316088201, hi := 15170316088201}
lemma t22_contains : t22.Contains (sourcePower true 13 (-1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (-1/2) 2 22 coarse_13_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -1261799877711, hi := 1261799877711}
lemma t23_contains : t23.Contains (sourcePower true 13 (-1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (-1/2) 2 23 coarse_13_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -101632568986, hi := 101632568986}
lemma t24_contains : t24.Contains (sourcePower true 13 (-1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (-1/2) 2 24 coarse_13_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -7934186533, hi := 7934186533}
lemma t25_contains : t25.Contains (sourcePower true 13 (-1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (-1/2) 2 25 coarse_13_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -600945943, hi := 600945943}
lemma t26_contains : t26.Contains (sourcePower true 13 (-1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (-1/2) 2 26 coarse_13_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -44208789, hi := 44208789}
lemma t27_contains : t27.Contains (sourcePower true 13 (-1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (-1/2) 2 27 coarse_13_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -3162457, hi := 3162457}
lemma t28_contains : t28.Contains (sourcePower true 13 (-1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 13 (-1/2) 2 28 coarse_13_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 13 (-1/2) 2 r.val) := by
  fin_cases r
  · exact t0_contains
  · exact t1_contains
  · exact t2_contains
  · exact t3_contains
  · exact t4_contains
  · exact t5_contains
  · exact t6_contains
  · exact t7_contains
  · exact t8_contains
  · exact t9_contains
  · exact t10_contains
  · exact t11_contains
  · exact t12_contains
  · exact t13_contains
  · exact t14_contains
  · exact t15_contains
  · exact t16_contains
  · exact t17_contains
  · exact t18_contains
  · exact t19_contains
  · exact t20_contains
  · exact t21_contains
  · exact t22_contains
  · exact t23_contains
  · exact t24_contains
  · exact t25_contains
  · exact t26_contains
  · exact t27_contains
  · exact t28_contains
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 13 (-1/2) 2) k.val := by
  fin_cases k
  · exact bound0
  · exact bound1
  · exact bound2
  · exact bound3
  · exact bound4
  · exact bound5
  · exact bound6
  · exact bound7
  · exact bound8
  · exact bound9
  · exact bound10
  · exact bound11
  · exact bound12
  · exact bound13
  · exact bound14
  · exact bound15
  · exact bound16
  · exact bound17
  · exact bound18
  · exact bound19
  · exact bound20
  · exact bound21
  · exact bound22
  · exact bound23
  · exact bound24
  · exact bound25
  · exact bound26
  · exact bound27
  · exact bound28
end N1_left
end SharpPlanar.Bernstein13

end OAI
