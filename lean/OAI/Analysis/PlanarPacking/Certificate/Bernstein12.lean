import OAI.Analysis.PlanarPacking.Certificate.LowBlock12_0
import OAI.Analysis.PlanarPacking.Certificate.LowBlock12_1
import OAI.Analysis.PlanarPacking.Certificate.LowBlock12_10
import OAI.Analysis.PlanarPacking.Certificate.LowBlock12_11
import OAI.Analysis.PlanarPacking.Certificate.CoarseBound12

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein12
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 61451870782754334557887457376, hi := 61451870782926870143619619324}
lemma t0_checked : ((hm12_0_0_2.realAnswer).add hm12_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 12 (1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_0_0_2.realContains hm12_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -68392677232393836247174386897, hi := -68392677232327173032422620753}
lemma t1_checked : ((hm12_0_0_3.realAnswer).add hm12_1_1_3.realAnswer).scale (-1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 12 (1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_0_0_3.realContains hm12_1_1_3.realContains) (-1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := 15351330037314008013857284244, hi := 15351330037333596654915174042}
lemma t2_checked : ((hm12_0_0_4.realAnswer).add hm12_1_1_4.realAnswer).scale (-1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 12 (1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_0_0_4.realContains hm12_1_1_4.realContains) (-1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 6019219521564652454054716063, hi := 6019219521569285273348680292}
lemma t3_checked : ((hm12_0_0_5.realAnswer).add hm12_1_1_5.realAnswer).scale (-1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 12 (1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_0_0_5.realContains hm12_1_1_5.realContains) (-1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := -2207469923573222124698097481, hi := -2207469923572305961399924704}
lemma t4_checked : ((hm12_0_0_6.realAnswer).add hm12_1_1_6.realAnswer).scale (-1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 12 (1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_0_0_6.realContains hm12_1_1_6.realContains) (-1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -172201938830744301018145682, hi := -172201938830588617881209139}
lemma t5_checked : ((hm12_0_0_7.realAnswer).add hm12_1_1_7.realAnswer).scale (-1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 12 (1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_0_0_7.realContains hm12_1_1_7.realContains) (-1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := 114346374233584744018950159, hi := 114346374233607945462155430}
lemma t6_checked : ((hm12_0_0_8.realAnswer).add hm12_1_1_8.realAnswer).scale (-1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 12 (1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_0_0_8.realContains hm12_1_1_8.realContains) (-1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 32497956112314523873831, hi := 32497956115395410721941}
lemma t7_checked : ((hm12_0_0_9.realAnswer).add hm12_1_1_9.realAnswer).scale (-1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 12 (1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_0_0_9.realContains hm12_1_1_9.realContains) (-1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := -3241078729847996661402522, hi := -3241078729847627454098318}
lemma t8_checked : ((hm12_0_0_10.realAnswer).add hm12_1_1_10.realAnswer).scale (-1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 12 (1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_0_0_10.realContains hm12_1_1_10.realContains) (-1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := 122657991969313412264091, hi := 122657991969353773383334}
lemma t9_checked : ((hm12_0_0_11.realAnswer).add hm12_1_1_11.realAnswer).scale (-1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 12 (1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_0_0_11.realContains hm12_1_1_11.realContains) (-1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := 57601146639564352844449, hi := 57601146639568416489346}
lemma t10_checked : ((hm12_0_0_12.realAnswer).add hm12_1_1_12.realAnswer).scale (-1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 12 (1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_0_0_12.realContains hm12_1_1_12.realContains) (-1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -3830130818471174413470, hi := -3830130818470794033735}
lemma t11_checked : ((hm12_0_0_13.realAnswer).add hm12_1_1_13.realAnswer).scale (-1) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 12 (1/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_0_0_13.realContains hm12_1_1_13.realContains) (-1) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -171396147550665061348791, hi := 171396147550665061348791}
lemma t12_contains : t12.Contains (sourcePower false 12 (1/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (1/2) 2 12 coarse_12_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -20540279013060288964123, hi := 20540279013060288964123}
lemma t13_contains : t13.Contains (sourcePower false 12 (1/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (1/2) 2 13 coarse_12_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -2370812092565497112264, hi := 2370812092565497112264}
lemma t14_contains : t14.Contains (sourcePower false 12 (1/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (1/2) 2 14 coarse_12_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -263953881363605769697, hi := 263953881363605769697}
lemma t15_contains : t15.Contains (sourcePower false 12 (1/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (1/2) 2 15 coarse_12_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -28365989397522196385, hi := 28365989397522196385}
lemma t16_contains : t16.Contains (sourcePower false 12 (1/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (1/2) 2 16 coarse_12_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -2943072604808163227, hi := 2943072604808163227}
lemma t17_contains : t17.Contains (sourcePower false 12 (1/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (1/2) 2 17 coarse_12_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -294818953479539848, hi := 294818953479539848}
lemma t18_contains : t18.Contains (sourcePower false 12 (1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (1/2) 2 18 coarse_12_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -28516436648066880, hi := 28516436648066880}
lemma t19_contains : t19.Contains (sourcePower false 12 (1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (1/2) 2 19 coarse_12_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -2663938389153873, hi := 2663938389153873}
lemma t20_contains : t20.Contains (sourcePower false 12 (1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (1/2) 2 20 coarse_12_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -240457452818595, hi := 240457452818595}
lemma t21_contains : t21.Contains (sourcePower false 12 (1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (1/2) 2 21 coarse_12_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -20985905895579, hi := 20985905895579}
lemma t22_contains : t22.Contains (sourcePower false 12 (1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (1/2) 2 22 coarse_12_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -1772419477128, hi := 1772419477128}
lemma t23_contains : t23.Contains (sourcePower false 12 (1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (1/2) 2 23 coarse_12_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -145009275090, hi := 145009275090}
lemma t24_contains : t24.Contains (sourcePower false 12 (1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (1/2) 2 24 coarse_12_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -11505508624, hi := 11505508624}
lemma t25_contains : t25.Contains (sourcePower false 12 (1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (1/2) 2 25 coarse_12_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -886376938, hi := 886376938}
lemma t26_contains : t26.Contains (sourcePower false 12 (1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (1/2) 2 26 coarse_12_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -66385150, hi := 66385150}
lemma t27_contains : t27.Contains (sourcePower false 12 (1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (1/2) 2 27 coarse_12_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -4839517, hi := 4839517}
lemma t28_contains : t28.Contains (sourcePower false 12 (1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (1/2) 2 28 coarse_12_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 12 (1/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (1/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 57107874017072128817429474713, hi := 57107874017213800199224982736}
lemma t0_checked : ((hm12_1_0_2.realAnswer).add hm12_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 12 (1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_1_0_2.realContains hm12_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -64102648638575682381800867583, hi := -64102648638520946701470089508}
lemma t1_checked : ((hm12_1_0_3.realAnswer).add hm12_0_1_3.realAnswer).scale (1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 12 (1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_1_0_3.realContains hm12_0_1_3.realContains) (1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := 14881897462067047697700182100, hi := 14881897462083132231575770777}
lemma t2_checked : ((hm12_1_0_4.realAnswer).add hm12_0_1_4.realAnswer).scale (1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 12 (1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_1_0_4.realContains hm12_0_1_4.realContains) (1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 5451874784449207388662781310, hi := 5451874784453011827281267286}
lemma t3_checked : ((hm12_1_0_5.realAnswer).add hm12_0_1_5.realAnswer).scale (1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 12 (1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_1_0_5.realContains hm12_0_1_5.realContains) (1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := -2107615803192218289586973149, hi := -2107615803191465834166763822}
lemma t4_checked : ((hm12_1_0_6.realAnswer).add hm12_0_1_6.realAnswer).scale (1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 12 (1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_1_0_6.realContains hm12_0_1_6.realContains) (1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -138560400336620494335049796, hi := -138560400336492601637852046}
lemma t5_checked : ((hm12_1_0_7.realAnswer).add hm12_0_1_7.realAnswer).scale (1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 12 (1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_1_0_7.realContains hm12_0_1_7.realContains) (1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := 108003698222192452161017401, hi := 108003698222211518818240316}
lemma t6_checked : ((hm12_1_0_8.realAnswer).add hm12_0_1_8.realAnswer).scale (1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 12 (1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_1_0_8.realContains hm12_0_1_8.realContains) (1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -1168490931924759867310974, hi := -1168490931922226511909750}
lemma t7_checked : ((hm12_1_0_9.realAnswer).add hm12_0_1_9.realAnswer).scale (1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 12 (1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_1_0_9.realContains hm12_0_1_9.realContains) (1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := -3019144120641077049858858, hi := -3019144120640773143387300}
lemma t8_checked : ((hm12_1_0_10.realAnswer).add hm12_0_1_10.realAnswer).scale (1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 12 (1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_1_0_10.realContains hm12_0_1_10.realContains) (1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := 151855211936327173158757, hi := 151855211936360455689282}
lemma t9_checked : ((hm12_1_0_11.realAnswer).add hm12_0_1_11.realAnswer).scale (1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 12 (1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_1_0_11.realContains hm12_0_1_11.realContains) (1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := 52531744323438884876666, hi := 52531744323442246456653}
lemma t10_checked : ((hm12_1_0_12.realAnswer).add hm12_0_1_12.realAnswer).scale (1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 12 (1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_1_0_12.realContains hm12_0_1_12.realContains) (1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -4347157169218591395576, hi := -4347157169218274979164}
lemma t11_checked : ((hm12_1_0_13.realAnswer).add hm12_0_1_13.realAnswer).scale (1) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 12 (1/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_1_0_13.realContains hm12_0_1_13.realContains) (1) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -171396147550665061348791, hi := 171396147550665061348791}
lemma t12_contains : t12.Contains (sourcePower true 12 (1/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (1/2) 2 12 coarse_12_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -20540279013060288964123, hi := 20540279013060288964123}
lemma t13_contains : t13.Contains (sourcePower true 12 (1/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (1/2) 2 13 coarse_12_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -2370812092565497112264, hi := 2370812092565497112264}
lemma t14_contains : t14.Contains (sourcePower true 12 (1/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (1/2) 2 14 coarse_12_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -263953881363605769697, hi := 263953881363605769697}
lemma t15_contains : t15.Contains (sourcePower true 12 (1/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (1/2) 2 15 coarse_12_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -28365989397522196385, hi := 28365989397522196385}
lemma t16_contains : t16.Contains (sourcePower true 12 (1/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (1/2) 2 16 coarse_12_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -2943072604808163227, hi := 2943072604808163227}
lemma t17_contains : t17.Contains (sourcePower true 12 (1/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (1/2) 2 17 coarse_12_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -294818953479539848, hi := 294818953479539848}
lemma t18_contains : t18.Contains (sourcePower true 12 (1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (1/2) 2 18 coarse_12_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -28516436648066880, hi := 28516436648066880}
lemma t19_contains : t19.Contains (sourcePower true 12 (1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (1/2) 2 19 coarse_12_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -2663938389153873, hi := 2663938389153873}
lemma t20_contains : t20.Contains (sourcePower true 12 (1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (1/2) 2 20 coarse_12_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -240457452818595, hi := 240457452818595}
lemma t21_contains : t21.Contains (sourcePower true 12 (1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (1/2) 2 21 coarse_12_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -20985905895579, hi := 20985905895579}
lemma t22_contains : t22.Contains (sourcePower true 12 (1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (1/2) 2 22 coarse_12_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -1772419477128, hi := 1772419477128}
lemma t23_contains : t23.Contains (sourcePower true 12 (1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (1/2) 2 23 coarse_12_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -145009275090, hi := 145009275090}
lemma t24_contains : t24.Contains (sourcePower true 12 (1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (1/2) 2 24 coarse_12_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -11505508624, hi := 11505508624}
lemma t25_contains : t25.Contains (sourcePower true 12 (1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (1/2) 2 25 coarse_12_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -886376938, hi := 886376938}
lemma t26_contains : t26.Contains (sourcePower true 12 (1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (1/2) 2 26 coarse_12_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -66385150, hi := 66385150}
lemma t27_contains : t27.Contains (sourcePower true 12 (1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (1/2) 2 27 coarse_12_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -4839517, hi := 4839517}
lemma t28_contains : t28.Contains (sourcePower true 12 (1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (1/2) 2 28 coarse_12_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 12 (1/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (1/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 61451870782754334557887457376, hi := 61451870782926870143619619324}
lemma t0_checked : ((hm12_0_0_2.realAnswer).add hm12_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 12 (-3/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_0_0_2.realContains hm12_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 205178031696981519097267862259, hi := 205178031697181508741523160691}
lemma t1_checked : ((hm12_0_0_3.realAnswer).add hm12_1_1_3.realAnswer).scale (3) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 12 (-3/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_0_0_3.realContains hm12_1_1_3.realContains) (3) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := 138161970335826072124715558198, hi := 138161970336002369894236566372}
lemma t2_checked : ((hm12_0_0_4.realAnswer).add hm12_1_1_4.realAnswer).scale (-9) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 12 (-3/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_0_0_4.realContains hm12_1_1_4.realContains) (-9) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -162518927082370702380414367864, hi := -162518927082245616259477333704}
lemma t3_checked : ((hm12_0_0_5.realAnswer).add hm12_1_1_5.realAnswer).scale (27) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 12 (-3/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_0_0_5.realContains hm12_1_1_5.realContains) (27) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := -178805063809430992100545895936, hi := -178805063809356782873393901049}
lemma t4_checked : ((hm12_0_0_6.realAnswer).add hm12_1_1_6.realAnswer).scale (-81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 12 (-3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_0_0_6.realContains hm12_1_1_6.realContains) (-81) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 41845071135833034145133820814, hi := 41845071135870865147409400635}
lemma t5_checked : ((hm12_0_0_7.realAnswer).add hm12_1_1_7.realAnswer).scale (243) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 12 (-3/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_0_0_7.realContains hm12_1_1_7.realContains) (243) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := 83358506816283278389814666047, hi := 83358506816300192241911307787}
lemma t6_checked : ((hm12_0_0_8.realAnswer).add hm12_1_1_8.realAnswer).scale (-729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 12 (-3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_0_0_8.realContains hm12_1_1_8.realContains) (-729) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -71073030024369763248884216, hi := -71073030017631863712068397}
lemma t7_checked : ((hm12_0_0_9.realAnswer).add hm12_1_1_9.realAnswer).scale (2187) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 12 (-3/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_0_0_9.realContains hm12_1_1_9.realContains) (2187) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := -21264717546532706095461944382, hi := -21264717546530283726339066935}
lemma t8_checked : ((hm12_0_0_10.realAnswer).add hm12_1_1_10.realAnswer).scale (-6561) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 12 (-3/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_0_0_10.realContains hm12_1_1_10.realContains) (-6561) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := -2414277255932790321504152666, hi := -2414277255931995893594107343}
lemma t9_checked : ((hm12_0_0_11.realAnswer).add hm12_1_1_11.realAnswer).scale (19683) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 12 (-3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_0_0_11.realContains hm12_1_1_11.realContains) (19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := 3401290107919635471111871538, hi := 3401290107919875425279358509}
lemma t10_checked : ((hm12_0_0_12.realAnswer).add hm12_1_1_12.realAnswer).scale (-59049) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 12 (-3/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_0_0_12.realContains hm12_1_1_12.realContains) (-59049) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := 678496184099645750694136736, hi := 678496184099713133822869926}
lemma t11_checked : ((hm12_0_0_13.realAnswer).add hm12_1_1_13.realAnswer).scale (177147) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 12 (-3/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_0_0_13.realContains hm12_1_1_13.realContains) (177147) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -91086940050472990868262756351, hi := 91086940050472990868262756351}
lemma t12_contains : t12.Contains (sourcePower false 12 (-3/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (-3/2) 2 12 coarse_12_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -32747839256939319082147225590, hi := 32747839256939319082147225590}
lemma t13_contains : t13.Contains (sourcePower false 12 (-3/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (-3/2) 2 13 coarse_12_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -11339520743565903157545117223, hi := 11339520743565903157545117223}
lemma t14_contains : t14.Contains (sourcePower false 12 (-3/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (-3/2) 2 14 coarse_12_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -3787449695975412374043620960, hi := 3787449695975412374043620960}
lemma t15_contains : t15.Contains (sourcePower false 12 (-3/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (-3/2) 2 15 coarse_12_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -1221062831484096079059057587, hi := 1221062831484096079059057587}
lemma t16_contains : t16.Contains (sourcePower false 12 (-3/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (-3/2) 2 16 coarse_12_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -380068875905760782769548654, hi := 380068875905760782769548654}
lemma t17_contains : t17.Contains (sourcePower false 12 (-3/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (-3/2) 2 17 coarse_12_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -114218903123511579077843282, hi := 114218903123511579077843282}
lemma t18_contains : t18.Contains (sourcePower false 12 (-3/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (-3/2) 2 18 coarse_12_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -33143555492194773979714580, hi := 33143555492194773979714580}
lemma t19_contains : t19.Contains (sourcePower false 12 (-3/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (-3/2) 2 19 coarse_12_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -9288578820526788622989364, hi := 9288578820526788622989364}
lemma t20_contains : t20.Contains (sourcePower false 12 (-3/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (-3/2) 2 20 coarse_12_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -2515269886776208955260010, hi := 2515269886776208955260010}
lemma t21_contains : t21.Contains (sourcePower false 12 (-3/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (-3/2) 2 21 coarse_12_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -658559963858000548233917, hi := 658559963858000548233917}
lemma t22_contains : t22.Contains (sourcePower false 12 (-3/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (-3/2) 2 22 coarse_12_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -166861203791677917241811, hi := 166861203791677917241811}
lemma t23_contains : t23.Contains (sourcePower false 12 (-3/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (-3/2) 2 23 coarse_12_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -40954902349054626329048, hi := 40954902349054626329048}
lemma t24_contains : t24.Contains (sourcePower false 12 (-3/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (-3/2) 2 24 coarse_12_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -9748486402679208977336, hi := 9748486402679208977336}
lemma t25_contains : t25.Contains (sourcePower false 12 (-3/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (-3/2) 2 25 coarse_12_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -2253051248616112321678, hi := 2253051248616112321678}
lemma t26_contains : t26.Contains (sourcePower false 12 (-3/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (-3/2) 2 26 coarse_12_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -506226427008888682575, hi := 506226427008888682575}
lemma t27_contains : t27.Contains (sourcePower false 12 (-3/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (-3/2) 2 27 coarse_12_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -110712622742236369478, hi := 110712622742236369478}
lemma t28_contains : t28.Contains (sourcePower false 12 (-3/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 12 (-3/2) 2 28 coarse_12_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 12 (-3/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 12 (-3/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 57107874017072128817429474713, hi := 57107874017213800199224982736}
lemma t0_checked : ((hm12_1_0_2.realAnswer).add hm12_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 12 (-3/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_1_0_2.realContains hm12_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 192307945915562840104410268524, hi := 192307945915727047145402602749}
lemma t1_checked : ((hm12_1_0_3.realAnswer).add hm12_0_1_3.realAnswer).scale (-3) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 12 (-3/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_1_0_3.realContains hm12_0_1_3.realContains) (-3) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := 133937077158603429279301638906, hi := 133937077158748190084181936993}
lemma t2_checked : ((hm12_1_0_4.realAnswer).add hm12_0_1_4.realAnswer).scale (9) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 12 (-3/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_1_0_4.realContains hm12_0_1_4.realContains) (9) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -147200619180231319336594216719, hi := -147200619180128599493895095383}
lemma t3_checked : ((hm12_1_0_5.realAnswer).add hm12_0_1_5.realAnswer).scale (-27) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 12 (-3/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_1_0_5.realContains hm12_0_1_5.realContains) (-27) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := -170716880058569681456544825004, hi := -170716880058508732567507869597}
lemma t4_checked : ((hm12_1_0_6.realAnswer).add hm12_0_1_6.realAnswer).scale (81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 12 (-3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_1_0_6.realContains hm12_0_1_6.realContains) (81) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 33670177281767702197998047337, hi := 33670177281798780123417100315}
lemma t5_checked : ((hm12_1_0_7.realAnswer).add hm12_0_1_7.realAnswer).scale (-243) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 12 (-3/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_1_0_7.realContains hm12_0_1_7.realContains) (-243) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := 78734696003978297625381685420, hi := 78734696003992197218497190068}
lemma t6_checked : ((hm12_1_0_8.realAnswer).add hm12_0_1_8.realAnswer).scale (729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 12 (-3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_1_0_8.realContains hm12_0_1_8.realContains) (729) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 2555489668113909381546624582, hi := 2555489668119449829809098293}
lemma t7_checked : ((hm12_1_0_9.realAnswer).add hm12_0_1_9.realAnswer).scale (-2187) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 12 (-3/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_1_0_9.realContains hm12_0_1_9.realContains) (-2187) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := -19808604575526106524123963469, hi := -19808604575524112593764077504}
lemma t8_checked : ((hm12_1_0_10.realAnswer).add hm12_0_1_10.realAnswer).scale (6561) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 12 (-3/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_1_0_10.realContains hm12_0_1_10.realContains) (6561) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := -2988966136543382849332127188, hi := -2988966136542727749283831868}
lemma t9_checked : ((hm12_1_0_11.realAnswer).add hm12_0_1_11.realAnswer).scale (-19683) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 12 (-3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_1_0_11.realContains hm12_0_1_11.realContains) (-19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := 3101946970554742713082281773, hi := 3101946970554941211018878432}
lemma t10_checked : ((hm12_1_0_12.realAnswer).add hm12_0_1_12.realAnswer).scale (59049) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 12 (-3/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_1_0_12.realContains hm12_0_1_12.realContains) (59049) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := 770085851055509757734031624, hi := 770085851055565809952062230}
lemma t11_checked : ((hm12_1_0_13.realAnswer).add hm12_0_1_13.realAnswer).scale (-177147) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 12 (-3/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm12_1_0_13.realContains hm12_0_1_13.realContains) (-177147) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -91086940050472990868262756351, hi := 91086940050472990868262756351}
lemma t12_contains : t12.Contains (sourcePower true 12 (-3/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (-3/2) 2 12 coarse_12_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -32747839256939319082147225590, hi := 32747839256939319082147225590}
lemma t13_contains : t13.Contains (sourcePower true 12 (-3/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (-3/2) 2 13 coarse_12_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -11339520743565903157545117223, hi := 11339520743565903157545117223}
lemma t14_contains : t14.Contains (sourcePower true 12 (-3/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (-3/2) 2 14 coarse_12_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -3787449695975412374043620960, hi := 3787449695975412374043620960}
lemma t15_contains : t15.Contains (sourcePower true 12 (-3/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (-3/2) 2 15 coarse_12_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -1221062831484096079059057587, hi := 1221062831484096079059057587}
lemma t16_contains : t16.Contains (sourcePower true 12 (-3/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (-3/2) 2 16 coarse_12_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -380068875905760782769548654, hi := 380068875905760782769548654}
lemma t17_contains : t17.Contains (sourcePower true 12 (-3/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (-3/2) 2 17 coarse_12_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -114218903123511579077843282, hi := 114218903123511579077843282}
lemma t18_contains : t18.Contains (sourcePower true 12 (-3/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (-3/2) 2 18 coarse_12_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -33143555492194773979714580, hi := 33143555492194773979714580}
lemma t19_contains : t19.Contains (sourcePower true 12 (-3/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (-3/2) 2 19 coarse_12_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -9288578820526788622989364, hi := 9288578820526788622989364}
lemma t20_contains : t20.Contains (sourcePower true 12 (-3/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (-3/2) 2 20 coarse_12_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -2515269886776208955260010, hi := 2515269886776208955260010}
lemma t21_contains : t21.Contains (sourcePower true 12 (-3/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (-3/2) 2 21 coarse_12_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -658559963858000548233917, hi := 658559963858000548233917}
lemma t22_contains : t22.Contains (sourcePower true 12 (-3/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (-3/2) 2 22 coarse_12_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -166861203791677917241811, hi := 166861203791677917241811}
lemma t23_contains : t23.Contains (sourcePower true 12 (-3/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (-3/2) 2 23 coarse_12_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -40954902349054626329048, hi := 40954902349054626329048}
lemma t24_contains : t24.Contains (sourcePower true 12 (-3/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (-3/2) 2 24 coarse_12_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -9748486402679208977336, hi := 9748486402679208977336}
lemma t25_contains : t25.Contains (sourcePower true 12 (-3/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (-3/2) 2 25 coarse_12_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -2253051248616112321678, hi := 2253051248616112321678}
lemma t26_contains : t26.Contains (sourcePower true 12 (-3/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (-3/2) 2 26 coarse_12_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -506226427008888682575, hi := 506226427008888682575}
lemma t27_contains : t27.Contains (sourcePower true 12 (-3/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (-3/2) 2 27 coarse_12_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -110712622742236369478, hi := 110712622742236369478}
lemma t28_contains : t28.Contains (sourcePower true 12 (-3/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 12 (-3/2) 2 28 coarse_12_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 12 (-3/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 12 (-3/2) 2) k.val := by
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
end SharpPlanar.Bernstein12

end OAI
