import OAI.Analysis.PlanarPacking.Certificate.LowBlock36_0
import OAI.Analysis.PlanarPacking.Certificate.LowBlock36_1
import OAI.Analysis.PlanarPacking.Certificate.LowBlock36_10
import OAI.Analysis.PlanarPacking.Certificate.MixedBound36
import OAI.Analysis.PlanarPacking.Certificate.CoarseBound36

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein36
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 52426170716289159934331211820, hi := 52426170716481916365157812188}
lemma t0_checked : ((hm36_0_0_2.realAnswer).add hm36_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 36 (1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_0_0_2.realContains hm36_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -55581467500208741724445772633, hi := -55581467500134756147820649715}
lemma t1_checked : ((hm36_0_0_3.realAnswer).add hm36_1_1_3.realAnswer).scale (-1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 36 (1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_0_0_3.realContains hm36_1_1_3.realContains) (-1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := 9997482414171668750067763525, hi := 9997482414193349447334937333}
lemma t2_checked : ((hm36_0_0_4.realAnswer).add hm36_1_1_4.realAnswer).scale (-1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 36 (1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_0_0_4.realContains hm36_1_1_4.realContains) (-1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 5820263902555906938481700804, hi := 5820263902561028643674973696}
lemma t3_checked : ((hm36_0_0_5.realAnswer).add hm36_1_1_5.realAnswer).scale (-1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 36 (1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_0_0_5.realContains hm36_1_1_5.realContains) (-1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr4 : RBox := {lo := -1797366677298254339026286668, hi := 1797366677298254339026286668}
lemma tr4_contains : tr4.Contains (fullMoment true true 36 6) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 6 36 mixed_36_6) <;> norm_num [tr4,precision]
noncomputable def t4 : RBox := {lo := -1690572071041722764824134520, hi := -1465901236378428577093212980}
lemma t4_checked : ((hm36_0_0_6.realAnswer).add tr4).scale (-1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 36 (1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_0_0_6.realContains tr4_contains) (-1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr5 : RBox := {lo := -1054748594041481953701852891, hi := 1054748594041481953701852891}
lemma tr5_contains : tr5.Contains (fullMoment true true 36 7) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 7 36 mixed_36_7) <;> norm_num [tr5,precision]
noncomputable def t5 : RBox := {lo := -288345560368785275787074630, hi := -222423773241020638464269611}
lemma t5_checked : ((hm36_0_0_7.realAnswer).add tr5).scale (-1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 36 (1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_0_0_7.realContains tr5_contains) (-1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr6 : RBox := {lo := -542205561747256519505331368, hi := 542205561747256519505331368}
lemma tr6_contains : tr6.Contains (fullMoment true true 36 8) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 8 36 mixed_36_8) <;> norm_num [tr6,precision]
noncomputable def t6 : RBox := {lo := 78505306548487620666794207, hi := 95449230353115021161421130}
lemma t6_checked : ((hm36_0_0_8.realAnswer).add tr6).scale (-1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 36 (1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_0_0_8.realContains tr6_contains) (-1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr7 : RBox := {lo := -248007659112966961373842623, hi := 248007659112966961373842623}
lemma tr7_contains : tr7.Contains (fullMoment true true 36 9) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 9 36 mixed_36_9) <;> norm_num [tr7,precision]
noncomputable def t7 : RBox := {lo := 4325629047989256110644267, hi := 8200748721632768003775457}
lemma t7_checked : ((hm36_0_0_9.realAnswer).add tr7).scale (-1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 36 (1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_0_0_9.realContains tr7_contains) (-1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -102187287443684063655955502, hi := 102187287443684063655955502}
lemma tr8_contains : tr8.Contains (fullMoment true true 36 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 10 36 mixed_36_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := -3063469735856202019372389, hi := -2265131552702012794156543}
lemma t8_checked : ((hm36_0_0_10.realAnswer).add tr8).scale (-1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 36 (1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_0_0_10.realContains tr8_contains) (-1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -38307059161154352730149430, hi := 38307059161154352730149430}
lemma tr9_contains : tr9.Contains (fullMoment true true 36 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 11 36 mixed_36_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -172742991348237789749619, hi := -23106041499934151029172}
lemma t9_checked : ((hm36_0_0_11.realAnswer).add tr9).scale (-1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 36 (1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_0_0_11.realContains tr9_contains) (-1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -13172692487444001619504985, hi := 13172692487444001619504985}
lemma tr10_contains : tr10.Contains (fullMoment true true 36 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 12 36 mixed_36_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := 40235275232920764615564, hi := 65963190247464284204049}
lemma t10_checked : ((hm36_0_0_12.realAnswer).add tr10).scale (-1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 36 (1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_0_0_12.realContains tr10_contains) (-1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -4183834238406027061996438, hi := 4183834238406027061996438}
lemma tr11_contains : tr11.Contains (fullMoment true true 36 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 13 36 mixed_36_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := -990636605535078486950, hi := 3095139017908720217424}
lemma t11_checked : ((hm36_0_0_13.realAnswer).add tr11).scale (-1) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 36 (1/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_0_0_13.realContains tr11_contains) (-1) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -88050869421777572522194, hi := 88050869421777572522194}
lemma t12_contains : t12.Contains (sourcePower false 36 (1/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (1/2) 2 12 coarse_36_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -8947333922685233817253, hi := 8947333922685233817253}
lemma t13_contains : t13.Contains (sourcePower false 36 (1/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (1/2) 2 13 coarse_36_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -857029939340576458208, hi := 857029939340576458208}
lemma t14_contains : t14.Contains (sourcePower false 36 (1/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (1/2) 2 14 coarse_36_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -77632643843105102825, hi := 77632643843105102825}
lemma t15_contains : t15.Contains (sourcePower false 36 (1/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (1/2) 2 15 coarse_36_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -6669954225551631815, hi := 6669954225551631815}
lemma t16_contains : t16.Contains (sourcePower false 36 (1/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (1/2) 2 16 coarse_36_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -545032650142071095, hi := 545032650142071095}
lemma t17_contains : t17.Contains (sourcePower false 36 (1/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (1/2) 2 17 coarse_36_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -42468327468036483, hi := 42468327468036483}
lemma t18_contains : t18.Contains (sourcePower false 36 (1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (1/2) 2 18 coarse_36_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -3163188611309559, hi := 3163188611309559}
lemma t19_contains : t19.Contains (sourcePower false 36 (1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (1/2) 2 19 coarse_36_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -225761628138761, hi := 225761628138761}
lemma t20_contains : t20.Contains (sourcePower false 36 (1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (1/2) 2 20 coarse_36_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -15476837523320, hi := 15476837523320}
lemma t21_contains : t21.Contains (sourcePower false 36 (1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (1/2) 2 21 coarse_36_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -1021592911047, hi := 1021592911047}
lemma t22_contains : t22.Contains (sourcePower false 36 (1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (1/2) 2 22 coarse_36_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -65092026637, hi := 65092026637}
lemma t23_contains : t23.Contains (sourcePower false 36 (1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (1/2) 2 23 coarse_36_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -4013972563, hi := 4013972563}
lemma t24_contains : t24.Contains (sourcePower false 36 (1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (1/2) 2 24 coarse_36_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -240228394, hi := 240228394}
lemma t25_contains : t25.Contains (sourcePower false 36 (1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (1/2) 2 25 coarse_36_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -13994330, hi := 13994330}
lemma t26_contains : t26.Contains (sourcePower false 36 (1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (1/2) 2 26 coarse_36_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -795957, hi := 795957}
lemma t27_contains : t27.Contains (sourcePower false 36 (1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (1/2) 2 27 coarse_36_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -44340, hi := 44340}
lemma t28_contains : t28.Contains (sourcePower false 36 (1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (1/2) 2 28 coarse_36_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 36 (1/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (1/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 55576760806685359727950294215, hi := 55576760806833877625784852719}
lemma t0_checked : ((hm36_1_0_2.realAnswer).add hm36_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 36 (1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_1_0_2.realContains hm36_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -58795876162262332422903458726, hi := -58795876162205007933275776527}
lemma t1_checked : ((hm36_1_0_3.realAnswer).add hm36_0_1_3.realAnswer).scale (1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 36 (1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_1_0_3.realContains hm36_0_1_3.realContains) (1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := 10464075089447804768444857775, hi := 10464075089464641100825115616}
lemma t2_checked : ((hm36_1_0_4.realAnswer).add hm36_0_1_4.realAnswer).scale (1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 36 (1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_1_0_4.realContains hm36_0_1_4.realContains) (1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 6194872543394980673083087183, hi := 6194872543398961614002693623}
lemma t3_checked : ((hm36_1_0_5.realAnswer).add hm36_0_1_5.realAnswer).scale (1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 36 (1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_1_0_5.realContains hm36_0_1_5.realContains) (1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr4 : RBox := {lo := -1797366677298254339026286668, hi := 1797366677298254339026286668}
lemma tr4_contains : tr4.Contains (fullMoment false true 36 6) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 6 36 mixed_36_6) <;> norm_num [tr4,precision]
noncomputable def t4 : RBox := {lo := -1772573321117334816270061366, hi := -1547902486454265894915494309}
lemma t4_checked : ((hm36_1_0_6.realAnswer).add tr4).scale (1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 36 (1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_1_0_6.realContains tr4_contains) (1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr5 : RBox := {lo := -1054748594041481953701852891, hi := 1054748594041481953701852891}
lemma tr5_contains : tr5.Contains (fullMoment false true 36 7) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 7 36 mixed_36_7) <;> norm_num [tr5,precision]
noncomputable def t5 : RBox := {lo := -307290205088959007857801753, hi := -241368417961232647976646243}
lemma t5_checked : ((hm36_1_0_7.realAnswer).add tr5).scale (1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 36 (1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_1_0_7.realContains tr5_contains) (1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr6 : RBox := {lo := -542205561747256519505331368, hi := 542205561747256519505331368}
lemma tr6_contains : tr6.Contains (fullMoment false true 36 8) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 8 36 mixed_36_8) <;> norm_num [tr6,precision]
noncomputable def t6 : RBox := {lo := 83193150443962139632666557, hi := 100137074248583831225195686}
lemma t6_checked : ((hm36_1_0_8.realAnswer).add tr6).scale (1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 36 (1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_1_0_8.realContains tr6_contains) (1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr7 : RBox := {lo := -248007659112966961373842623, hi := 248007659112966961373842623}
lemma tr7_contains : tr7.Contains (fullMoment false true 36 9) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 9 36 mixed_36_9) <;> norm_num [tr7,precision]
noncomputable def t7 : RBox := {lo := 4902354393540312354597746, hi := 8777474067183065274325582}
lemma t7_checked : ((hm36_1_0_9.realAnswer).add tr7).scale (1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 36 (1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_1_0_9.realContains tr7_contains) (1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -102187287443684063655955502, hi := 102187287443684063655955502}
lemma tr8_contains : tr8.Contains (fullMoment false true 36 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 10 36 mixed_36_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := -3211433092753347532357987, hi := -2413094909599249362638948}
lemma t8_checked : ((hm36_1_0_10.realAnswer).add tr8).scale (1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 36 (1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_1_0_10.realContains tr8_contains) (1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -38307059161154352730149430, hi := 38307059161154352730149430}
lemma tr9_contains : tr9.Contains (fullMoment false true 36 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 11 36 mixed_36_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -184774507636044784902388, hi := -35137557787751103377189}
lemma t9_checked : ((hm36_1_0_11.realAnswer).add tr9).scale (1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 36 (1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_1_0_11.realContains tr9_contains) (1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -13172692487444001619504985, hi := 13172692487444001619504985}
lemma tr10_contains : tr10.Contains (fullMoment false true 36 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 12 36 mixed_36_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := 43265304187579719615676, hi := 68993219202122238472647}
lemma t10_checked : ((hm36_1_0_12.realAnswer).add tr10).scale (1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 36 (1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_1_0_12.realContains tr10_contains) (1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -4183834238406027061996438, hi := 4183834238406027061996438}
lemma tr11_contains : tr11.Contains (fullMoment false true 36 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 13 36 mixed_36_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := -805051455784256284190, hi := 3280724167659449335755}
lemma t11_checked : ((hm36_1_0_13.realAnswer).add tr11).scale (1) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 36 (1/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_1_0_13.realContains tr11_contains) (1) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -88050869421777572522194, hi := 88050869421777572522194}
lemma t12_contains : t12.Contains (sourcePower true 36 (1/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (1/2) 2 12 coarse_36_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -8947333922685233817253, hi := 8947333922685233817253}
lemma t13_contains : t13.Contains (sourcePower true 36 (1/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (1/2) 2 13 coarse_36_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -857029939340576458208, hi := 857029939340576458208}
lemma t14_contains : t14.Contains (sourcePower true 36 (1/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (1/2) 2 14 coarse_36_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -77632643843105102825, hi := 77632643843105102825}
lemma t15_contains : t15.Contains (sourcePower true 36 (1/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (1/2) 2 15 coarse_36_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -6669954225551631815, hi := 6669954225551631815}
lemma t16_contains : t16.Contains (sourcePower true 36 (1/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (1/2) 2 16 coarse_36_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -545032650142071095, hi := 545032650142071095}
lemma t17_contains : t17.Contains (sourcePower true 36 (1/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (1/2) 2 17 coarse_36_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -42468327468036483, hi := 42468327468036483}
lemma t18_contains : t18.Contains (sourcePower true 36 (1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (1/2) 2 18 coarse_36_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -3163188611309559, hi := 3163188611309559}
lemma t19_contains : t19.Contains (sourcePower true 36 (1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (1/2) 2 19 coarse_36_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -225761628138761, hi := 225761628138761}
lemma t20_contains : t20.Contains (sourcePower true 36 (1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (1/2) 2 20 coarse_36_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -15476837523320, hi := 15476837523320}
lemma t21_contains : t21.Contains (sourcePower true 36 (1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (1/2) 2 21 coarse_36_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -1021592911047, hi := 1021592911047}
lemma t22_contains : t22.Contains (sourcePower true 36 (1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (1/2) 2 22 coarse_36_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -65092026637, hi := 65092026637}
lemma t23_contains : t23.Contains (sourcePower true 36 (1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (1/2) 2 23 coarse_36_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -4013972563, hi := 4013972563}
lemma t24_contains : t24.Contains (sourcePower true 36 (1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (1/2) 2 24 coarse_36_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -240228394, hi := 240228394}
lemma t25_contains : t25.Contains (sourcePower true 36 (1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (1/2) 2 25 coarse_36_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -13994330, hi := 13994330}
lemma t26_contains : t26.Contains (sourcePower true 36 (1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (1/2) 2 26 coarse_36_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -795957, hi := 795957}
lemma t27_contains : t27.Contains (sourcePower true 36 (1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (1/2) 2 27 coarse_36_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -44340, hi := 44340}
lemma t28_contains : t28.Contains (sourcePower true 36 (1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (1/2) 2 28 coarse_36_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 36 (1/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 52426170716289159934331211820, hi := 52426170716481916365157812188}
lemma t0_checked : ((hm36_0_0_2.realAnswer).add hm36_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 36 (-3/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_0_0_2.realContains hm36_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 166744402500404268443461949145, hi := 166744402500626225173337317898}
lemma t1_checked : ((hm36_0_0_3.realAnswer).add hm36_1_1_3.realAnswer).scale (3) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 36 (-3/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_0_0_3.realContains hm36_1_1_3.realContains) (3) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := 89977341727545018750609871729, hi := 89977341727740145026014435995}
lemma t2_checked : ((hm36_0_0_4.realAnswer).add hm36_1_1_4.realAnswer).scale (-9) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 36 (-3/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_0_0_4.realContains hm36_1_1_4.realContains) (-9) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -157147125369147773379224289782, hi := -157147125369009487339005921711}
lemma t3_checked : ((hm36_0_0_5.realAnswer).add hm36_1_1_5.realAnswer).scale (27) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 36 (-3/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_0_0_5.realContains hm36_1_1_5.realContains) (27) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr4 : RBox := {lo := -1797366677298254339026286668, hi := 1797366677298254339026286668}
lemma tr4_contains : tr4.Contains (fullMoment true true 36 6) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 6 36 mixed_36_6) <;> norm_num [tr4,precision]
noncomputable def t4 : RBox := {lo := -136936337754379543950754896095, hi := -118738000146652714744550251425}
lemma t4_checked : ((hm36_0_0_6.realAnswer).add tr4).scale (-81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 36 (-3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_0_0_6.realContains tr4_contains) (-81) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr5 : RBox := {lo := -1054748594041481953701852891, hi := 1054748594041481953701852891}
lemma tr5_contains : tr5.Contains (fullMoment true true 36 7) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 7 36 mixed_36_7) <;> norm_num [tr5,precision]
noncomputable def t5 : RBox := {lo := 54048976897568015146817515662, hi := 70067971169614822016259135007}
lemma t5_checked : ((hm36_0_0_7.realAnswer).add tr5).scale (243) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 36 (-3/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_0_0_7.realContains tr5_contains) (243) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr6 : RBox := {lo := -542205561747256519505331368, hi := 542205561747256519505331368}
lemma tr6_contains : tr6.Contains (fullMoment true true 36 8) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 8 36 mixed_36_8) <;> norm_num [tr6,precision]
noncomputable def t6 : RBox := {lo := 57230368473847475466092977483, hi := 69582488927420850426676003087}
lemma t6_checked : ((hm36_0_0_8.realAnswer).add tr6).scale (-729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 36 (-3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_0_0_8.realContains tr6_contains) (-729) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr7 : RBox := {lo := -248007659112966961373842623, hi := 248007659112966961373842623}
lemma tr7_contains : tr7.Contains (fullMoment true true 36 9) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 9 36 mixed_36_9) <;> norm_num [tr7,precision]
noncomputable def t7 : RBox := {lo := -17935037454210863624256922768, hi := -9460150727952503113979012766}
lemma t7_checked : ((hm36_0_0_9.realAnswer).add tr7).scale (2187) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 36 (-3/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_0_0_9.realContains tr7_contains) (2187) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -102187287443684063655955502, hi := 102187287443684063655955502}
lemma tr8_contains : tr8.Contains (fullMoment true true 36 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 10 36 mixed_36_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := -20099424936952541449102238719, hi := -14861528117277905942461085107}
lemma t8_checked : ((hm36_0_0_10.realAnswer).add tr8).scale (-6561) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 36 (-3/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_0_0_10.realContains tr8_contains) (-6561) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -38307059161154352730149430, hi := 38307059161154352730149430}
lemma tr9_contains : tr9.Contains (fullMoment true true 36 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 11 36 mixed_36_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := 454796214843203894707208968, hi := 3400100298707364415641750239}
lemma t9_checked : ((hm36_0_0_11.realAnswer).add tr9).scale (19683) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 36 (-3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_0_0_11.realContains tr9_contains) (19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -13172692487444001619504985, hi := 13172692487444001619504985}
lemma tr10_contains : tr10.Contains (fullMoment true true 36 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 12 36 mixed_36_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := 2375852767228738229784497166, hi := 3895060420922518517964871756}
lemma t10_checked : ((hm36_0_0_12.realAnswer).add tr10).scale (-59049) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 36 (-3/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_0_0_12.realContains tr10_contains) (-59049) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -4183834238406027061996438, hi := 4183834238406027061996438}
lemma tr11_contains : tr11.Contains (fullMoment true true 36 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 13 36 mixed_36_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := -548294591605476060355929664, hi := 175488302760722548727584951}
lemma t11_checked : ((hm36_0_0_13.realAnswer).add tr11).scale (177147) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 36 (-3/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_0_0_13.realContains tr11_contains) (177147) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -46793842096378894918766913353, hi := 46793842096378894918766913353}
lemma t12_contains : t12.Contains (sourcePower false 36 (-3/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (-3/2) 2 12 coarse_36_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -14264940261617290035222848399, hi := 14264940261617290035222848399}
lemma t13_contains : t13.Contains (sourcePower false 36 (-3/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (-3/2) 2 13 coarse_36_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -4099147631937857641734979784, hi := 4099147631937857641734979784}
lemma t14_contains : t14.Contains (sourcePower false 36 (-3/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (-3/2) 2 14 coarse_36_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -1113943586668837711657210604, hi := 1113943586668837711657210604}
lemma t15_contains : t15.Contains (sourcePower false 36 (-3/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (-3/2) 2 15 coarse_36_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -287119658630092165815552628, hi := 287119658630092165815552628}
lemma t16_contains : t16.Contains (sourcePower false 36 (-3/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (-3/2) 2 16 coarse_36_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -70385605279669034351869203, hi := 70385605279669034351869203}
lemma t17_contains : t17.Contains (sourcePower false 36 (-3/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (-3/2) 2 17 coarse_36_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -16453100194678825906419940, hi := 16453100194678825906419940}
lemma t18_contains : t18.Contains (sourcePower false 36 (-3/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (-3/2) 2 18 coarse_36_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -3676452235778340063267296, hi := 3676452235778340063267296}
lemma t19_contains : t19.Contains (sourcePower false 36 (-3/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (-3/2) 2 19 coarse_36_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -787182123338594070900422, hi := 787182123338594070900422}
lemma t20_contains : t20.Contains (sourcePower false 36 (-3/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (-3/2) 2 20 coarse_36_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -161893186959370361506375, hi := 161893186959370361506375}
lemma t21_contains : t21.Contains (sourcePower false 36 (-3/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (-3/2) 2 21 coarse_36_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -32058668037672876068172, hi := 32058668037672876068172}
lemma t22_contains : t22.Contains (sourcePower false 36 (-3/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (-3/2) 2 22 coarse_36_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -6127970303894711358004, hi := 6127970303894711358004}
lemma t23_contains : t23.Contains (sourcePower false 36 (-3/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (-3/2) 2 23 coarse_36_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -1133664410226523058330, hi := 1133664410226523058330}
lemma t24_contains : t24.Contains (sourcePower false 36 (-3/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (-3/2) 2 24 coarse_36_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -203542781882395719468, hi := 203542781882395719468}
lemma t25_contains : t25.Contains (sourcePower false 36 (-3/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (-3/2) 2 25 coarse_36_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -35571707206776473197, hi := 35571707206776473197}
lemma t26_contains : t26.Contains (sourcePower false 36 (-3/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (-3/2) 2 26 coarse_36_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -6069644414832718076, hi := 6069644414832718076}
lemma t27_contains : t27.Contains (sourcePower false 36 (-3/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (-3/2) 2 27 coarse_36_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -1014355712285277065, hi := 1014355712285277065}
lemma t28_contains : t28.Contains (sourcePower false 36 (-3/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 36 (-3/2) 2 28 coarse_36_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 36 (-3/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 36 (-3/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 55576760806685359727950294215, hi := 55576760806833877625784852719}
lemma t0_checked : ((hm36_1_0_2.realAnswer).add hm36_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 36 (-3/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_1_0_2.realContains hm36_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 176387628486615023799827329582, hi := 176387628486786997268710376177}
lemma t1_checked : ((hm36_1_0_3.realAnswer).add hm36_0_1_3.realAnswer).scale (-3) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 36 (-3/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_1_0_3.realContains hm36_0_1_3.realContains) (-3) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := 94176675805030242916003719981, hi := 94176675805181769907426040542}
lemma t2_checked : ((hm36_1_0_4.realAnswer).add hm36_0_1_4.realAnswer).scale (9) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 36 (-3/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_1_0_4.realContains hm36_0_1_4.realContains) (9) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -167261558671771963578072727815, hi := -167261558671664478173243353961}
lemma t3_checked : ((hm36_1_0_5.realAnswer).add hm36_0_1_5.realAnswer).scale (-27) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 36 (-3/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_1_0_5.realContains hm36_0_1_5.realContains) (-27) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr4 : RBox := {lo := -1797366677298254339026286668, hi := 1797366677298254339026286668}
lemma tr4_contains : tr4.Contains (fullMoment false true 36 6) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 6 36 mixed_36_6) <;> norm_num [tr4,precision]
noncomputable def t4 : RBox := {lo := -143578439010504120117874970606, hi := -125380101402795537488155039079}
lemma t4_checked : ((hm36_1_0_6.realAnswer).add tr4).scale (81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 36 (-3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_1_0_6.realContains tr4_contains) (81) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr5 : RBox := {lo := -1054748594041481953701852891, hi := 1054748594041481953701852891}
lemma tr5_contains : tr5.Contains (fullMoment false true 36 7) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 7 36 mixed_36_7) <;> norm_num [tr5,precision]
noncomputable def t5 : RBox := {lo := 58652525564579533458325037124, hi := 74671519836617038909445825812}
lemma t5_checked : ((hm36_1_0_7.realAnswer).add tr5).scale (-243) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 36 (-3/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_1_0_7.realContains tr5_contains) (-243) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr6 : RBox := {lo := -542205561747256519505331368, hi := 542205561747256519505331368}
lemma tr6_contains : tr6.Contains (fullMoment false true 36 8) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 8 36 mixed_36_8) <;> norm_num [tr6,precision]
noncomputable def t6 : RBox := {lo := 60647806673648399792213920702, hi := 72999927127217612963167654878}
lemma t6_checked : ((hm36_1_0_8.realAnswer).add tr6).scale (729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 36 (-3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_1_0_8.realContains tr6_contains) (729) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr7 : RBox := {lo := -248007659112966961373842623, hi := 248007659112966961373842623}
lemma tr7_contains : tr7.Contains (fullMoment false true 36 9) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 9 36 mixed_36_9) <;> norm_num [tr7,precision]
noncomputable def t7 : RBox := {lo := -19196335784929363754950046468, hi := -10721449058672663119505272620}
lemma t7_checked : ((hm36_1_0_9.realAnswer).add tr7).scale (-2187) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 36 (-3/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_1_0_9.realContains tr7_contains) (-2187) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -102187287443684063655955502, hi := 102187287443684063655955502}
lemma tr8_contains : tr8.Contains (fullMoment false true 36 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 10 36 mixed_36_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := -21070212521554713159800750401, hi := -15832315701880675068274141902}
lemma t8_checked : ((hm36_1_0_10.realAnswer).add tr8).scale (6561) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 36 (-3/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_1_0_10.realContains tr8_contains) (6561) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -38307059161154352730149430, hi := 38307059161154352730149430}
lemma tr9_contains : tr9.Contains (fullMoment false true 36 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 11 36 mixed_36_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := 691612549936304967773212317, hi := 3636916633800269501233699314}
lemma t9_checked : ((hm36_1_0_11.realAnswer).add tr9).scale (-19683) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 36 (-3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_1_0_11.realContains tr9_contains) (-19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -13172692487444001619504985, hi := 13172692487444001619504985}
lemma tr10_contains : tr10.Contains (fullMoment false true 36 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 12 36 mixed_36_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := 2554772946972394863586059966, hi := 4073980600666116059571302718}
lemma t10_checked : ((hm36_1_0_12.realAnswer).add tr10).scale (59049) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 36 (-3/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_1_0_12.realContains tr10_contains) (59049) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -4183834238406027061996438, hi := 4183834238406027061996438}
lemma tr11_contains : tr11.Contains (fullMoment false true 36 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 13 36 mixed_36_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := -581170444128368471480832089, hi := 142612450237813647975334830}
lemma t11_checked : ((hm36_1_0_13.realAnswer).add tr11).scale (-177147) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 36 (-3/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm36_1_0_13.realContains tr11_contains) (-177147) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -46793842096378894918766913353, hi := 46793842096378894918766913353}
lemma t12_contains : t12.Contains (sourcePower true 36 (-3/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (-3/2) 2 12 coarse_36_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -14264940261617290035222848399, hi := 14264940261617290035222848399}
lemma t13_contains : t13.Contains (sourcePower true 36 (-3/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (-3/2) 2 13 coarse_36_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -4099147631937857641734979784, hi := 4099147631937857641734979784}
lemma t14_contains : t14.Contains (sourcePower true 36 (-3/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (-3/2) 2 14 coarse_36_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -1113943586668837711657210604, hi := 1113943586668837711657210604}
lemma t15_contains : t15.Contains (sourcePower true 36 (-3/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (-3/2) 2 15 coarse_36_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -287119658630092165815552628, hi := 287119658630092165815552628}
lemma t16_contains : t16.Contains (sourcePower true 36 (-3/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (-3/2) 2 16 coarse_36_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -70385605279669034351869203, hi := 70385605279669034351869203}
lemma t17_contains : t17.Contains (sourcePower true 36 (-3/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (-3/2) 2 17 coarse_36_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -16453100194678825906419940, hi := 16453100194678825906419940}
lemma t18_contains : t18.Contains (sourcePower true 36 (-3/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (-3/2) 2 18 coarse_36_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -3676452235778340063267296, hi := 3676452235778340063267296}
lemma t19_contains : t19.Contains (sourcePower true 36 (-3/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (-3/2) 2 19 coarse_36_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -787182123338594070900422, hi := 787182123338594070900422}
lemma t20_contains : t20.Contains (sourcePower true 36 (-3/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (-3/2) 2 20 coarse_36_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -161893186959370361506375, hi := 161893186959370361506375}
lemma t21_contains : t21.Contains (sourcePower true 36 (-3/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (-3/2) 2 21 coarse_36_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -32058668037672876068172, hi := 32058668037672876068172}
lemma t22_contains : t22.Contains (sourcePower true 36 (-3/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (-3/2) 2 22 coarse_36_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -6127970303894711358004, hi := 6127970303894711358004}
lemma t23_contains : t23.Contains (sourcePower true 36 (-3/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (-3/2) 2 23 coarse_36_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -1133664410226523058330, hi := 1133664410226523058330}
lemma t24_contains : t24.Contains (sourcePower true 36 (-3/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (-3/2) 2 24 coarse_36_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -203542781882395719468, hi := 203542781882395719468}
lemma t25_contains : t25.Contains (sourcePower true 36 (-3/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (-3/2) 2 25 coarse_36_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -35571707206776473197, hi := 35571707206776473197}
lemma t26_contains : t26.Contains (sourcePower true 36 (-3/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (-3/2) 2 26 coarse_36_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -6069644414832718076, hi := 6069644414832718076}
lemma t27_contains : t27.Contains (sourcePower true 36 (-3/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (-3/2) 2 27 coarse_36_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -1014355712285277065, hi := 1014355712285277065}
lemma t28_contains : t28.Contains (sourcePower true 36 (-3/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (-3/2) 2 28 coarse_36_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 36 (-3/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) k.val := by
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
end SharpPlanar.Bernstein36

end OAI
