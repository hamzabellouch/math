import OAI.Analysis.PlanarPacking.Certificate.LowBlock27_0
import OAI.Analysis.PlanarPacking.Certificate.LowBlock27_1
import OAI.Analysis.PlanarPacking.Certificate.LowBlock27_10
import OAI.Analysis.PlanarPacking.Certificate.LowBlock27_11
import OAI.Analysis.PlanarPacking.Certificate.MixedBound27
import OAI.Analysis.PlanarPacking.Certificate.CoarseBound27

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein27
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 28929288993229985313356265183, hi := 28929288993403452012686746439}
lemma t0_checked : ((hm27_0_0_2.realAnswer).add hm27_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 27 (1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_0_0_2.realContains hm27_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -12080982087626340009965678334, hi := -12080982087559345463646727088}
lemma t1_checked : ((hm27_0_0_3.realAnswer).add hm27_1_1_3.realAnswer).scale (-1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 27 (1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_0_0_3.realContains hm27_1_1_3.realContains) (-1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -9161000892551392829268707434, hi := -9161000892531711018759031544}
lemma t2_checked : ((hm27_0_0_4.realAnswer).add hm27_1_1_4.realAnswer).scale (-1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 27 (1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_0_0_4.realContains hm27_1_1_4.realContains) (-1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 2470854680265563235768870969, hi := 2470854680270217371786067013}
lemma t3_checked : ((hm27_0_0_5.realAnswer).add hm27_1_1_5.realAnswer).scale (-1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 27 (1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_0_0_5.realContains hm27_1_1_5.realContains) (-1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 1258792798416188555149157977, hi := 1258792798417108764129102893}
lemma t4_checked : ((hm27_0_0_6.realAnswer).add hm27_1_1_6.realAnswer).scale (-1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 27 (1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_0_0_6.realContains hm27_1_1_6.realContains) (-1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -136070654858536954653493470, hi := -136070654858380631544913071}
lemma t5_checked : ((hm27_0_0_7.realAnswer).add hm27_1_1_7.realAnswer).scale (-1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 27 (1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_0_0_7.realContains hm27_1_1_7.realContains) (-1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -73253593558777629223741823, hi := -73253593558754345320755268}
lemma t6_checked : ((hm27_0_0_8.realAnswer).add hm27_1_1_8.realAnswer).scale (-1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 27 (1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_0_0_8.realContains hm27_1_1_8.realContains) (-1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 3807142131614433360754015, hi := 3807142131617522012264174}
lemma t7_checked : ((hm27_0_0_9.realAnswer).add hm27_1_1_9.realAnswer).scale (-1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 27 (1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_0_0_9.realContains hm27_1_1_9.realContains) (-1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -728815928958878777357237282, hi := 728815928958878777357237282}
lemma tr8_contains : tr8.Contains (fullMoment true true 27 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 10 27 mixed_27_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := -406633684498555347771173, hi := 5287240760493054529717172}
lemma t8_checked : ((hm27_0_0_10.realAnswer).add tr8).scale (-1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 27 (1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_0_0_10.realContains tr8_contains) (-1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -273586055473683921267866222, hi := 273586055473683921267866222}
lemma tr9_contains : tr9.Contains (fullMoment true true 27 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 11 27 mixed_27_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -594319915571777109305213, hi := 474375613622340952710297}
lemma t9_checked : ((hm27_0_0_11.realAnswer).add tr9).scale (-1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 27 (1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_0_0_11.realContains tr9_contains) (-1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -94191747073031887938338274, hi := 94191747073031887938338274}
lemma tr10_contains : tr10.Contains (fullMoment true true 27 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 12 27 mixed_27_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -142678018040181174330846, hi := 41290237961838258068390}
lemma t10_checked : ((hm27_0_0_12.realAnswer).add tr10).scale (-1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 27 (1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_0_0_12.realContains tr10_contains) (-1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -826462401871455103132452, hi := 826462401871455103132452}
lemma t11_contains : t11.Contains (sourcePower false 27 (1/2) 2 11) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (1/2) 2 11 coarse_27_13) <;> norm_num [t11,precision]
noncomputable def t12 : RBox := {lo := -89909022963477775641683, hi := 89909022963477775641683}
lemma t12_contains : t12.Contains (sourcePower false 27 (1/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (1/2) 2 12 coarse_27_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -9203579534301380843272, hi := 9203579534301380843272}
lemma t13_contains : t13.Contains (sourcePower false 27 (1/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (1/2) 2 13 coarse_27_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -890168433085651111959, hi := 890168433085651111959}
lemma t14_contains : t14.Contains (sourcePower false 27 (1/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (1/2) 2 14 coarse_27_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -81667185972791006988, hi := 81667185972791006988}
lemma t15_contains : t15.Contains (sourcePower false 27 (1/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (1/2) 2 15 coarse_27_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -7133969330518964885, hi := 7133969330518964885}
lemma t16_contains : t16.Contains (sourcePower false 27 (1/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (1/2) 2 16 coarse_27_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -595600727454733885, hi := 595600727454733885}
lemma t17_contains : t17.Contains (sourcePower false 27 (1/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (1/2) 2 17 coarse_27_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -47704585830818839, hi := 47704585830818839}
lemma t18_contains : t18.Contains (sourcePower false 27 (1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (1/2) 2 18 coarse_27_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -3679656824384760, hi := 3679656824384760}
lemma t19_contains : t19.Contains (sourcePower false 27 (1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (1/2) 2 19 coarse_27_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -274393575161513, hi := 274393575161513}
lemma t20_contains : t20.Contains (sourcePower false 27 (1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (1/2) 2 20 coarse_27_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -19857565186914, hi := 19857565186914}
lemma t21_contains : t21.Contains (sourcePower false 27 (1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (1/2) 2 21 coarse_27_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -1399802782276, hi := 1399802782276}
lemma t22_contains : t22.Contains (sourcePower false 27 (1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (1/2) 2 22 coarse_27_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -96441529722, hi := 96441529722}
lemma t23_contains : t23.Contains (sourcePower false 27 (1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (1/2) 2 23 coarse_27_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -6512766124, hi := 6512766124}
lemma t24_contains : t24.Contains (sourcePower false 27 (1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (1/2) 2 24 coarse_27_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -432038233, hi := 432038233}
lemma t25_contains : t25.Contains (sourcePower false 27 (1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (1/2) 2 25 coarse_27_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -28192908, hi := 28192908}
lemma t26_contains : t26.Contains (sourcePower false 27 (1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (1/2) 2 26 coarse_27_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -1810811, hi := 1810811}
lemma t27_contains : t27.Contains (sourcePower false 27 (1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (1/2) 2 27 coarse_27_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -114464, hi := 114464}
lemma t28_contains : t28.Contains (sourcePower false 27 (1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (1/2) 2 28 coarse_27_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 27 (1/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (1/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 29308395013571919211948121096, hi := 29308395013713855658857956451}
lemma t0_checked : ((hm27_1_0_2.realAnswer).add hm27_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 27 (1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_1_0_2.realContains hm27_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -12148835160149641206844218047, hi := -12148835160094808814216553504}
lemma t1_checked : ((hm27_1_0_3.realAnswer).add hm27_0_1_3.realAnswer).scale (1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 27 (1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_1_0_3.realContains hm27_0_1_3.realContains) (1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -9320738140558341721005888573, hi := -9320738140542230487177381033}
lemma t2_checked : ((hm27_1_0_4.realAnswer).add hm27_0_1_4.realAnswer).scale (1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 27 (1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_1_0_4.realContains hm27_0_1_4.realContains) (1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 2475454640760206917814823257, hi := 2475454640764017074144603440}
lemma t3_checked : ((hm27_1_0_5.realAnswer).add hm27_0_1_5.realAnswer).scale (1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 27 (1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_1_0_5.realContains hm27_0_1_5.realContains) (1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 1283591701646041422353363952, hi := 1283591701646794805487900263}
lemma t4_checked : ((hm27_1_0_6.realAnswer).add hm27_0_1_6.realAnswer).scale (1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 27 (1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_1_0_6.realContains hm27_0_1_6.realContains) (1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -134103441105821732604994753, hi := -134103441105693744608145398}
lemma t5_checked : ((hm27_1_0_7.realAnswer).add hm27_0_1_7.realAnswer).scale (1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 27 (1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_1_0_7.realContains hm27_0_1_7.realContains) (1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -74716527229043335668614836, hi := -74716527229024271748881359}
lemma t6_checked : ((hm27_1_0_8.realAnswer).add hm27_0_1_8.realAnswer).scale (1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 27 (1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_1_0_8.realContains hm27_0_1_8.realContains) (1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 3640150830399666786460396, hi := 3640150830402195683583897}
lemma t7_checked : ((hm27_1_0_9.realAnswer).add hm27_0_1_9.realAnswer).scale (1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 27 (1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_1_0_9.realContains hm27_0_1_9.realContains) (1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -728815928958878777357237282, hi := 728815928958878777357237282}
lemma tr8_contains : tr8.Contains (fullMoment false true 27 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 10 27 mixed_27_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := -369036465002890643656529, hi := 5324837979988652257441112}
lemma t8_checked : ((hm27_1_0_10.realAnswer).add tr8).scale (1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 27 (1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_1_0_10.realContains tr8_contains) (1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -273586055473683921267866222, hi := 273586055473683921267866222}
lemma tr9_contains : tr9.Contains (fullMoment false true 27 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 11 27 mixed_27_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -587212221373609432351700, hi := 481483307820501332090967}
lemma t9_checked : ((hm27_1_0_11.realAnswer).add tr9).scale (1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 27 (1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_1_0_11.realContains tr9_contains) (1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -94191747073031887938338274, hi := 94191747073031887938338274}
lemma tr10_contains : tr10.Contains (fullMoment false true 27 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 12 27 mixed_27_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -143456314438875109710952, hi := 40511941563143592428876}
lemma t10_checked : ((hm27_1_0_12.realAnswer).add tr10).scale (1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 27 (1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_1_0_12.realContains tr10_contains) (1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -826462401871455103132452, hi := 826462401871455103132452}
lemma t11_contains : t11.Contains (sourcePower true 27 (1/2) 2 11) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (1/2) 2 11 coarse_27_13) <;> norm_num [t11,precision]
noncomputable def t12 : RBox := {lo := -89909022963477775641683, hi := 89909022963477775641683}
lemma t12_contains : t12.Contains (sourcePower true 27 (1/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (1/2) 2 12 coarse_27_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -9203579534301380843272, hi := 9203579534301380843272}
lemma t13_contains : t13.Contains (sourcePower true 27 (1/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (1/2) 2 13 coarse_27_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -890168433085651111959, hi := 890168433085651111959}
lemma t14_contains : t14.Contains (sourcePower true 27 (1/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (1/2) 2 14 coarse_27_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -81667185972791006988, hi := 81667185972791006988}
lemma t15_contains : t15.Contains (sourcePower true 27 (1/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (1/2) 2 15 coarse_27_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -7133969330518964885, hi := 7133969330518964885}
lemma t16_contains : t16.Contains (sourcePower true 27 (1/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (1/2) 2 16 coarse_27_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -595600727454733885, hi := 595600727454733885}
lemma t17_contains : t17.Contains (sourcePower true 27 (1/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (1/2) 2 17 coarse_27_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -47704585830818839, hi := 47704585830818839}
lemma t18_contains : t18.Contains (sourcePower true 27 (1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (1/2) 2 18 coarse_27_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -3679656824384760, hi := 3679656824384760}
lemma t19_contains : t19.Contains (sourcePower true 27 (1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (1/2) 2 19 coarse_27_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -274393575161513, hi := 274393575161513}
lemma t20_contains : t20.Contains (sourcePower true 27 (1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (1/2) 2 20 coarse_27_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -19857565186914, hi := 19857565186914}
lemma t21_contains : t21.Contains (sourcePower true 27 (1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (1/2) 2 21 coarse_27_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -1399802782276, hi := 1399802782276}
lemma t22_contains : t22.Contains (sourcePower true 27 (1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (1/2) 2 22 coarse_27_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -96441529722, hi := 96441529722}
lemma t23_contains : t23.Contains (sourcePower true 27 (1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (1/2) 2 23 coarse_27_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -6512766124, hi := 6512766124}
lemma t24_contains : t24.Contains (sourcePower true 27 (1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (1/2) 2 24 coarse_27_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -432038233, hi := 432038233}
lemma t25_contains : t25.Contains (sourcePower true 27 (1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (1/2) 2 25 coarse_27_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -28192908, hi := 28192908}
lemma t26_contains : t26.Contains (sourcePower true 27 (1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (1/2) 2 26 coarse_27_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -1810811, hi := 1810811}
lemma t27_contains : t27.Contains (sourcePower true 27 (1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (1/2) 2 27 coarse_27_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -114464, hi := 114464}
lemma t28_contains : t28.Contains (sourcePower true 27 (1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (1/2) 2 28 coarse_27_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 27 (1/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (1/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 28929288993229985313356265183, hi := 28929288993403452012686746439}
lemma t0_checked : ((hm27_0_0_2.realAnswer).add hm27_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 27 (-1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_0_0_2.realContains hm27_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 24161964175118690927293454177, hi := 24161964175252680019931356667}
lemma t1_checked : ((hm27_0_0_3.realAnswer).add hm27_1_1_3.realAnswer).scale (1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 27 (-1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_0_0_3.realContains hm27_1_1_3.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -36644003570205571317074829734, hi := -36644003570126844075036126177}
lemma t2_checked : ((hm27_0_0_4.realAnswer).add hm27_1_1_4.realAnswer).scale (-1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 27 (-1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_0_0_4.realContains hm27_1_1_4.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -19766837442161738974288536101, hi := -19766837442124505886150967753}
lemma t3_checked : ((hm27_0_0_5.realAnswer).add hm27_1_1_5.realAnswer).scale (1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 27 (-1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_0_0_5.realContains hm27_1_1_5.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 20140684774659016882386527645, hi := 20140684774673740226065646281}
lemma t4_checked : ((hm27_0_0_6.realAnswer).add hm27_1_1_6.realAnswer).scale (-1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 27 (-1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_0_0_6.realContains hm27_1_1_6.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 4354260955468180209437218299, hi := 4354260955473182548911791022}
lemma t5_checked : ((hm27_0_0_7.realAnswer).add hm27_1_1_7.realAnswer).scale (1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 27 (-1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_0_0_7.realContains hm27_1_1_7.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -4688229987761768270319476669, hi := -4688229987760278100528337189}
lemma t6_checked : ((hm27_0_0_8.realAnswer).add hm27_1_1_8.realAnswer).scale (-1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 27 (-1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_0_0_8.realContains hm27_1_1_8.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -487314192847042817569814256, hi := -487314192846647470176513981}
lemma t7_checked : ((hm27_0_0_9.realAnswer).add hm27_1_1_9.realAnswer).scale (1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 27 (-1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_0_0_9.realContains hm27_1_1_9.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -728815928958878777357237282, hi := 728815928958878777357237282}
lemma tr8_contains : tr8.Contains (fullMoment true true 27 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 10 27 mixed_27_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := -104098223231630169029420271, hi := 1353533634686221959607595917}
lemma t8_checked : ((hm27_0_0_10.realAnswer).add tr8).scale (-1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 27 (-1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_0_0_10.realContains tr8_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -273586055473683921267866222, hi := 273586055473683921267866222}
lemma tr9_contains : tr9.Contains (fullMoment true true 27 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 11 27 mixed_27_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -242880314174638567787671928, hi := 304291796772749879964269046}
lemma t9_checked : ((hm27_0_0_11.realAnswer).add tr9).scale (1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 27 (-1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_0_0_11.realContains tr9_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -94191747073031887938338274, hi := 94191747073031887938338274}
lemma tr10_contains : tr10.Contains (fullMoment true true 27 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 12 27 mixed_27_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -146102290473145522514785846, hi := 42281203672922376262030869}
lemma t10_checked : ((hm27_0_0_12.realAnswer).add tr10).scale (-1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 27 (-1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_0_0_12.realContains tr10_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -1692594999032740051215259804, hi := 1692594999032740051215259804}
lemma t11_contains : t11.Contains (sourcePower false 27 (-1/1) 2 11) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (-1/1) 2 11 coarse_27_13) <;> norm_num [t11,precision]
noncomputable def t12 : RBox := {lo := -368267358058404969028329713, hi := 368267358058404969028329713}
lemma t12_contains : t12.Contains (sourcePower false 27 (-1/1) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (-1/1) 2 12 coarse_27_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -75395723544996911868080822, hi := 75395723544996911868080822}
lemma t13_contains : t13.Contains (sourcePower false 27 (-1/1) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (-1/1) 2 13 coarse_27_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -14584519607675307818323276, hi := 14584519607675307818323276}
lemma t14_contains : t14.Contains (sourcePower false 27 (-1/1) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (-1/1) 2 14 coarse_27_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -2676070349956415716955635, hi := 2676070349956415716955635}
lemma t15_contains : t15.Contains (sourcePower false 27 (-1/1) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (-1/1) 2 15 coarse_27_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -467531814044890882677192, hi := 467531814044890882677192}
lemma t16_contains : t16.Contains (sourcePower false 27 (-1/1) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (-1/1) 2 16 coarse_27_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -78066578548946879717983, hi := 78066578548946879717983}
lemma t17_contains : t17.Contains (sourcePower false 27 (-1/1) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (-1/1) 2 17 coarse_27_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -12505470948034173484841, hi := 12505470948034173484841}
lemma t18_contains : t18.Contains (sourcePower false 27 (-1/1) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (-1/1) 2 18 coarse_27_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -1929199917143036737388, hi := 1929199917143036737388}
lemma t19_contains : t19.Contains (sourcePower false 27 (-1/1) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (-1/1) 2 19 coarse_27_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -287722517468558106377, hi := 287722517468558106377}
lemma t20_contains : t20.Contains (sourcePower false 27 (-1/1) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (-1/1) 2 20 coarse_27_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -41644332546865669400, hi := 41644332546865669400}
lemma t21_contains : t21.Contains (sourcePower false 27 (-1/1) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (-1/1) 2 21 coarse_27_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -5871198408907366325, hi := 5871198408907366325}
lemma t22_contains : t22.Contains (sourcePower false 27 (-1/1) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (-1/1) 2 22 coarse_27_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -809010187757680160, hi := 809010187757680160}
lemma t23_contains : t23.Contains (sourcePower false 27 (-1/1) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (-1/1) 2 23 coarse_27_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -109266084005681632, hi := 109266084005681632}
lemma t24_contains : t24.Contains (sourcePower false 27 (-1/1) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (-1/1) 2 24 coarse_27_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -14496797495949849, hi := 14496797495949849}
lemma t25_contains : t25.Contains (sourcePower false 27 (-1/1) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (-1/1) 2 25 coarse_27_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -1891993966608611, hi := 1891993966608611}
lemma t26_contains : t26.Contains (sourcePower false 27 (-1/1) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (-1/1) 2 26 coarse_27_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -243042902681483, hi := 243042902681483}
lemma t27_contains : t27.Contains (sourcePower false 27 (-1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (-1/1) 2 27 coarse_27_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -30725956372471, hi := 30725956372471}
lemma t28_contains : t28.Contains (sourcePower false 27 (-1/1) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 27 (-1/1) 2 28 coarse_27_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 27 (-1/1) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 27 (-1/1) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 29308395013571919211948121096, hi := 29308395013713855658857956451}
lemma t0_checked : ((hm27_1_0_2.realAnswer).add hm27_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 27 (-1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_1_0_2.realContains hm27_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 24297670320189617628433107009, hi := 24297670320299282413688436093}
lemma t1_checked : ((hm27_1_0_3.realAnswer).add hm27_0_1_3.realAnswer).scale (-1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 27 (-1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_1_0_3.realContains hm27_0_1_3.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -37282952562233366884023554289, hi := -37282952562168921948709524133}
lemma t2_checked : ((hm27_1_0_4.realAnswer).add hm27_0_1_4.realAnswer).scale (1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 27 (-1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_1_0_4.realContains hm27_0_1_4.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -19803637126112136593156827515, hi := -19803637126081655342518586057}
lemma t3_checked : ((hm27_1_0_5.realAnswer).add hm27_0_1_5.realAnswer).scale (-1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 27 (-1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_1_0_5.realContains hm27_0_1_5.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 20537467226336662757653823242, hi := 20537467226348716887806404206}
lemma t4_checked : ((hm27_1_0_6.realAnswer).add hm27_0_1_6.realAnswer).scale (1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 27 (-1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_1_0_6.realContains hm27_0_1_6.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 4291310115382199827460652739, hi := 4291310115386295443359832072}
lemma t5_checked : ((hm27_1_0_7.realAnswer).add hm27_0_1_7.realAnswer).scale (-1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 27 (-1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_1_0_7.realContains hm27_0_1_7.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -4781857742658773482791349454, hi := -4781857742657553391928407012}
lemma t6_checked : ((hm27_1_0_8.realAnswer).add hm27_0_1_8.realAnswer).scale (1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 27 (-1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_1_0_8.realContains hm27_0_1_8.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -465939306291481047498738780, hi := -465939306291157348666930704}
lemma t7_checked : ((hm27_1_0_9.realAnswer).add hm27_0_1_9.realAnswer).scale (-1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 27 (-1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_1_0_9.realContains hm27_0_1_9.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -728815928958878777357237282, hi := 728815928958878777357237282}
lemma tr8_contains : tr8.Contains (fullMoment false true 27 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 10 27 mixed_27_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := -94473335040740004776071389, hi := 1363158522877094977904924468}
lemma t8_checked : ((hm27_1_0_10.realAnswer).add tr8).scale (1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 27 (-1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_1_0_10.realContains tr8_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -273586055473683921267866222, hi := 273586055473683921267866222}
lemma tr9_contains : tr9.Contains (fullMoment false true 27 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 11 27 mixed_27_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -246519453604096682030574692, hi := 300652657343288029364070110}
lemma t9_checked : ((hm27_1_0_11.realAnswer).add tr9).scale (-1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 27 (-1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_1_0_11.realContains tr9_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -94191747073031887938338274, hi := 94191747073031887938338274}
lemma tr10_contains : tr10.Contains (fullMoment false true 27 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 12 27 mixed_27_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -146899265985408112344013964, hi := 41484228160659038647168137}
lemma t10_checked : ((hm27_1_0_12.realAnswer).add tr10).scale (1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 27 (-1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm27_1_0_12.realContains tr10_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -1692594999032740051215259804, hi := 1692594999032740051215259804}
lemma t11_contains : t11.Contains (sourcePower true 27 (-1/1) 2 11) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (-1/1) 2 11 coarse_27_13) <;> norm_num [t11,precision]
noncomputable def t12 : RBox := {lo := -368267358058404969028329713, hi := 368267358058404969028329713}
lemma t12_contains : t12.Contains (sourcePower true 27 (-1/1) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (-1/1) 2 12 coarse_27_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -75395723544996911868080822, hi := 75395723544996911868080822}
lemma t13_contains : t13.Contains (sourcePower true 27 (-1/1) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (-1/1) 2 13 coarse_27_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -14584519607675307818323276, hi := 14584519607675307818323276}
lemma t14_contains : t14.Contains (sourcePower true 27 (-1/1) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (-1/1) 2 14 coarse_27_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -2676070349956415716955635, hi := 2676070349956415716955635}
lemma t15_contains : t15.Contains (sourcePower true 27 (-1/1) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (-1/1) 2 15 coarse_27_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -467531814044890882677192, hi := 467531814044890882677192}
lemma t16_contains : t16.Contains (sourcePower true 27 (-1/1) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (-1/1) 2 16 coarse_27_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -78066578548946879717983, hi := 78066578548946879717983}
lemma t17_contains : t17.Contains (sourcePower true 27 (-1/1) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (-1/1) 2 17 coarse_27_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -12505470948034173484841, hi := 12505470948034173484841}
lemma t18_contains : t18.Contains (sourcePower true 27 (-1/1) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (-1/1) 2 18 coarse_27_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -1929199917143036737388, hi := 1929199917143036737388}
lemma t19_contains : t19.Contains (sourcePower true 27 (-1/1) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (-1/1) 2 19 coarse_27_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -287722517468558106377, hi := 287722517468558106377}
lemma t20_contains : t20.Contains (sourcePower true 27 (-1/1) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (-1/1) 2 20 coarse_27_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -41644332546865669400, hi := 41644332546865669400}
lemma t21_contains : t21.Contains (sourcePower true 27 (-1/1) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (-1/1) 2 21 coarse_27_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -5871198408907366325, hi := 5871198408907366325}
lemma t22_contains : t22.Contains (sourcePower true 27 (-1/1) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (-1/1) 2 22 coarse_27_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -809010187757680160, hi := 809010187757680160}
lemma t23_contains : t23.Contains (sourcePower true 27 (-1/1) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (-1/1) 2 23 coarse_27_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -109266084005681632, hi := 109266084005681632}
lemma t24_contains : t24.Contains (sourcePower true 27 (-1/1) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (-1/1) 2 24 coarse_27_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -14496797495949849, hi := 14496797495949849}
lemma t25_contains : t25.Contains (sourcePower true 27 (-1/1) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (-1/1) 2 25 coarse_27_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -1891993966608611, hi := 1891993966608611}
lemma t26_contains : t26.Contains (sourcePower true 27 (-1/1) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (-1/1) 2 26 coarse_27_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -243042902681483, hi := 243042902681483}
lemma t27_contains : t27.Contains (sourcePower true 27 (-1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (-1/1) 2 27 coarse_27_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -30725956372471, hi := 30725956372471}
lemma t28_contains : t28.Contains (sourcePower true 27 (-1/1) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 27 (-1/1) 2 28 coarse_27_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 27 (-1/1) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) k.val := by
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
end SharpPlanar.Bernstein27

end OAI
