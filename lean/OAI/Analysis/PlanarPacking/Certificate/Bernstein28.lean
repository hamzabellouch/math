import OAI.Analysis.PlanarPacking.Certificate.LowBlock28_0
import OAI.Analysis.PlanarPacking.Certificate.LowBlock28_1
import OAI.Analysis.PlanarPacking.Certificate.LowBlock28_10
import OAI.Analysis.PlanarPacking.Certificate.LowBlock28_11
import OAI.Analysis.PlanarPacking.Certificate.MixedBound28
import OAI.Analysis.PlanarPacking.Certificate.CoarseBound28

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein28
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 53572065653605471163481495577, hi := 53572065653779362113488256454}
lemma t0_checked : ((hm28_0_0_2.realAnswer).add hm28_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 28 (3/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_0_0_2.realContains hm28_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 169561061694486737598116094022, hi := 169561061694688183391607635874}
lemma t1_checked : ((hm28_0_0_3.realAnswer).add hm28_1_1_3.realAnswer).scale (-3) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 28 (3/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_0_0_3.realContains hm28_1_1_3.realContains) (-3) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := 89522630108250704633950529379, hi := 89522630108428237475608418526}
lemma t2_checked : ((hm28_0_0_4.realAnswer).add hm28_1_1_4.realAnswer).scale (-9) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 28 (3/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_0_0_4.realContains hm28_1_1_4.realContains) (-9) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -161344202786787510373601088985, hi := -161344202786661570299260587956}
lemma t3_checked : ((hm28_0_0_5.realAnswer).add hm28_1_1_5.realAnswer).scale (-27) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 28 (3/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_0_0_5.realContains hm28_1_1_5.realContains) (-27) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := -128484391152766544543076037707, hi := -128484391152691842762221453565}
lemma t4_checked : ((hm28_0_0_6.realAnswer).add hm28_1_1_6.realAnswer).scale (-81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 28 (3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_0_0_6.realContains hm28_1_1_6.realContains) (-81) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 64578024435592254792230079600, hi := 64578024435630325661419307102}
lemma t5_checked : ((hm28_0_0_7.realAnswer).add hm28_1_1_7.realAnswer).scale (-243) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 28 (3/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_0_0_7.realContains hm28_1_1_7.realContains) (-243) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := 63661121625194689313764607265, hi := 63661121625211701289032594851}
lemma t6_checked : ((hm28_0_0_8.realAnswer).add hm28_1_1_8.realAnswer).scale (-729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 28 (3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_0_0_8.realContains hm28_1_1_8.realContains) (-729) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -14600916086764974747375777778, hi := -14600916086758204552852360775}
lemma t7_checked : ((hm28_0_0_9.realAnswer).add hm28_1_1_9.realAnswer).scale (-2187) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 28 (3/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_0_0_9.realContains hm28_1_1_9.realContains) (-2187) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -583317053256357189680567802, hi := 583317053256357189680567802}
lemma tr8_contains : tr8.Contains (fullMoment true true 28 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 10 28 mixed_28_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := -32959788579715799069888989955, hi := -3060232435846498396282852568}
lemma t8_checked : ((hm28_0_0_10.realAnswer).add tr8).scale (-6561) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 28 (3/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_0_0_10.realContains tr8_contains) (-6561) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -218934359068331366565401467, hi := 218934359068331366565401467}
lemma tr9_contains : tr9.Contains (fullMoment true true 28 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 11 28 mixed_28_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -6292552990910282725827201296, hi := 10540591499488817082477624227}
lemma t9_checked : ((hm28_0_0_11.realAnswer).add tr9).scale (-19683) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 28 (3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_0_0_11.realContains tr9_contains) (-19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -75365738378018125404513893, hi := 75365738378018125404513893}
lemma tr10_contains : tr10.Contains (fullMoment true true 28 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 12 28 mixed_28_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -1108807378404120305639285454, hi := 7583129116681259198826308762}
lemma t10_checked : ((hm28_0_0_12.realAnswer).add tr10).scale (-59049) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 28 (3/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_0_0_12.realContains tr10_contains) (-59049) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -23959747803008070727398235, hi := 23959747803008070727398235}
lemma tr11_contains : tr11.Contains (fullMoment true true 28 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 13 28 mixed_28_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := -2293706629503702921410202363, hi := 1851212749460690100801475673}
lemma t11_checked : ((hm28_0_0_13.realAnswer).add tr11).scale (-177147) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 28 (3/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_0_0_13.realContains tr11_contains) (-177147) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -47551748981776413753898836465, hi := 47551748981776413753898836465}
lemma t12_contains : t12.Contains (sourcePower false 28 (3/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (3/2) 2 12 coarse_28_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -14578471500289312856490453923, hi := 14578471500289312856490453923}
lemma t13_contains : t13.Contains (sourcePower false 28 (3/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (3/2) 2 13 coarse_28_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -4220780499850943816803078776, hi := 4220780499850943816803078776}
lemma t14_contains : t14.Contains (sourcePower false 28 (3/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (3/2) 2 14 coarse_28_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -1158366745494303787974643957, hi := 1158366745494303787974643957}
lemma t15_contains : t15.Contains (sourcePower false 28 (3/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (3/2) 2 15 coarse_28_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -302446302716274629369327260, hi := 302446302716274629369327260}
lemma t16_contains : t16.Contains (sourcePower false 28 (3/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (3/2) 2 16 coarse_28_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -75396249374312909453520699, hi := 75396249374312909453520699}
lemma t17_contains : t17.Contains (sourcePower false 28 (3/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (3/2) 2 17 coarse_28_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -18009576036600048324944622, hi := 18009576036600048324944622}
lemma t18_contains : t18.Contains (sourcePower false 28 (3/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (3/2) 2 18 coarse_28_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -4136995935440357267488668, hi := 4136995935440357267488668}
lemma t19_contains : t19.Contains (sourcePower false 28 (3/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (3/2) 2 19 coarse_28_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -917275826786287346187836, hi := 917275826786287346187836}
lemma t20_contains : t20.Contains (sourcePower false 28 (3/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (3/2) 2 20 coarse_28_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -197048374827896082858002, hi := 197048374827896082858002}
lemma t21_contains : t21.Contains (sourcePower false 28 (3/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (3/2) 2 21 coarse_28_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -41163784493358540938996, hi := 41163784493358540938996}
lemma t22_contains : t22.Contains (sourcePower false 28 (3/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (3/2) 2 22 coarse_28_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -8392059223461790609972, hi := 8392059223461790609972}
lemma t23_contains : t23.Contains (sourcePower false 28 (3/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (3/2) 2 23 coarse_28_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -1675046444258822050151, hi := 1675046444258822050151}
lemma t24_contains : t24.Contains (sourcePower false 28 (3/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (3/2) 2 24 coarse_28_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -328210851349012800663, hi := 328210851349012800663}
lemma t25_contains : t25.Contains (sourcePower false 28 (3/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (3/2) 2 25 coarse_28_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -63256426471434251136, hi := 63256426471434251136}
lemma t26_contains : t26.Contains (sourcePower false 28 (3/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (3/2) 2 26 coarse_28_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -12005859662292129143, hi := 12005859662292129143}
lemma t27_contains : t27.Contains (sourcePower false 28 (3/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (3/2) 2 27 coarse_28_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -2244844860502577062, hi := 2244844860502577062}
lemma t28_contains : t28.Contains (sourcePower false 28 (3/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (3/2) 2 28 coarse_28_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 28 (3/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (3/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 54596086286414276157629956797, hi := 54596086286556366769529502400}
lemma t0_checked : ((hm28_1_0_2.realAnswer).add hm28_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 28 (3/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_1_0_2.realContains hm28_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 173267231542336682125204232031, hi := 173267231542501354948145795936}
lemma t1_checked : ((hm28_1_0_3.realAnswer).add hm28_0_1_3.realAnswer).scale (3) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 28 (3/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_1_0_3.realContains hm28_0_1_3.realContains) (3) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := 92681381616187175613694721686, hi := 92681381616332330157110801330}
lemma t2_checked : ((hm28_1_0_4.realAnswer).add hm28_0_1_4.realAnswer).scale (9) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 28 (3/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_1_0_4.realContains hm28_0_1_4.realContains) (9) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -163724387595077585600657986431, hi := -163724387594974602910157740608}
lemma t3_checked : ((hm28_1_0_5.realAnswer).add hm28_0_1_5.realAnswer).scale (27) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 28 (3/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_1_0_5.realContains hm28_0_1_5.realContains) (27) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := -132369364958306795205733795922, hi := -132369364958245706768335251306}
lemma t4_checked : ((hm28_1_0_6.realAnswer).add hm28_0_1_6.realAnswer).scale (81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 28 (3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_1_0_6.realContains hm28_0_1_6.realContains) (81) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 64776955170409267760084874679, hi := 64776955170440401834798376568}
lemma t5_checked : ((hm28_1_0_7.realAnswer).add hm28_0_1_7.realAnswer).scale (243) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 28 (3/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_1_0_7.realContains hm28_0_1_7.realContains) (243) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := 65485213001990402244613822611, hi := 65485213002004314720283351868}
lemma t6_checked : ((hm28_1_0_8.realAnswer).add hm28_0_1_8.realAnswer).scale (729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 28 (3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_1_0_8.realContains hm28_0_1_8.realContains) (729) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -14366235057888390940101585897, hi := -14366235057882854242317229525}
lemma t7_checked : ((hm28_1_0_9.realAnswer).add hm28_0_1_9.realAnswer).scale (2187) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 28 (3/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_1_0_9.realContains hm28_0_1_9.realContains) (2187) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -583317053256357189680567802, hi := 583317053256357189680567802}
lemma tr8_contains : tr8.Contains (fullMoment false true 28 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 10 28 mixed_28_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := -33409359046836491817371859608, hi := -3509802902967633979947623916}
lemma t8_checked : ((hm28_1_0_10.realAnswer).add tr8).scale (6561) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 28 (3/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_1_0_10.realContains tr8_contains) (6561) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -218934359068331366565401467, hi := 218934359068331366565401467}
lemma tr9_contains : tr9.Contains (fullMoment false true 28 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 11 28 mixed_28_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -6418338087775682420911137007, hi := 10414806402623272614693288274}
lemma t9_checked : ((hm28_1_0_11.realAnswer).add tr9).scale (19683) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 28 (3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_1_0_11.realContains tr9_contains) (19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -75365738378018125404513893, hi := 75365738378018125404513893}
lemma tr10_contains : tr10.Contains (fullMoment false true 28 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 12 28 mixed_28_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -1030332550963118175973099781, hi := 7661603944122217859009779201}
lemma t10_checked : ((hm28_1_0_12.realAnswer).add tr10).scale (59049) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 28 (3/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_1_0_12.realContains tr10_contains) (59049) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -23959747803008070727398235, hi := 23959747803008070727398235}
lemma tr11_contains : tr11.Contains (fullMoment false true 28 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 13 28 mixed_28_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := -2268041930336048725092328254, hi := 1876877448628332225540424362}
lemma t11_checked : ((hm28_1_0_13.realAnswer).add tr11).scale (177147) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 28 (3/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_1_0_13.realContains tr11_contains) (177147) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -47551748981776413753898836465, hi := 47551748981776413753898836465}
lemma t12_contains : t12.Contains (sourcePower true 28 (3/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (3/2) 2 12 coarse_28_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -14578471500289312856490453923, hi := 14578471500289312856490453923}
lemma t13_contains : t13.Contains (sourcePower true 28 (3/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (3/2) 2 13 coarse_28_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -4220780499850943816803078776, hi := 4220780499850943816803078776}
lemma t14_contains : t14.Contains (sourcePower true 28 (3/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (3/2) 2 14 coarse_28_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -1158366745494303787974643957, hi := 1158366745494303787974643957}
lemma t15_contains : t15.Contains (sourcePower true 28 (3/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (3/2) 2 15 coarse_28_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -302446302716274629369327260, hi := 302446302716274629369327260}
lemma t16_contains : t16.Contains (sourcePower true 28 (3/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (3/2) 2 16 coarse_28_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -75396249374312909453520699, hi := 75396249374312909453520699}
lemma t17_contains : t17.Contains (sourcePower true 28 (3/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (3/2) 2 17 coarse_28_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -18009576036600048324944622, hi := 18009576036600048324944622}
lemma t18_contains : t18.Contains (sourcePower true 28 (3/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (3/2) 2 18 coarse_28_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -4136995935440357267488668, hi := 4136995935440357267488668}
lemma t19_contains : t19.Contains (sourcePower true 28 (3/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (3/2) 2 19 coarse_28_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -917275826786287346187836, hi := 917275826786287346187836}
lemma t20_contains : t20.Contains (sourcePower true 28 (3/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (3/2) 2 20 coarse_28_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -197048374827896082858002, hi := 197048374827896082858002}
lemma t21_contains : t21.Contains (sourcePower true 28 (3/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (3/2) 2 21 coarse_28_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -41163784493358540938996, hi := 41163784493358540938996}
lemma t22_contains : t22.Contains (sourcePower true 28 (3/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (3/2) 2 22 coarse_28_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -8392059223461790609972, hi := 8392059223461790609972}
lemma t23_contains : t23.Contains (sourcePower true 28 (3/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (3/2) 2 23 coarse_28_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -1675046444258822050151, hi := 1675046444258822050151}
lemma t24_contains : t24.Contains (sourcePower true 28 (3/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (3/2) 2 24 coarse_28_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -328210851349012800663, hi := 328210851349012800663}
lemma t25_contains : t25.Contains (sourcePower true 28 (3/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (3/2) 2 25 coarse_28_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -63256426471434251136, hi := 63256426471434251136}
lemma t26_contains : t26.Contains (sourcePower true 28 (3/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (3/2) 2 26 coarse_28_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -12005859662292129143, hi := 12005859662292129143}
lemma t27_contains : t27.Contains (sourcePower true 28 (3/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (3/2) 2 27 coarse_28_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -2244844860502577062, hi := 2244844860502577062}
lemma t28_contains : t28.Contains (sourcePower true 28 (3/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (3/2) 2 28 coarse_28_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 28 (3/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (3/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 53572065653605471163481495577, hi := 53572065653779362113488256454}
lemma t0_checked : ((hm28_0_0_2.realAnswer).add hm28_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 28 (-1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_0_0_2.realContains hm28_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -56520353898229394463869211958, hi := -56520353898162245866038698007}
lemma t1_checked : ((hm28_0_0_3.realAnswer).add hm28_1_1_3.realAnswer).scale (1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 28 (-1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_0_0_3.realContains hm28_1_1_3.realContains) (1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := 9946958900916744959327836597, hi := 9946958900936470830623157614}
lemma t2_checked : ((hm28_0_0_4.realAnswer).add hm28_1_1_4.realAnswer).scale (-1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 28 (-1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_0_0_4.realContains hm28_1_1_4.realContains) (-1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 5975711214320798899972614368, hi := 5975711214325463347170410704}
lemma t3_checked : ((hm28_0_0_5.realAnswer).add hm28_1_1_5.realAnswer).scale (1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 28 (-1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_0_0_5.realContains hm28_1_1_5.realContains) (1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := -1586227051268722772136741207, hi := -1586227051267800527928659920}
lemma t4_checked : ((hm28_0_0_6.realAnswer).add hm28_1_1_6.realAnswer).scale (-1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 28 (-1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_0_0_6.realContains hm28_1_1_6.realContains) (-1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -265753186977902574738351059, hi := -265753186977745904494773990}
lemma t5_checked : ((hm28_0_0_7.realAnswer).add hm28_1_1_7.realAnswer).scale (1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 28 (-1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_0_0_7.realContains hm28_1_1_7.realContains) (1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := 87326641461172413324779982, hi := 87326641461195749367671598}
lemma t6_checked : ((hm28_0_0_8.realAnswer).add hm28_1_1_8.realAnswer).scale (-1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 28 (-1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_0_0_8.realContains hm28_1_1_8.realContains) (-1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 6676230492344858048857961, hi := 6676230492347953702503785}
lemma t7_checked : ((hm28_0_0_9.realAnswer).add hm28_1_1_9.realAnswer).scale (1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 28 (-1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_0_0_9.realContains hm28_1_1_9.realContains) (1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -583317053256357189680567802, hi := 583317053256357189680567802}
lemma tr8_contains : tr8.Contains (fullMoment true true 28 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 10 28 mixed_28_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := -5023592223703063415620941, hi := -466427745137402590501882}
lemma t8_checked : ((hm28_0_0_10.realAnswer).add tr8).scale (-1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 28 (-1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_0_0_10.realContains tr8_contains) (-1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -218934359068331366565401467, hi := 218934359068331366565401467}
lemma tr9_contains : tr9.Contains (fullMoment true true 28 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 11 28 mixed_28_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -535517527789910942563513, hi := 319694812320798797227415}
lemma t9_checked : ((hm28_0_0_11.realAnswer).add tr9).scale (1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 28 (-1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_0_0_11.realContains tr9_contains) (1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -75365738378018125404513893, hi := 75365738378018125404513893}
lemma tr10_contains : tr10.Contains (fullMoment true true 28 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 12 28 mixed_28_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -18777750315909165365024, hi := 128420957453661521767114}
lemma t10_checked : ((hm28_0_0_12.realAnswer).add tr10).scale (-1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 28 (-1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_0_0_12.realContains tr10_contains) (-1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -23959747803008070727398235, hi := 23959747803008070727398235}
lemma tr11_contains : tr11.Contains (fullMoment true true 28 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 13 28 mixed_28_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := -10450150154734147915582, hi := 12948041059141294638974}
lemma t11_checked : ((hm28_0_0_13.realAnswer).add tr11).scale (1) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 28 (-1/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_0_0_13.realContains tr11_contains) (1) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -89477004938979893824336, hi := 89477004938979893824336}
lemma t12_contains : t12.Contains (sourcePower false 28 (-1/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (-1/2) 2 12 coarse_28_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -9143988702596219747499, hi := 9143988702596219747499}
lemma t13_contains : t13.Contains (sourcePower false 28 (-1/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (-1/2) 2 13 coarse_28_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -882460350433160619859, hi := 882460350433160619859}
lemma t14_contains : t14.Contains (sourcePower false 28 (-1/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (-1/2) 2 14 coarse_28_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -80728570161776349096, hi := 80728570161776349096}
lemma t15_contains : t15.Contains (sourcePower false 28 (-1/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (-1/2) 2 15 coarse_28_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -7026000951762960747, hi := 7026000951762960747}
lemma t16_contains : t16.Contains (sourcePower false 28 (-1/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (-1/2) 2 16 coarse_28_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -583832694824095193, hi := 583832694824095193}
lemma t17_contains : t17.Contains (sourcePower false 28 (-1/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (-1/2) 2 17 coarse_28_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -46485863675114117, hi := 46485863675114117}
lemma t18_contains : t18.Contains (sourcePower false 28 (-1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (-1/2) 2 18 coarse_28_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -3559436540659536, hi := 3559436540659536}
lemma t19_contains : t19.Contains (sourcePower false 28 (-1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (-1/2) 2 19 coarse_28_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -263072137905406, hi := 263072137905406}
lemma t20_contains : t20.Contains (sourcePower false 28 (-1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (-1/2) 2 20 coarse_28_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -18837640661253, hi := 18837640661253}
lemma t21_contains : t21.Contains (sourcePower false 28 (-1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (-1/2) 2 21 coarse_28_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -1311739788467, hi := 1311739788467}
lemma t22_contains : t22.Contains (sourcePower false 28 (-1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (-1/2) 2 22 coarse_28_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -89141447400, hi := 89141447400}
lemma t23_contains : t23.Contains (sourcePower false 28 (-1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (-1/2) 2 23 coarse_28_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -5930847266, hi := 5930847266}
lemma t24_contains : t24.Contains (sourcePower false 28 (-1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (-1/2) 2 24 coarse_28_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -387366062, hi := 387366062}
lemma t25_contains : t25.Contains (sourcePower false 28 (-1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (-1/2) 2 25 coarse_28_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -24885825, hi := 24885825}
lemma t26_contains : t26.Contains (sourcePower false 28 (-1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (-1/2) 2 26 coarse_28_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -1574416, hi := 1574416}
lemma t27_contains : t27.Contains (sourcePower false 28 (-1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (-1/2) 2 27 coarse_28_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -98128, hi := 98128}
lemma t28_contains : t28.Contains (sourcePower false 28 (-1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 28 (-1/2) 2 28 coarse_28_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 28 (-1/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 28 (-1/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 54596086286414276157629956797, hi := 54596086286556366769529502400}
lemma t0_checked : ((hm28_1_0_2.realAnswer).add hm28_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 28 (-1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_1_0_2.realContains hm28_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -57755743847500451649381931979, hi := -57755743847445560708401410677}
lemma t1_checked : ((hm28_1_0_3.realAnswer).add hm28_0_1_3.realAnswer).scale (-1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 28 (-1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_1_0_3.realContains hm28_0_1_3.realContains) (-1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := 10297931290687463957077191298, hi := 10297931290703592239678977926}
lemma t2_checked : ((hm28_1_0_4.realAnswer).add hm28_0_1_4.realAnswer).scale (1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 28 (-1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_1_0_4.realContains hm28_0_1_4.realContains) (1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 6063866207221281589265101504, hi := 6063866207225095762987332831}
lemma t3_checked : ((hm28_1_0_5.realAnswer).add hm28_0_1_5.realAnswer).scale (-1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 28 (-1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_1_0_5.realContains hm28_0_1_5.realContains) (-1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := -1634189690843293767972022172, hi := -1634189690842539589732533966}
lemma t4_checked : ((hm28_1_0_6.realAnswer).add hm28_0_1_6.realAnswer).scale (1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 28 (-1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_1_0_6.realContains hm28_0_1_6.realContains) (1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -266571831977120995204931591, hi := -266571831976992871440678496}
lemma t5_checked : ((hm28_1_0_7.realAnswer).add hm28_0_1_7.realAnswer).scale (-1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 28 (-1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_1_0_7.realContains hm28_0_1_7.realContains) (-1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := 89828824419739920774504557, hi := 89828824419759005103269345}
lemma t6_checked : ((hm28_1_0_8.realAnswer).add hm28_0_1_8.realAnswer).scale (1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 28 (-1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_1_0_8.realContains hm28_0_1_8.realContains) (1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 6568923208908483878517251, hi := 6568923208911015519022216}
lemma t7_checked : ((hm28_1_0_9.realAnswer).add hm28_0_1_9.realAnswer).scale (-1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 28 (-1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_1_0_9.realContains hm28_0_1_9.realContains) (-1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -583317053256357189680567802, hi := 583317053256357189680567802}
lemma tr8_contains : tr8.Contains (fullMoment false true 28 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 10 28 mixed_28_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := -5092113861733956990911730, hi := -534949383168363661019299}
lemma t8_checked : ((hm28_1_0_10.realAnswer).add tr8).scale (1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 28 (-1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_1_0_10.realContains tr8_contains) (1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -218934359068331366565401467, hi := 218934359068331366565401467}
lemma tr9_contains : tr9.Contains (fullMoment false true 28 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 11 28 mixed_28_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -529126982808681228201661, hi := 326085357302021156374087}
lemma t9_checked : ((hm28_1_0_11.realAnswer).add tr9).scale (-1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 28 (-1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_1_0_11.realContains tr9_contains) (-1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -75365738378018125404513893, hi := 75365738378018125404513893}
lemma tr10_contains : tr10.Contains (fullMoment false true 28 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 12 28 mixed_28_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -17448772222444379684214, hi := 129749935547125571288418}
lemma t10_checked : ((hm28_1_0_12.realAnswer).add tr10).scale (1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 28 (-1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_1_0_12.realContains tr10_contains) (1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -23959747803008070727398235, hi := 23959747803008070727398235}
lemma tr11_contains : tr11.Contains (fullMoment false true 28 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 13 28 mixed_28_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := -10595028132727803606838, hi := 12803163081147570803301}
lemma t11_checked : ((hm28_1_0_13.realAnswer).add tr11).scale (-1) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 28 (-1/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm28_1_0_13.realContains tr11_contains) (-1) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -89477004938979893824336, hi := 89477004938979893824336}
lemma t12_contains : t12.Contains (sourcePower true 28 (-1/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (-1/2) 2 12 coarse_28_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -9143988702596219747499, hi := 9143988702596219747499}
lemma t13_contains : t13.Contains (sourcePower true 28 (-1/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (-1/2) 2 13 coarse_28_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -882460350433160619859, hi := 882460350433160619859}
lemma t14_contains : t14.Contains (sourcePower true 28 (-1/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (-1/2) 2 14 coarse_28_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -80728570161776349096, hi := 80728570161776349096}
lemma t15_contains : t15.Contains (sourcePower true 28 (-1/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (-1/2) 2 15 coarse_28_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -7026000951762960747, hi := 7026000951762960747}
lemma t16_contains : t16.Contains (sourcePower true 28 (-1/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (-1/2) 2 16 coarse_28_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -583832694824095193, hi := 583832694824095193}
lemma t17_contains : t17.Contains (sourcePower true 28 (-1/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (-1/2) 2 17 coarse_28_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -46485863675114117, hi := 46485863675114117}
lemma t18_contains : t18.Contains (sourcePower true 28 (-1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (-1/2) 2 18 coarse_28_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -3559436540659536, hi := 3559436540659536}
lemma t19_contains : t19.Contains (sourcePower true 28 (-1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (-1/2) 2 19 coarse_28_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -263072137905406, hi := 263072137905406}
lemma t20_contains : t20.Contains (sourcePower true 28 (-1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (-1/2) 2 20 coarse_28_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -18837640661253, hi := 18837640661253}
lemma t21_contains : t21.Contains (sourcePower true 28 (-1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (-1/2) 2 21 coarse_28_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -1311739788467, hi := 1311739788467}
lemma t22_contains : t22.Contains (sourcePower true 28 (-1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (-1/2) 2 22 coarse_28_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -89141447400, hi := 89141447400}
lemma t23_contains : t23.Contains (sourcePower true 28 (-1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (-1/2) 2 23 coarse_28_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -5930847266, hi := 5930847266}
lemma t24_contains : t24.Contains (sourcePower true 28 (-1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (-1/2) 2 24 coarse_28_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -387366062, hi := 387366062}
lemma t25_contains : t25.Contains (sourcePower true 28 (-1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (-1/2) 2 25 coarse_28_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -24885825, hi := 24885825}
lemma t26_contains : t26.Contains (sourcePower true 28 (-1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (-1/2) 2 26 coarse_28_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -1574416, hi := 1574416}
lemma t27_contains : t27.Contains (sourcePower true 28 (-1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (-1/2) 2 27 coarse_28_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -98128, hi := 98128}
lemma t28_contains : t28.Contains (sourcePower true 28 (-1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 28 (-1/2) 2 28 coarse_28_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 28 (-1/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 28 (-1/2) 2) k.val := by
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
end SharpPlanar.Bernstein28

end OAI
