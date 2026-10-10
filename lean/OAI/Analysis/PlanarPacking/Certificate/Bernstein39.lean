import OAI.Analysis.PlanarPacking.Certificate.LowBlock39_0
import OAI.Analysis.PlanarPacking.Certificate.LowBlock39_1
import OAI.Analysis.PlanarPacking.Certificate.LowBlock39_10
import OAI.Analysis.PlanarPacking.Certificate.MixedBound39
import OAI.Analysis.PlanarPacking.Certificate.CoarseBound39

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein39
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 27724996064324143733931502505, hi := 27724996064551861453911962360}
lemma t0_checked : ((hm39_0_0_2.realAnswer).add hm39_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 39 (1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_0_0_2.realContains hm39_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -11507375710819762256302248042, hi := -11507375710733089518451868974}
lemma t1_checked : ((hm39_0_0_3.realAnswer).add hm39_1_1_3.realAnswer).scale (-1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 39 (1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_0_0_3.realContains hm39_1_1_3.realContains) (-1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -8819786303213856602507514089, hi := -8819786303188546531640685545}
lemma t2_checked : ((hm39_0_0_4.realAnswer).add hm39_1_1_4.realAnswer).scale (-1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 39 (1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_0_0_4.realContains hm39_1_1_4.realContains) (-1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 2350089288621544521734441584, hi := 2350089288627514946853371101}
lemma t3_checked : ((hm39_0_0_5.realAnswer).add hm39_1_1_5.realAnswer).scale (-1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 39 (1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_0_0_5.realContains hm39_1_1_5.realContains) (-1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr4 : RBox := {lo := -950984512557742813967069481, hi := 950984512557742813967069481}
lemma tr4_contains : tr4.Contains (fullMoment true true 39 6) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 6 39 mixed_39_6) <;> norm_num [tr4,precision]
noncomputable def t4 : RBox := {lo := 1157105663708280819829289628, hi := 1275978727779178242134228371}
lemma t4_checked : ((hm39_0_0_6.realAnswer).add tr4).scale (-1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 39 (1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_0_0_6.realContains tr4_contains) (-1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr5 : RBox := {lo := -557658605426100677627684034, hi := 557658605426100677627684034}
lemma tr5_contains : tr5.Contains (fullMoment true true 39 7) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 7 39 mixed_39_7) <;> norm_num [tr5,precision]
noncomputable def t5 : RBox := {lo := -144524912224341302404564595, hi := -109671249385009582011183563}
lemma t5_checked : ((hm39_0_0_7.realAnswer).add tr5).scale (-1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 39 (1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_0_0_7.realContains tr5_contains) (-1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr6 : RBox := {lo := -286484792976969139723090417, hi := 286484792976969139723090417}
lemma tr6_contains : tr6.Contains (fullMoment true true 39 8) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 8 39 mixed_39_8) <;> norm_num [tr6,precision]
noncomputable def t6 : RBox := {lo := -75558472592100375794679700, hi := -66605822811540209037193880}
lemma t6_checked : ((hm39_0_0_8.realAnswer).add tr6).scale (-1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 39 (1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_0_0_8.realContains tr6_contains) (-1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr7 : RBox := {lo := -130964293330677630666136863, hi := 130964293330677630666136863}
lemma tr7_contains : tr7.Contains (fullMoment true true 39 9) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 9 39 mixed_39_9) <;> norm_num [tr7,precision]
noncomputable def t7 : RBox := {lo := 2451792599391428338645828, hi := 4498109682687236213344907}
lemma t7_checked : ((hm39_0_0_9.realAnswer).add tr7).scale (-1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 39 (1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_0_0_9.realContains tr7_contains) (-1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -53934136505805891769016377, hi := 53934136505805891769016377}
lemma tr8_contains : tr8.Contains (fullMoment true true 39 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 10 39 mixed_39_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := 2093280535918847318897588, hi := 2514640977370931688540136}
lemma t8_checked : ((hm39_0_0_10.realAnswer).add tr8).scale (-1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 39 (1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_0_0_10.realContains tr8_contains) (-1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -20209267537129097201365382, hi := 20209267537129097201365382}
lemma tr9_contains : tr9.Contains (fullMoment true true 39 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 11 39 mixed_39_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -98791229698309799967807, hi := -19848778381347289012264}
lemma t9_checked : ((hm39_0_0_11.realAnswer).add tr9).scale (-1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 39 (1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_0_0_11.realContains tr9_contains) (-1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -6946632271962133634215599, hi := 6946632271962133634215599}
lemma tr10_contains : tr10.Contains (fullMoment true true 39 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 12 39 mixed_39_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -54633278150644329153893, hi := -41065636994463070298464}
lemma t10_checked : ((hm39_0_0_12.realAnswer).add tr10).scale (-1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 39 (1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_0_0_12.realContains tr10_contains) (-1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -812916126211309011353084, hi := 812916126211309011353084}
lemma t11_contains : t11.Contains (sourcePower false 39 (1/2) 2 11) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (1/2) 2 11 coarse_39_13) <;> norm_num [t11,precision]
noncomputable def t12 : RBox := {lo := -87908302074304336339431, hi := 87908302074304336339431}
lemma t12_contains : t12.Contains (sourcePower false 39 (1/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (1/2) 2 12 coarse_39_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -8927686191517795332792, hi := 8927686191517795332792}
lemma t13_contains : t13.Contains (sourcePower false 39 (1/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (1/2) 2 13 coarse_39_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -854490483495713626741, hi := 854490483495713626741}
lemma t14_contains : t14.Contains (sourcePower false 39 (1/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (1/2) 2 14 coarse_39_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -77323625460143770825, hi := 77323625460143770825}
lemma t15_contains : t15.Contains (sourcePower false 39 (1/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (1/2) 2 15 coarse_39_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -6634429492819200158, hi := 6634429492819200158}
lemma t16_contains : t16.Contains (sourcePower false 39 (1/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (1/2) 2 16 coarse_39_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -541162686131840994, hi := 541162686131840994}
lemma t17_contains : t17.Contains (sourcePower false 39 (1/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (1/2) 2 17 coarse_39_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -42067734326804533, hi := 42067734326804533}
lemma t18_contains : t18.Contains (sourcePower false 39 (1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (1/2) 2 18 coarse_39_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -3123688754100502, hi := 3123688754100502}
lemma t19_contains : t19.Contains (sourcePower false 39 (1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (1/2) 2 19 coarse_39_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -222043209846211, hi := 222043209846211}
lemma t20_contains : t20.Contains (sourcePower false 39 (1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (1/2) 2 20 coarse_39_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -15141964192164, hi := 15141964192164}
lemma t21_contains : t21.Contains (sourcePower false 39 (1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (1/2) 2 21 coarse_39_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -992687705435, hi := 992687705435}
lemma t22_contains : t22.Contains (sourcePower false 39 (1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (1/2) 2 22 coarse_39_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -62696548386, hi := 62696548386}
lemma t23_contains : t23.Contains (sourcePower false 39 (1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (1/2) 2 23 coarse_39_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -3823067150, hi := 3823067150}
lemma t24_contains : t24.Contains (sourcePower false 39 (1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (1/2) 2 24 coarse_39_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -225576575, hi := 225576575}
lemma t25_contains : t25.Contains (sourcePower false 39 (1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (1/2) 2 25 coarse_39_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -12909895, hi := 12909895}
lemma t26_contains : t26.Contains (sourcePower false 39 (1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (1/2) 2 26 coarse_39_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -718457, hi := 718457}
lemma t27_contains : t27.Contains (sourcePower false 39 (1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (1/2) 2 27 coarse_39_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -38986, hi := 38986}
lemma t28_contains : t28.Contains (sourcePower false 39 (1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (1/2) 2 28 coarse_39_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 39 (1/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (1/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 29769963946646971299750265757, hi := 29769963946807468726307875557}
lemma t0_checked : ((hm39_1_0_2.realAnswer).add hm39_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 39 (1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_1_0_2.realContains hm39_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -12296933026537218292621506128, hi := -12296933026475355477507045445}
lemma t1_checked : ((hm39_1_0_3.realAnswer).add hm39_0_1_3.realAnswer).scale (1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 39 (1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_1_0_3.realContains hm39_0_1_3.realContains) (1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -9495604786681813868655921189, hi := -9495604786663657306139193846}
lemma t2_checked : ((hm39_1_0_4.realAnswer).add hm39_0_1_4.realAnswer).scale (1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 39 (1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_1_0_4.realContains hm39_0_1_4.realContains) (1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 2504882474170811304292495715, hi := 2504882474175102949903001121}
lemma t3_checked : ((hm39_1_0_5.realAnswer).add hm39_0_1_5.realAnswer).scale (1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 39 (1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_1_0_5.realContains hm39_0_1_5.realContains) (1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr4 : RBox := {lo := -950984512557742813967069481, hi := 950984512557742813967069481}
lemma tr4_contains : tr4.Contains (fullMoment false true 39 6) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 6 39 mixed_39_6) <;> norm_num [tr4,precision]
noncomputable def t4 : RBox := {lo := 1251528494534060489025431933, hi := 1370401558604626812243373675}
lemma t4_checked : ((hm39_1_0_6.realAnswer).add tr4).scale (1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 39 (1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_1_0_6.realContains tr4_contains) (1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr5 : RBox := {lo := -557658605426100677627684034, hi := 557658605426100677627684034}
lemma tr5_contains : tr5.Contains (fullMoment false true 39 7) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 7 39 mixed_39_7) <;> norm_num [tr5,precision]
noncomputable def t5 : RBox := {lo := -151558159737823685202371908, hi := -116704496898548220211523354}
lemma t5_checked : ((hm39_1_0_7.realAnswer).add tr5).scale (1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 39 (1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_1_0_7.realContains tr5_contains) (1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr6 : RBox := {lo := -286484792976969139723090417, hi := 286484792976969139723090417}
lemma tr6_contains : tr6.Contains (fullMoment false true 39 8) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 8 39 mixed_39_8) <;> norm_num [tr6,precision]
noncomputable def t6 : RBox := {lo := -81070328091693104131223742, hi := -72117678311141332899686244}
lemma t6_checked : ((hm39_1_0_8.realAnswer).add tr6).scale (1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 39 (1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_1_0_8.realContains tr6_contains) (1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr7 : RBox := {lo := -130964293330677630666136863, hi := 130964293330677630666136863}
lemma tr7_contains : tr7.Contains (fullMoment false true 39 9) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 9 39 mixed_39_9) <;> norm_num [tr7,precision]
noncomputable def t7 : RBox := {lo := 2567828230349949894627143, hi := 4614145313644640290828928}
lemma t7_checked : ((hm39_1_0_9.realAnswer).add tr7).scale (1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 39 (1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_1_0_9.realContains tr7_contains) (1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -53934136505805891769016377, hi := 53934136505805891769016377}
lemma tr8_contains : tr8.Contains (fullMoment false true 39 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 10 39 mixed_39_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := 2271153018901614800119361, hi := 2692513460353564877989645}
lemma t8_checked : ((hm39_1_0_10.realAnswer).add tr8).scale (1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 39 (1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_1_0_10.realContains tr8_contains) (1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -20209267537129097201365382, hi := 20209267537129097201365382}
lemma tr9_contains : tr9.Contains (fullMoment false true 39 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 11 39 mixed_39_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -98560922649690163797214, hi := -19618471332742369529931}
lemma t9_checked : ((hm39_1_0_11.realAnswer).add tr9).scale (1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 39 (1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_1_0_11.realContains tr9_contains) (1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -6946632271962133634215599, hi := 6946632271962133634215599}
lemma tr10_contains : tr10.Contains (fullMoment false true 39 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 12 39 mixed_39_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -58314988478651022560092, hi := -44747347322471246604929}
lemma t10_checked : ((hm39_1_0_12.realAnswer).add tr10).scale (1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 39 (1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_1_0_12.realContains tr10_contains) (1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -812916126211309011353084, hi := 812916126211309011353084}
lemma t11_contains : t11.Contains (sourcePower true 39 (1/2) 2 11) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (1/2) 2 11 coarse_39_13) <;> norm_num [t11,precision]
noncomputable def t12 : RBox := {lo := -87908302074304336339431, hi := 87908302074304336339431}
lemma t12_contains : t12.Contains (sourcePower true 39 (1/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (1/2) 2 12 coarse_39_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -8927686191517795332792, hi := 8927686191517795332792}
lemma t13_contains : t13.Contains (sourcePower true 39 (1/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (1/2) 2 13 coarse_39_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -854490483495713626741, hi := 854490483495713626741}
lemma t14_contains : t14.Contains (sourcePower true 39 (1/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (1/2) 2 14 coarse_39_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -77323625460143770825, hi := 77323625460143770825}
lemma t15_contains : t15.Contains (sourcePower true 39 (1/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (1/2) 2 15 coarse_39_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -6634429492819200158, hi := 6634429492819200158}
lemma t16_contains : t16.Contains (sourcePower true 39 (1/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (1/2) 2 16 coarse_39_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -541162686131840994, hi := 541162686131840994}
lemma t17_contains : t17.Contains (sourcePower true 39 (1/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (1/2) 2 17 coarse_39_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -42067734326804533, hi := 42067734326804533}
lemma t18_contains : t18.Contains (sourcePower true 39 (1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (1/2) 2 18 coarse_39_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -3123688754100502, hi := 3123688754100502}
lemma t19_contains : t19.Contains (sourcePower true 39 (1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (1/2) 2 19 coarse_39_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -222043209846211, hi := 222043209846211}
lemma t20_contains : t20.Contains (sourcePower true 39 (1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (1/2) 2 20 coarse_39_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -15141964192164, hi := 15141964192164}
lemma t21_contains : t21.Contains (sourcePower true 39 (1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (1/2) 2 21 coarse_39_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -992687705435, hi := 992687705435}
lemma t22_contains : t22.Contains (sourcePower true 39 (1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (1/2) 2 22 coarse_39_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -62696548386, hi := 62696548386}
lemma t23_contains : t23.Contains (sourcePower true 39 (1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (1/2) 2 23 coarse_39_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -3823067150, hi := 3823067150}
lemma t24_contains : t24.Contains (sourcePower true 39 (1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (1/2) 2 24 coarse_39_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -225576575, hi := 225576575}
lemma t25_contains : t25.Contains (sourcePower true 39 (1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (1/2) 2 25 coarse_39_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -12909895, hi := 12909895}
lemma t26_contains : t26.Contains (sourcePower true 39 (1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (1/2) 2 26 coarse_39_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -718457, hi := 718457}
lemma t27_contains : t27.Contains (sourcePower true 39 (1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (1/2) 2 27 coarse_39_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -38986, hi := 38986}
lemma t28_contains : t28.Contains (sourcePower true 39 (1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (1/2) 2 28 coarse_39_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 39 (1/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (1/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 27724996064324143733931502505, hi := 27724996064551861453911962360}
lemma t0_checked : ((hm39_0_0_2.realAnswer).add hm39_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 39 (-1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_0_0_2.realContains hm39_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 23014751421466179036903737948, hi := 23014751421639524512604496083}
lemma t1_checked : ((hm39_0_0_3.realAnswer).add hm39_1_1_3.realAnswer).scale (1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 39 (-1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_0_0_3.realContains hm39_1_1_3.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -35279145212855426410030056353, hi := -35279145212754186126562742182}
lemma t2_checked : ((hm39_0_0_4.realAnswer).add hm39_1_1_4.realAnswer).scale (-1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 39 (-1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_0_0_4.realContains hm39_1_1_4.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -18800714309020119574826968806, hi := -18800714308972356173875532676}
lemma t3_checked : ((hm39_0_0_5.realAnswer).add hm39_1_1_5.realAnswer).scale (1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 39 (-1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_0_0_5.realContains hm39_1_1_5.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr4 : RBox := {lo := -950984512557742813967069481, hi := 950984512557742813967069481}
lemma tr4_contains : tr4.Contains (fullMoment true true 39 6) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 6 39 mixed_39_6) <;> norm_num [tr4,precision]
noncomputable def t4 : RBox := {lo := 18513690619332493117268634054, hi := 20415659644466851874147653927}
lemma t4_checked : ((hm39_0_0_6.realAnswer).add tr4).scale (-1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 39 (-1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_0_0_6.realContains tr4_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr5 : RBox := {lo := -557658605426100677627684034, hi := 557658605426100677627684034}
lemma tr5_contains : tr5.Contains (fullMoment true true 39 7) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 7 39 mixed_39_7) <;> norm_num [tr5,precision]
noncomputable def t5 : RBox := {lo := 3509479980320306624357874030, hi := 4624797191178921676946067036}
lemma t5_checked : ((hm39_0_0_7.realAnswer).add tr5).scale (1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 39 (-1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_0_0_7.realContains tr5_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr6 : RBox := {lo := -286484792976969139723090417, hi := 286484792976969139723090417}
lemma tr6_contains : tr6.Contains (fullMoment true true 39 8) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 8 39 mixed_39_8) <;> norm_num [tr6,precision]
noncomputable def t6 : RBox := {lo := -4835742245894424050859500763, hi := -4262772659938573378380408351}
lemma t6_checked : ((hm39_0_0_8.realAnswer).add tr6).scale (-1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 39 (-1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_0_0_8.realContains tr6_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr7 : RBox := {lo := -130964293330677630666136863, hi := 130964293330677630666136863}
lemma tr7_contains : tr7.Contains (fullMoment true true 39 9) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 9 39 mixed_39_9) <;> norm_num [tr7,precision]
noncomputable def t7 : RBox := {lo := -575758039383966235308148074, hi := -313829452722102827346666063}
lemma t7_checked : ((hm39_0_0_9.realAnswer).add tr7).scale (1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 39 (-1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_0_0_9.realContains tr7_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -53934136505805891769016377, hi := 53934136505805891769016377}
lemma tr8_contains : tr8.Contains (fullMoment true true 39 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 10 39 mixed_39_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := 535879817195224913637782713, hi := 643748090206958512266274783}
lemma t8_checked : ((hm39_0_0_10.realAnswer).add tr8).scale (-1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 39 (-1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_0_0_10.realContains tr8_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -20209267537129097201365382, hi := 20209267537129097201365382}
lemma tr9_contains : tr9.Contains (fullMoment true true 39 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 11 39 mixed_39_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := 10162574531249811974279223, hi := 50581109605534617583516986}
lemma t9_checked : ((hm39_0_0_11.realAnswer).add tr9).scale (1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 39 (-1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_0_0_11.realContains tr9_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -6946632271962133634215599, hi := 6946632271962133634215599}
lemma tr10_contains : tr10.Contains (fullMoment true true 39 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 12 39 mixed_39_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -55944476826259793053586291, hi := -42051212282330183985627719}
lemma t10_checked : ((hm39_0_0_12.realAnswer).add tr10).scale (-1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 39 (-1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_0_0_12.realContains tr10_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -1664852226480760855251115215, hi := 1664852226480760855251115215}
lemma t11_contains : t11.Contains (sourcePower false 39 (-1/1) 2 11) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (-1/1) 2 11 coarse_39_13) <;> norm_num [t11,precision]
noncomputable def t12 : RBox := {lo := -360072405296350561646305502, hi := 360072405296350561646305502}
lemma t12_contains : t12.Contains (sourcePower false 39 (-1/1) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (-1/1) 2 12 coarse_39_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -73135605280913779366227181, hi := 73135605280913779366227181}
lemma t13_contains : t13.Contains (sourcePower false 39 (-1/1) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (-1/1) 2 13 coarse_39_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -13999972081593772060522585, hi := 13999972081593772060522585}
lemma t14_contains : t14.Contains (sourcePower false 39 (-1/1) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (-1/1) 2 14 coarse_39_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -2533740559077991082380588, hi := 2533740559077991082380588}
lemma t15_contains : t15.Contains (sourcePower false 39 (-1/1) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (-1/1) 2 15 coarse_39_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -434793971241399101497012, hi := 434793971241399101497012}
lemma t16_contains : t16.Contains (sourcePower false 39 (-1/1) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (-1/1) 2 16 coarse_39_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -70931275596672662697091, hi := 70931275596672662697091}
lemma t17_contains : t17.Contains (sourcePower false 39 (-1/1) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (-1/1) 2 17 coarse_39_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -11027804147365847283637, hi := 11027804147365847283637}
lemma t18_contains : t18.Contains (sourcePower false 39 (-1/1) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (-1/1) 2 18 coarse_39_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -1637712529509843641519, hi := 1637712529509843641519}
lemma t19_contains : t19.Contains (sourcePower false 39 (-1/1) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (-1/1) 2 19 coarse_39_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -232829180807700478412, hi := 232829180807700478412}
lemma t20_contains : t20.Contains (sourcePower false 39 (-1/1) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (-1/1) 2 20 coarse_39_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -31755000489523633449, hi := 31755000489523633449}
lemma t21_contains : t21.Contains (sourcePower false 39 (-1/1) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (-1/1) 2 21 coarse_39_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -4163634013653937202, hi := 4163634013653937202}
lemma t22_contains : t22.Contains (sourcePower false 39 (-1/1) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (-1/1) 2 22 coarse_39_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -525936767355968363, hi := 525936767355968363}
lemma t23_contains : t23.Contains (sourcePower false 39 (-1/1) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (-1/1) 2 23 coarse_39_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -64140423352441557, hi := 64140423352441557}
lemma t24_contains : t24.Contains (sourcePower false 39 (-1/1) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (-1/1) 2 24 coarse_39_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -7569093846066644, hi := 7569093846066644}
lemma t25_contains : t25.Contains (sourcePower false 39 (-1/1) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (-1/1) 2 25 coarse_39_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -866368337543320, hi := 866368337543320}
lemma t26_contains : t26.Contains (sourcePower false 39 (-1/1) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (-1/1) 2 26 coarse_39_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -96429547209064, hi := 96429547209064}
lemma t27_contains : t27.Contains (sourcePower false 39 (-1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (-1/1) 2 27 coarse_39_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -10465115562657, hi := 10465115562657}
lemma t28_contains : t28.Contains (sourcePower false 39 (-1/1) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 39 (-1/1) 2 28 coarse_39_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 39 (-1/1) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 39 (-1/1) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 29769963946646971299750265757, hi := 29769963946807468726307875557}
lemma t0_checked : ((hm39_1_0_2.realAnswer).add hm39_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 39 (-1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_1_0_2.realContains hm39_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 24593866052950710955014090891, hi := 24593866053074436585243012255}
lemma t1_checked : ((hm39_1_0_3.realAnswer).add hm39_0_1_3.realAnswer).scale (-1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 39 (-1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_1_0_3.realContains hm39_0_1_3.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -37982419146727255474623684755, hi := -37982419146654629224556775387}
lemma t2_checked : ((hm39_1_0_4.realAnswer).add hm39_0_1_4.realAnswer).scale (1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 39 (-1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_1_0_4.realContains hm39_0_1_4.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -20039059793400823599224008965, hi := -20039059793366490434339965722}
lemma t3_checked : ((hm39_1_0_5.realAnswer).add hm39_0_1_5.realAnswer).scale (-1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 39 (-1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_1_0_5.realContains hm39_0_1_5.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr4 : RBox := {lo := -950984512557742813967069481, hi := 950984512557742813967069481}
lemma tr4_contains : tr4.Contains (fullMoment false true 39 6) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 6 39 mixed_39_6) <;> norm_num [tr4,precision]
noncomputable def t4 : RBox := {lo := 20024455912544967824406910940, hi := 21926424937674028995893978800}
lemma t4_checked : ((hm39_1_0_6.realAnswer).add tr4).scale (1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 39 (-1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_1_0_6.realContains tr4_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr5 : RBox := {lo := -557658605426100677627684034, hi := 557658605426100677627684034}
lemma tr5_contains : tr5.Contains (fullMoment false true 39 7) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 7 39 mixed_39_7) <;> norm_num [tr5,precision]
noncomputable def t5 : RBox := {lo := 3734543900753543046768747349, hi := 4849861111610357926475901041}
lemma t5_checked : ((hm39_1_0_7.realAnswer).add tr5).scale (-1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 39 (-1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_1_0_7.realContains tr5_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr6 : RBox := {lo := -286484792976969139723090417, hi := 286484792976969139723090417}
lemma tr6_contains : tr6.Contains (fullMoment false true 39 8) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 8 39 mixed_39_8) <;> norm_num [tr6,precision]
noncomputable def t6 : RBox := {lo := -5188500997868358664398319444, hi := -4615531411913045305579919655}
lemma t6_checked : ((hm39_1_0_8.realAnswer).add tr6).scale (1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 39 (-1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_1_0_8.realContains tr6_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr7 : RBox := {lo := -130964293330677630666136863, hi := 130964293330677630666136863}
lemma tr7_contains : tr7.Contains (fullMoment false true 39 9) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 9 39 mixed_39_9) <;> norm_num [tr7,precision]
noncomputable def t7 : RBox := {lo := -590610600146513957226102674, hi := -328682013484793586512274350}
lemma t7_checked : ((hm39_1_0_9.realAnswer).add tr7).scale (-1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 39 (-1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_1_0_9.realContains tr7_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -53934136505805891769016377, hi := 53934136505805891769016377}
lemma tr8_contains : tr8.Contains (fullMoment false true 39 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 10 39 mixed_39_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := 581415172838813388830556472, hi := 689283445850512608765349102}
lemma t8_checked : ((hm39_1_0_10.realAnswer).add tr8).scale (1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 39 (-1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_1_0_10.realContains tr8_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -20209267537129097201365382, hi := 20209267537129097201365382}
lemma tr9_contains : tr9.Contains (fullMoment false true 39 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 11 39 mixed_39_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := 10044657322364093199324825, hi := 50463192396641363864173144}
lemma t9_checked : ((hm39_1_0_11.realAnswer).add tr9).scale (-1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 39 (-1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_1_0_11.realContains tr9_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -6946632271962133634215599, hi := 6946632271962133634215599}
lemma tr10_contains : tr10.Contains (fullMoment false true 39 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 12 39 mixed_39_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -59714548202138647101533629, hi := -45821283658210556523447973}
lemma t10_checked : ((hm39_1_0_12.realAnswer).add tr10).scale (1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 39 (-1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm39_1_0_12.realContains tr10_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -1664852226480760855251115215, hi := 1664852226480760855251115215}
lemma t11_contains : t11.Contains (sourcePower true 39 (-1/1) 2 11) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (-1/1) 2 11 coarse_39_13) <;> norm_num [t11,precision]
noncomputable def t12 : RBox := {lo := -360072405296350561646305502, hi := 360072405296350561646305502}
lemma t12_contains : t12.Contains (sourcePower true 39 (-1/1) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (-1/1) 2 12 coarse_39_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -73135605280913779366227181, hi := 73135605280913779366227181}
lemma t13_contains : t13.Contains (sourcePower true 39 (-1/1) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (-1/1) 2 13 coarse_39_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -13999972081593772060522585, hi := 13999972081593772060522585}
lemma t14_contains : t14.Contains (sourcePower true 39 (-1/1) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (-1/1) 2 14 coarse_39_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -2533740559077991082380588, hi := 2533740559077991082380588}
lemma t15_contains : t15.Contains (sourcePower true 39 (-1/1) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (-1/1) 2 15 coarse_39_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -434793971241399101497012, hi := 434793971241399101497012}
lemma t16_contains : t16.Contains (sourcePower true 39 (-1/1) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (-1/1) 2 16 coarse_39_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -70931275596672662697091, hi := 70931275596672662697091}
lemma t17_contains : t17.Contains (sourcePower true 39 (-1/1) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (-1/1) 2 17 coarse_39_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -11027804147365847283637, hi := 11027804147365847283637}
lemma t18_contains : t18.Contains (sourcePower true 39 (-1/1) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (-1/1) 2 18 coarse_39_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -1637712529509843641519, hi := 1637712529509843641519}
lemma t19_contains : t19.Contains (sourcePower true 39 (-1/1) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (-1/1) 2 19 coarse_39_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -232829180807700478412, hi := 232829180807700478412}
lemma t20_contains : t20.Contains (sourcePower true 39 (-1/1) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (-1/1) 2 20 coarse_39_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -31755000489523633449, hi := 31755000489523633449}
lemma t21_contains : t21.Contains (sourcePower true 39 (-1/1) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (-1/1) 2 21 coarse_39_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -4163634013653937202, hi := 4163634013653937202}
lemma t22_contains : t22.Contains (sourcePower true 39 (-1/1) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (-1/1) 2 22 coarse_39_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -525936767355968363, hi := 525936767355968363}
lemma t23_contains : t23.Contains (sourcePower true 39 (-1/1) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (-1/1) 2 23 coarse_39_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -64140423352441557, hi := 64140423352441557}
lemma t24_contains : t24.Contains (sourcePower true 39 (-1/1) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (-1/1) 2 24 coarse_39_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -7569093846066644, hi := 7569093846066644}
lemma t25_contains : t25.Contains (sourcePower true 39 (-1/1) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (-1/1) 2 25 coarse_39_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -866368337543320, hi := 866368337543320}
lemma t26_contains : t26.Contains (sourcePower true 39 (-1/1) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (-1/1) 2 26 coarse_39_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -96429547209064, hi := 96429547209064}
lemma t27_contains : t27.Contains (sourcePower true 39 (-1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (-1/1) 2 27 coarse_39_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -10465115562657, hi := 10465115562657}
lemma t28_contains : t28.Contains (sourcePower true 39 (-1/1) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 39 (-1/1) 2 28 coarse_39_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 39 (-1/1) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 39 (-1/1) 2) k.val := by
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
end SharpPlanar.Bernstein39

end OAI
