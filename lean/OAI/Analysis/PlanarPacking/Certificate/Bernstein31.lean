import OAI.Analysis.PlanarPacking.Certificate.LowBlock31_0
import OAI.Analysis.PlanarPacking.Certificate.LowBlock31_1
import OAI.Analysis.PlanarPacking.Certificate.LowBlock31_10
import OAI.Analysis.PlanarPacking.Certificate.MixedBound31
import OAI.Analysis.PlanarPacking.Certificate.CoarseBound31

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein31
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 396427817358115097325289800663, hi := 396427817358291435691510236148}
lemma t0_checked : ((hm31_0_0_2.realAnswer).add hm31_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 31 (1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_0_0_2.realContains hm31_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -88217117868090127536194025242, hi := -88217117867954057736117572392}
lemma t1_checked : ((hm31_0_0_3.realAnswer).add hm31_1_1_3.realAnswer).scale (-1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 31 (1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_0_0_3.realContains hm31_1_1_3.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -254756789813020923967088303435, hi := -254756789812941007092650859716}
lemma t2_checked : ((hm31_0_0_4.realAnswer).add hm31_1_1_4.realAnswer).scale (-1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 31 (1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_0_0_4.realContains hm31_1_1_4.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 37012221145507912524956559054, hi := 37012221145545702383756043696}
lemma t3_checked : ((hm31_0_0_5.realAnswer).add hm31_1_1_5.realAnswer).scale (-1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 31 (1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_0_0_5.realContains hm31_1_1_5.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 70023235008623339743378908236, hi := 70023235008638282866359242167}
lemma t4_checked : ((hm31_0_0_6.realAnswer).add hm31_1_1_6.realAnswer).scale (-1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 31 (1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_0_0_6.realContains hm31_1_1_6.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -6113201029827714522699659362, hi := -6113201029822637238183758730}
lemma t5_checked : ((hm31_0_0_7.realAnswer).add hm31_1_1_7.realAnswer).scale (-1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 31 (1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_0_0_7.realContains hm31_1_1_7.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr6 : RBox := {lo := -1595574541314512198583916129, hi := 1595574541314512198583916129}
lemma tr6_contains : tr6.Contains (fullMoment true true 31 8) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 8 31 mixed_31_8) <;> norm_num [tr6,precision]
noncomputable def t6 : RBox := {lo := -12426989432135384731531185053, hi := -9235840349504847671181159701}
lemma t6_checked : ((hm31_0_0_8.realAnswer).add tr6).scale (-1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 31 (1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_0_0_8.realContains tr6_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr7 : RBox := {lo := -730532592140359898388862477, hi := 730532592140359898388862477}
lemma tr7_contains : tr7.Contains (fullMoment true true 31 9) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 9 31 mixed_31_9) <;> norm_num [tr7,precision]
noncomputable def t7 : RBox := {lo := -133602055107308959007806168, hi := 1327463129173812219596153184}
lemma t7_checked : ((hm31_0_0_9.realAnswer).add tr7).scale (-1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 31 (1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_0_0_9.realContains tr7_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -301261453327846246821723796, hi := 301261453327846246821723796}
lemma tr8_contains : tr8.Contains (fullMoment true true 31 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 10 31 mixed_31_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := 775423127211655802478209831, hi := 1377946033867444335569661335}
lemma t8_checked : ((hm31_0_0_10.realAnswer).add tr8).scale (-1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 31 (1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_0_0_10.realContains tr8_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -113019595441228187975959620, hi := 113019595441228187975959620}
lemma tr9_contains : tr9.Contains (fullMoment true true 31 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 11 31 mixed_31_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -150717377729198793039746676, hi := 75321813153278513163462827}
lemma t9_checked : ((hm31_0_0_11.realAnswer).add tr9).scale (-1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 31 (1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_0_0_11.realContains tr9_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -38890056305794465335597165, hi := 38890056305794465335597165}
lemma tr10_contains : tr10.Contains (fullMoment true true 31 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 12 31 mixed_31_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -113805918366965769537442860, hi := -36025805755372649558015392}
lemma t10_checked : ((hm31_0_0_12.realAnswer).add tr10).scale (-1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 31 (1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_0_0_12.realContains tr10_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -12359268881528133451052428, hi := 12359268881528133451052428}
lemma tr11_contains : tr11.Contains (fullMoment true true 31 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 13 31 mixed_31_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := -10631773177397223151575126, hi := 14086764585659819349267152}
lemma t11_checked : ((hm31_0_0_13.realAnswer).add tr11).scale (-1) 1=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 31 (1/1) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_0_0_13.realContains tr11_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -363070699164326615018086872, hi := 363070699164326615018086872}
lemma t12_contains : t12.Contains (sourcePower false 31 (1/1) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (1/1) 2 12 coarse_31_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -73962271777329974046821796, hi := 73962271777329974046821796}
lemma t13_contains : t13.Contains (sourcePower false 31 (1/1) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (1/1) 2 13 coarse_31_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -14213721997609591849798918, hi := 14213721997609591849798918}
lemma t14_contains : t14.Contains (sourcePower false 31 (1/1) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (1/1) 2 14 coarse_31_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -2585773992524154980080041, hi := 2585773992524154980080041}
lemma t15_contains : t15.Contains (sourcePower false 31 (1/1) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (1/1) 2 15 coarse_31_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -446759975292680258207762, hi := 446759975292680258207762}
lemma t16_contains : t16.Contains (sourcePower false 31 (1/1) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (1/1) 2 16 coarse_31_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -73538835195571904113332, hi := 73538835195571904113332}
lemma t17_contains : t17.Contains (sourcePower false 31 (1/1) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (1/1) 2 17 coarse_31_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -11567724912324847730582, hi := 11567724912324847730582}
lemma t18_contains : t18.Contains (sourcePower false 31 (1/1) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (1/1) 2 18 coarse_31_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -1744203475531886507303, hi := 1744203475531886507303}
lemma t19_contains : t19.Contains (sourcePower false 31 (1/1) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (1/1) 2 19 coarse_31_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -252881220492250857440, hi := 252881220492250857440}
lemma t20_contains : t20.Contains (sourcePower false 31 (1/1) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (1/1) 2 20 coarse_31_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -35367081633198004494, hi := 35367081633198004494}
lemma t21_contains : t21.Contains (sourcePower false 31 (1/1) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (1/1) 2 21 coarse_31_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -4787259615656135378, hi := 4787259615656135378}
lemma t22_contains : t22.Contains (sourcePower false 31 (1/1) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (1/1) 2 22 coarse_31_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -629309525621986588, hi := 629309525621986588}
lemma t23_contains : t23.Contains (sourcePower false 31 (1/1) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (1/1) 2 23 coarse_31_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -80618018826638037, hi := 80618018826638037}
lemma t24_contains : t24.Contains (sourcePower false 31 (1/1) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (1/1) 2 24 coarse_31_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -10098538453300210, hi := 10098538453300210}
lemma t25_contains : t25.Contains (sourcePower false 31 (1/1) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (1/1) 2 25 coarse_31_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -1240816760230138, hi := 1240816760230138}
lemma t26_contains : t26.Contains (sourcePower false 31 (1/1) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (1/1) 2 26 coarse_31_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -149953099101626, hi := 149953099101626}
lemma t27_contains : t27.Contains (sourcePower false 31 (1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (1/1) 2 27 coarse_31_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -17861124354033, hi := 17861124354033}
lemma t28_contains : t28.Contains (sourcePower false 31 (1/1) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (1/1) 2 28 coarse_31_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 31 (1/1) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (1/1) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 410384815005698034344155213549, hi := 410384815005840965527488845717}
lemma t0_checked : ((hm31_1_0_2.realAnswer).add hm31_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 31 (1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_1_0_2.realContains hm31_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -89299770091835364755824532919, hi := -89299770091724946366337383644}
lemma t1_checked : ((hm31_1_0_3.realAnswer).add hm31_0_1_3.realAnswer).scale (1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 31 (1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_1_0_3.realContains hm31_0_1_3.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -264193115054059525768340347339, hi := -264193115053994642098939833641}
lemma t2_checked : ((hm31_1_0_4.realAnswer).add hm31_0_1_4.realAnswer).scale (1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 31 (1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_1_0_4.realContains hm31_0_1_4.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 37023094851742236318780283718, hi := 37023094851772924420821480994}
lemma t3_checked : ((hm31_1_0_5.realAnswer).add hm31_0_1_5.realAnswer).scale (1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 31 (1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_1_0_5.realContains hm31_0_1_5.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 72686748275000481334929150156, hi := 72686748275012617375237311163}
lemma t4_checked : ((hm31_1_0_6.realAnswer).add hm31_0_1_6.realAnswer).scale (1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 31 (1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_1_0_6.realContains hm31_0_1_6.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -5975206155344995310243668287, hi := -5975206155340871717246398124}
lemma t5_checked : ((hm31_1_0_7.realAnswer).add hm31_0_1_7.realAnswer).scale (1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 31 (1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_1_0_7.realContains hm31_0_1_7.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr6 : RBox := {lo := -1595574541314512198583916129, hi := 1595574541314512198583916129}
lemma tr6_contains : tr6.Contains (fullMoment false true 31 8) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 8 31 mixed_31_8) <;> norm_num [tr6,precision]
noncomputable def t6 : RBox := {lo := -12846268396986379028540237134, hi := -9655119314356126195443103514}
lemma t6_checked : ((hm31_1_0_8.realAnswer).add tr6).scale (1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 31 (1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_1_0_8.realContains tr6_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr7 : RBox := {lo := -730532592140359898388862477, hi := 730532592140359898388862477}
lemma tr7_contains : tr7.Contains (fullMoment false true 31 9) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 9 31 mixed_31_9) <;> norm_num [tr7,precision]
noncomputable def t7 : RBox := {lo := -171140162084975839289290726, hi := 1289925022196069888874047314}
lemma t7_checked : ((hm31_1_0_9.realAnswer).add tr7).scale (1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 31 (1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_1_0_9.realContains tr7_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -301261453327846246821723796, hi := 301261453327846246821723796}
lemma tr8_contains : tr8.Contains (fullMoment false true 31 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 10 31 mixed_31_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := 817306530861319695703099649, hi := 1419829437517090164562225539}
lemma t8_checked : ((hm31_1_0_10.realAnswer).add tr8).scale (1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 31 (1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_1_0_10.realContains tr8_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -113019595441228187975959620, hi := 113019595441228187975959620}
lemma tr9_contains : tr9.Contains (fullMoment false true 31 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 11 31 mixed_31_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -146209744677340089918116475, hi := 79829446205133276313086420}
lemma t9_checked : ((hm31_1_0_11.realAnswer).add tr9).scale (1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 31 (1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_1_0_11.realContains tr9_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -38890056305794465335597165, hi := 38890056305794465335597165}
lemma tr10_contains : tr10.Contains (fullMoment false true 31 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 12 31 mixed_31_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -116730932096266323117801739, hi := -38950819484673992514511785}
lemma t10_checked : ((hm31_1_0_12.realAnswer).add tr10).scale (1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 31 (1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_1_0_12.realContains tr10_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -12359268881528133451052428, hi := 12359268881528133451052428}
lemma tr11_contains : tr11.Contains (fullMoment false true 31 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 13 31 mixed_31_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := -10977853565005649380164083, hi := 13740684198051246829061020}
lemma t11_checked : ((hm31_1_0_13.realAnswer).add tr11).scale (1) 1=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 31 (1/1) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_1_0_13.realContains tr11_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -363070699164326615018086872, hi := 363070699164326615018086872}
lemma t12_contains : t12.Contains (sourcePower true 31 (1/1) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (1/1) 2 12 coarse_31_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -73962271777329974046821796, hi := 73962271777329974046821796}
lemma t13_contains : t13.Contains (sourcePower true 31 (1/1) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (1/1) 2 13 coarse_31_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -14213721997609591849798918, hi := 14213721997609591849798918}
lemma t14_contains : t14.Contains (sourcePower true 31 (1/1) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (1/1) 2 14 coarse_31_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -2585773992524154980080041, hi := 2585773992524154980080041}
lemma t15_contains : t15.Contains (sourcePower true 31 (1/1) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (1/1) 2 15 coarse_31_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -446759975292680258207762, hi := 446759975292680258207762}
lemma t16_contains : t16.Contains (sourcePower true 31 (1/1) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (1/1) 2 16 coarse_31_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -73538835195571904113332, hi := 73538835195571904113332}
lemma t17_contains : t17.Contains (sourcePower true 31 (1/1) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (1/1) 2 17 coarse_31_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -11567724912324847730582, hi := 11567724912324847730582}
lemma t18_contains : t18.Contains (sourcePower true 31 (1/1) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (1/1) 2 18 coarse_31_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -1744203475531886507303, hi := 1744203475531886507303}
lemma t19_contains : t19.Contains (sourcePower true 31 (1/1) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (1/1) 2 19 coarse_31_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -252881220492250857440, hi := 252881220492250857440}
lemma t20_contains : t20.Contains (sourcePower true 31 (1/1) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (1/1) 2 20 coarse_31_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -35367081633198004494, hi := 35367081633198004494}
lemma t21_contains : t21.Contains (sourcePower true 31 (1/1) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (1/1) 2 21 coarse_31_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -4787259615656135378, hi := 4787259615656135378}
lemma t22_contains : t22.Contains (sourcePower true 31 (1/1) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (1/1) 2 22 coarse_31_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -629309525621986588, hi := 629309525621986588}
lemma t23_contains : t23.Contains (sourcePower true 31 (1/1) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (1/1) 2 23 coarse_31_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -80618018826638037, hi := 80618018826638037}
lemma t24_contains : t24.Contains (sourcePower true 31 (1/1) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (1/1) 2 24 coarse_31_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -10098538453300210, hi := 10098538453300210}
lemma t25_contains : t25.Contains (sourcePower true 31 (1/1) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (1/1) 2 25 coarse_31_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -1240816760230138, hi := 1240816760230138}
lemma t26_contains : t26.Contains (sourcePower true 31 (1/1) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (1/1) 2 26 coarse_31_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -149953099101626, hi := 149953099101626}
lemma t27_contains : t27.Contains (sourcePower true 31 (1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (1/1) 2 27 coarse_31_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -17861124354033, hi := 17861124354033}
lemma t28_contains : t28.Contains (sourcePower true 31 (1/1) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (1/1) 2 28 coarse_31_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 31 (1/1) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (1/1) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 396427817358115097325289800663, hi := 396427817358291435691510236148}
lemma t0_checked : ((hm31_0_0_2.realAnswer).add hm31_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 31 (-3/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_0_0_2.realContains hm31_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 132325676801931086604176358588, hi := 132325676802135191304291037863}
lemma t1_checked : ((hm31_0_0_3.realAnswer).add hm31_1_1_3.realAnswer).scale (3) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 31 (-3/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_0_0_3.realContains hm31_1_1_3.realContains) (3) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -573202777079297078925948682729, hi := -573202777079117265958464434361}
lemma t2_checked : ((hm31_0_0_4.realAnswer).add hm31_1_1_4.realAnswer).scale (-9) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 31 (-3/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_0_0_4.realContains hm31_1_1_4.realContains) (-9) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -124916246366216745545176647474, hi := -124916246366089204771728386807}
lemma t3_checked : ((hm31_0_0_5.realAnswer).add hm31_1_1_5.realAnswer).scale (27) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 31 (-3/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_0_0_5.realContains hm31_1_1_5.realContains) (27) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 354492627231155657450855722944, hi := 354492627231231307010943663471}
lemma t4_checked : ((hm31_0_0_6.realAnswer).add hm31_1_1_6.realAnswer).scale (-81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 31 (-3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_0_0_6.realContains hm31_1_1_6.realContains) (-81) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 46422120320215651527457917855, hi := 46422120320254207156750538281}
lemma t5_checked : ((hm31_0_0_7.realAnswer).add hm31_1_1_7.realAnswer).scale (243) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 31 (-3/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_0_0_7.realContains hm31_1_1_7.realContains) (243) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr6 : RBox := {lo := -1595574541314512198583916129, hi := 1595574541314512198583916129}
lemma tr6_contains : tr6.Contains (fullMoment true true 31 8) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 8 31 mixed_31_8) <;> norm_num [tr6,precision]
noncomputable def t6 : RBox := {lo := -141551176500417116707597404745, hi := -105201993981078655504547897219}
lemma t6_checked : ((hm31_0_0_8.realAnswer).add tr6).scale (-729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 31 (-3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_0_0_8.realContains tr6_contains) (-729) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr7 : RBox := {lo := -730532592140359898388862477, hi := 730532592140359898388862477}
lemma tr7_contains : tr7.Contains (fullMoment true true 31 9) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 9 31 mixed_31_9) <;> norm_num [tr7,precision]
noncomputable def t7 : RBox := {lo := -22680952058618182220756148543, hi := 2282716363435036666797438199}
lemma t7_checked : ((hm31_0_0_9.realAnswer).add tr7).scale (2187) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 31 (-3/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_0_0_9.realContains tr7_contains) (2187) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -301261453327846246821723796, hi := 301261453327846246821723796}
lemma tr8_contains : tr8.Contains (fullMoment true true 31 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 10 31 mixed_31_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := 19873246631389350468982557426, hi := 35315249719548055803408390699}
lemma t8_checked : ((hm31_0_0_10.realAnswer).add tr8).scale (-6561) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 31 (-3/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_0_0_10.realContains tr8_contains) (-6561) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -113019595441228187975959620, hi := 113019595441228187975959620}
lemma tr9_contains : tr9.Contains (fullMoment true true 31 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 11 31 mixed_31_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -2895623531828087841008669578, hi := 5794082316101210631643230125}
lemma t9_checked : ((hm31_0_0_11.realAnswer).add tr9).scale (19683) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 31 (-3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_0_0_11.realContains tr9_contains) (19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -38890056305794465335597165, hi := 38890056305794465335597165}
lemma tr10_contains : tr10.Contains (fullMoment true true 31 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 12 31 mixed_31_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -6562622728174767309977015079, hi := -2077429496141601156007080939}
lemma t10_checked : ((hm31_0_0_12.realAnswer).add tr10).scale (-59049) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 31 (-3/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_0_0_12.realContains tr10_contains) (-59049) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -12359268881528133451052428, hi := 12359268881528133451052428}
lemma tr11_contains : tr11.Contains (fullMoment true true 31 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 13 31 mixed_31_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := -1218470745144472665168275477, hi := 919622423367375922671913499}
lemma t11_checked : ((hm31_0_0_13.realAnswer).add tr11).scale (177147) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 31 (-3/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_0_0_13.realContains tr11_contains) (177147) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -47107093611960180813434351891, hi := 47107093611960180813434351891}
lemma t12_contains : t12.Contains (sourcePower false 31 (-3/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (-3/2) 2 12 coarse_31_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -14394500857769538111847053988, hi := 14394500857769538111847053988}
lemma t13_contains : t13.Contains (sourcePower false 31 (-3/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (-3/2) 2 13 coarse_31_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -4149401348216842768569389712, hi := 4149401348216842768569389712}
lemma t14_contains : t14.Contains (sourcePower false 31 (-3/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (-3/2) 2 14 coarse_31_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -1132294633232049409874126003, hi := 1132294633232049409874126003}
lemma t15_contains : t15.Contains (sourcePower false 31 (-3/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (-3/2) 2 15 coarse_31_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -293450195471052557636680464, hi := 293450195471052557636680464}
lemma t16_contains : t16.Contains (sourcePower false 31 (-3/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (-3/2) 2 16 coarse_31_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -72454964935198155024841805, hi := 72454964935198155024841805}
lemma t17_contains : t17.Contains (sourcePower false 31 (-3/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (-3/2) 2 17 coarse_31_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -17095846718408106363802409, hi := 17095846718408106363802409}
lemma t18_contains : t18.Contains (sourcePower false 31 (-3/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (-3/2) 2 18 coarse_31_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -3866616230427148851881964, hi := 3866616230427148851881964}
lemma t19_contains : t19.Contains (sourcePower false 31 (-3/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (-3/2) 2 19 coarse_31_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -840894980352613288021724, hi := 840894980352613288021724}
lemma t20_contains : t20.Contains (sourcePower false 31 (-3/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (-3/2) 2 20 coarse_31_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -176406939336102112504016, hi := 176406939336102112504016}
lemma t21_contains : t21.Contains (sourcePower false 31 (-3/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (-3/2) 2 21 coarse_31_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -35817451325097945676707, hi := 35817451325097945676707}
lemma t22_contains : t22.Contains (sourcePower false 31 (-3/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (-3/2) 2 22 coarse_31_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -7062578106899883956562, hi := 7062578106899883956562}
lemma t23_contains : t23.Contains (sourcePower false 31 (-3/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (-3/2) 2 23 coarse_31_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -1357132773949141042559, hi := 1357132773949141042559}
lemma t24_contains : t24.Contains (sourcePower false 31 (-3/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (-3/2) 2 24 coarse_31_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -254999894008141724024, hi := 254999894008141724024}
lemma t25_contains : t25.Contains (sourcePower false 31 (-3/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (-3/2) 2 25 coarse_31_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -46998109251959411980, hi := 46998109251959411980}
lemma t26_contains : t26.Contains (sourcePower false 31 (-3/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (-3/2) 2 26 coarse_31_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -8519604618663829526, hi := 8519604618663829526}
lemma t27_contains : t27.Contains (sourcePower false 31 (-3/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (-3/2) 2 27 coarse_31_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -1522173117322706802, hi := 1522173117322706802}
lemma t28_contains : t28.Contains (sourcePower false 31 (-3/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 31 (-3/2) 2 28 coarse_31_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 31 (-3/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 410384815005698034344155213549, hi := 410384815005840965527488845717}
lemma t0_checked : ((hm31_1_0_2.realAnswer).add hm31_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 31 (-3/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_1_0_2.realContains hm31_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 133949655137587419549506075466, hi := 133949655137753047133736799379}
lemma t1_checked : ((hm31_1_0_3.realAnswer).add hm31_0_1_3.realAnswer).scale (-3) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 31 (-3/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_1_0_3.realContains hm31_0_1_3.realContains) (-3) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -594434508871633932978765781513, hi := -594434508871487944722614625692}
lemma t2_checked : ((hm31_1_0_4.realAnswer).add hm31_0_1_4.realAnswer).scale (9) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 31 (-3/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_1_0_4.realContains hm31_0_1_4.realContains) (9) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -124952945124733619920272498355, hi := -124952945124630047575883457548}
lemma t3_checked : ((hm31_1_0_5.realAnswer).add hm31_0_1_5.realAnswer).scale (-27) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 31 (-3/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_1_0_5.realContains hm31_0_1_5.realContains) (-27) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 367976663142189936758078822664, hi := 367976663142251375462138887763}
lemma t4_checked : ((hm31_1_0_6.realAnswer).add hm31_0_1_6.realAnswer).scale (81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 31 (-3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_1_0_6.realContains hm31_0_1_6.realContains) (81) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 45374221742119744602839835754, hi := 45374221742151058137162856055}
lemma t5_checked : ((hm31_1_0_7.realAnswer).add hm31_0_1_7.realAnswer).scale (-243) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 31 (-3/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_1_0_7.realContains hm31_0_1_7.realContains) (-243) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr6 : RBox := {lo := -1595574541314512198583916129, hi := 1595574541314512198583916129}
lemma tr6_contains : tr6.Contains (fullMoment false true 31 8) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 8 31 mixed_31_8) <;> norm_num [tr6,precision]
noncomputable def t6 : RBox := {lo := -146327025959422973621966138605, hi := -109977843440087749944969100964}
lemma t6_checked : ((hm31_1_0_8.realAnswer).add tr6).scale (729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 31 (-3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_1_0_8.realContains tr6_contains) (729) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr7 : RBox := {lo := -730532592140359898388862477, hi := 730532592140359898388862477}
lemma tr7_contains : tr7.Contains (fullMoment false true 31 9) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 9 31 mixed_31_9) <;> norm_num [tr7,precision]
noncomputable def t7 : RBox := {lo := -22039578308928162866933917780, hi := 2924090113123766879106865764}
lemma t7_checked : ((hm31_1_0_9.realAnswer).add tr7).scale (-2187) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 31 (-3/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_1_0_9.realContains tr7_contains) (-2187) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -301261453327846246821723796, hi := 301261453327846246821723796}
lemma tr8_contains : tr8.Contains (fullMoment false true 31 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 10 31 mixed_31_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := 20946672456957494232453268738, hi := 36388675545115736600362350631}
lemma t8_checked : ((hm31_1_0_10.realAnswer).add tr8).scale (6561) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 31 (-3/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_1_0_10.realContains tr8_contains) (6561) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -113019595441228187975959620, hi := 113019595441228187975959620}
lemma tr9_contains : tr9.Contains (fullMoment false true 31 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 11 31 mixed_31_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -3068912089171168511075156260, hi := 5620793758757978495816965972}
lemma t9_checked : ((hm31_1_0_11.realAnswer).add tr9).scale (-19683) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 31 (-3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_1_0_11.realContains tr9_contains) (-19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -38890056305794465335597165, hi := 38890056305794465335597165}
lemma tr10_contains : tr10.Contains (fullMoment false true 31 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 12 31 mixed_31_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -6731293759133232532991284069, hi := -2246100527100111898427154680}
lemma t10_checked : ((hm31_1_0_12.realAnswer).add tr10).scale (59049) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 31 (-3/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_1_0_12.realContains tr10_contains) (59049) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -12359268881528133451052428, hi := 12359268881528133451052428}
lemma tr11_contains : tr11.Contains (fullMoment false true 31 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 13 31 mixed_31_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := -1188535636539152452161949468, hi := 949557531972683481810511139}
lemma t11_checked : ((hm31_1_0_13.realAnswer).add tr11).scale (-177147) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 31 (-3/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_1_0_13.realContains tr11_contains) (-177147) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -47107093611960180813434351891, hi := 47107093611960180813434351891}
lemma t12_contains : t12.Contains (sourcePower true 31 (-3/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (-3/2) 2 12 coarse_31_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -14394500857769538111847053988, hi := 14394500857769538111847053988}
lemma t13_contains : t13.Contains (sourcePower true 31 (-3/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (-3/2) 2 13 coarse_31_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -4149401348216842768569389712, hi := 4149401348216842768569389712}
lemma t14_contains : t14.Contains (sourcePower true 31 (-3/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (-3/2) 2 14 coarse_31_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -1132294633232049409874126003, hi := 1132294633232049409874126003}
lemma t15_contains : t15.Contains (sourcePower true 31 (-3/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (-3/2) 2 15 coarse_31_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -293450195471052557636680464, hi := 293450195471052557636680464}
lemma t16_contains : t16.Contains (sourcePower true 31 (-3/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (-3/2) 2 16 coarse_31_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -72454964935198155024841805, hi := 72454964935198155024841805}
lemma t17_contains : t17.Contains (sourcePower true 31 (-3/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (-3/2) 2 17 coarse_31_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -17095846718408106363802409, hi := 17095846718408106363802409}
lemma t18_contains : t18.Contains (sourcePower true 31 (-3/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (-3/2) 2 18 coarse_31_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -3866616230427148851881964, hi := 3866616230427148851881964}
lemma t19_contains : t19.Contains (sourcePower true 31 (-3/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (-3/2) 2 19 coarse_31_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -840894980352613288021724, hi := 840894980352613288021724}
lemma t20_contains : t20.Contains (sourcePower true 31 (-3/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (-3/2) 2 20 coarse_31_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -176406939336102112504016, hi := 176406939336102112504016}
lemma t21_contains : t21.Contains (sourcePower true 31 (-3/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (-3/2) 2 21 coarse_31_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -35817451325097945676707, hi := 35817451325097945676707}
lemma t22_contains : t22.Contains (sourcePower true 31 (-3/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (-3/2) 2 22 coarse_31_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -7062578106899883956562, hi := 7062578106899883956562}
lemma t23_contains : t23.Contains (sourcePower true 31 (-3/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (-3/2) 2 23 coarse_31_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -1357132773949141042559, hi := 1357132773949141042559}
lemma t24_contains : t24.Contains (sourcePower true 31 (-3/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (-3/2) 2 24 coarse_31_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -254999894008141724024, hi := 254999894008141724024}
lemma t25_contains : t25.Contains (sourcePower true 31 (-3/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (-3/2) 2 25 coarse_31_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -46998109251959411980, hi := 46998109251959411980}
lemma t26_contains : t26.Contains (sourcePower true 31 (-3/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (-3/2) 2 26 coarse_31_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -8519604618663829526, hi := 8519604618663829526}
lemma t27_contains : t27.Contains (sourcePower true 31 (-3/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (-3/2) 2 27 coarse_31_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -1522173117322706802, hi := 1522173117322706802}
lemma t28_contains : t28.Contains (sourcePower true 31 (-3/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (-3/2) 2 28 coarse_31_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 31 (-3/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 31 (-3/2) 2) k.val := by
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
end SharpPlanar.Bernstein31

end OAI
