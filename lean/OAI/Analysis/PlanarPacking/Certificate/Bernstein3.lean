import OAI.Analysis.PlanarPacking.Certificate.HighMoments3_0
import OAI.Analysis.PlanarPacking.Certificate.LowBlock3_1
import OAI.Analysis.PlanarPacking.Certificate.LowBlock3_10
import OAI.Analysis.PlanarPacking.Certificate.LowBlock3_11
import OAI.Analysis.PlanarPacking.Certificate.CoarseBound3

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein3
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 134242755693171941492068971114, hi := 134242755693383098939399762064}
lemma t0_checked : ((hm3_0_0_2.realAnswer).add hm3_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 3 (1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_0_0_2.realContains hm3_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -137916843240331210161755586204, hi := -137916843240239936221490871463}
lemma t1_checked : ((hm3_0_0_3.realAnswer).add hm3_1_1_3.realAnswer).scale (-1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 3 (1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_0_0_3.realContains hm3_1_1_3.realContains) (-1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := 19488633629458117577531696464, hi := 19488633629490507071289033369}
lemma t2_checked : ((hm3_0_0_4.realAnswer).add hm3_1_1_4.realAnswer).scale (-1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 3 (1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_0_0_4.realContains hm3_1_1_4.realContains) (-1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 18226648970922046096416564470, hi := 18226648970932246506931486906}
lemma t3_checked : ((hm3_0_0_5.realAnswer).add hm3_1_1_5.realAnswer).scale (-1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 3 (1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_0_0_5.realContains hm3_1_1_5.realContains) (-1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := -4576132383250642799382753521, hi := -4576132383247690549461407426}
lemma t4_checked : ((hm3_0_0_6.realAnswer).add hm3_1_1_6.realAnswer).scale (-1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 3 (1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_0_0_6.realContains hm3_1_1_6.realContains) (-1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -1016592280814678145610881564, hi := -1016592280813886794567813345}
lemma t5_checked : ((hm3_0_0_7.realAnswer).add hm3_1_1_7.realAnswer).scale (-1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 3 (1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_0_0_7.realContains hm3_1_1_7.realContains) (-1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := 358704014898911668109771351, hi := 358704014899108752629000758}
lemma t6_checked : ((hm3_0_0_8.realAnswer).add hm3_1_1_8.realAnswer).scale (-1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 3 (1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_0_0_8.realContains hm3_1_1_8.realContains) (-1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 41515278542564412279531244, hi := 41515278542610175089651726}
lemma t7_checked : ((hm3_0_0_9.realAnswer).add hm3_1_1_9.realAnswer).scale (-1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 3 (1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_0_0_9.realContains hm3_1_1_9.realContains) (-1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := -18732754848597353618114946, hi := -18732754848587466630153335}
lemma t8_checked : ((hm3_0_0_10.realAnswer).add hm3_1_1_10.realAnswer).scale (-1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 3 (1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_0_0_10.realContains hm3_1_1_10.realContains) (-1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := -1102344607945639953787152, hi := -1102344607943659854343142}
lemma t9_checked : ((hm3_0_0_11.realAnswer).add hm3_1_1_11.realAnswer).scale (-1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 3 (1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_0_0_11.realContains hm3_1_1_11.realContains) (-1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := 686043774428057984795082, hi := 686043774428424408140758}
lemma t10_checked : ((hm3_0_0_12.realAnswer).add hm3_1_1_12.realAnswer).scale (-1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 3 (1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_0_0_12.realContains hm3_1_1_12.realContains) (-1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := 11152949049564792416932, hi := 11152949049627547300395}
lemma t11_checked : ((hm3_0_0_13.realAnswer).add hm3_1_1_13.realAnswer).scale (-1) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 3 (1/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_0_0_13.realContains hm3_1_1_13.realContains) (-1) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -21940771376996794397866072, hi := 21940771376996794397866072}
lemma t12_contains : t12.Contains (sourcePower false 3 (1/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (1/2) 2 12 coarse_3_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -4043086167462381503002572, hi := 4043086167462381503002572}
lemma t13_contains : t13.Contains (sourcePower false 3 (1/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (1/2) 2 13 coarse_3_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -715864126238454682678554, hi := 715864126238454682678554}
lemma t14_contains : t14.Contains (sourcePower false 3 (1/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (1/2) 2 14 coarse_3_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -122249712386770544494617, hi := 122249712386770544494617}
lemma t15_contains : t15.Contains (sourcePower false 3 (1/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (1/2) 2 15 coarse_3_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -20198686864620612491610, hi := 20198686864620612491610}
lemma t16_contains : t16.Contains (sourcePower false 3 (1/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (1/2) 2 16 coarse_3_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -3236965951437818359099, hi := 3236965951437818359099}
lemma t17_contains : t17.Contains (sourcePower false 3 (1/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (1/2) 2 17 coarse_3_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -504105662040223246579, hi := 504105662040223246579}
lemma t18_contains : t18.Contains (sourcePower false 3 (1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (1/2) 2 18 coarse_3_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -76398703323662302251, hi := 76398703323662302251}
lemma t19_contains : t19.Contains (sourcePower false 3 (1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (1/2) 2 19 coarse_3_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -11279056507469007889, hi := 11279056507469007889}
lemma t20_contains : t20.Contains (sourcePower false 3 (1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (1/2) 2 20 coarse_3_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -1623305987221238879, hi := 1623305987221238879}
lemma t21_contains : t21.Contains (sourcePower false 3 (1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (1/2) 2 21 coarse_3_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -227882158301826892, hi := 227882158301826892}
lemma t22_contains : t22.Contains (sourcePower false 3 (1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (1/2) 2 22 coarse_3_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -31218112438688220, hi := 31218112438688220}
lemma t23_contains : t23.Contains (sourcePower false 3 (1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (1/2) 2 23 coarse_3_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -4175288966584807, hi := 4175288966584807}
lemma t24_contains : t24.Contains (sourcePower false 3 (1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (1/2) 2 24 coarse_3_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -545457456936434, hi := 545457456936434}
lemma t25_contains : t25.Contains (sourcePower false 3 (1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (1/2) 2 25 coarse_3_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -69641010703742, hi := 69641010703742}
lemma t26_contains : t26.Contains (sourcePower false 3 (1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (1/2) 2 26 coarse_3_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -8694835330545, hi := 8694835330545}
lemma t27_contains : t27.Contains (sourcePower false 3 (1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (1/2) 2 27 coarse_3_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -1062269013594, hi := 1062269013594}
lemma t28_contains : t28.Contains (sourcePower false 3 (1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (1/2) 2 28 coarse_3_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 3 (1/2) 2 r.val) := by
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
lemma bound0 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound1 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound2 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound3 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound4 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound5 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound6 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound7 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound8 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound9 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound10 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound11 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound12 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound13 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound14 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound15 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound16 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound17 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound18 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound19 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound20 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound21 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound22 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound23 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound24 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound25 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound26 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound27 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound28 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound (k : Fin 29) : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (1/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 109691133335343636536425348365, hi := 109691133335528244037722977195}
lemma t0_checked : ((hm3_1_0_2.realAnswer).add hm3_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 3 (1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_1_0_2.realContains hm3_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -105256841164242425896515790845, hi := -105256841164159297909392383384}
lemma t1_checked : ((hm3_1_0_3.realAnswer).add hm3_0_1_3.realAnswer).scale (1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 3 (1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_1_0_3.realContains hm3_0_1_3.realContains) (1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := 6221733600071639115390314718, hi := 6221733600102851815361339760}
lemma t2_checked : ((hm3_1_0_4.realAnswer).add hm3_0_1_4.realAnswer).scale (1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 3 (1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_1_0_4.realContains hm3_0_1_4.realContains) (1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 18568290326722164687390443039, hi := 18568290326732641268887686896}
lemma t3_checked : ((hm3_1_0_5.realAnswer).add hm3_0_1_5.realAnswer).scale (1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 3 (1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_1_0_5.realContains hm3_0_1_5.realContains) (1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := -3563772131706537110756825806, hi := -3563772131703326305994618464}
lemma t4_checked : ((hm3_1_0_6.realAnswer).add hm3_0_1_6.realAnswer).scale (1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 3 (1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_1_0_6.realContains hm3_0_1_6.realContains) (1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -1240821690830606770311970559, hi := -1240821690829708309941855865}
lemma t5_checked : ((hm3_1_0_7.realAnswer).add hm3_0_1_7.realAnswer).scale (1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 3 (1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_1_0_7.realContains hm3_0_1_7.realContains) (1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := 357850385719485676255413734, hi := 357850385719715991683111728}
lemma t6_checked : ((hm3_1_0_8.realAnswer).add hm3_0_1_8.realAnswer).scale (1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 3 (1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_1_0_8.realContains hm3_0_1_8.realContains) (1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 47255598420455691280433566, hi := 47255598420510142650643063}
lemma t7_checked : ((hm3_1_0_9.realAnswer).add hm3_0_1_9.realAnswer).scale (1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 3 (1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_1_0_9.realContains hm3_0_1_9.realContains) (1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := -19118964625187745380596812, hi := -19118964625175856362178512}
lemma t8_checked : ((hm3_1_0_10.realAnswer).add hm3_0_1_10.realAnswer).scale (1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 3 (1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_1_0_10.realContains hm3_0_1_10.realContains) (1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := -1201516671788532377365337, hi := -1201516671786137202463064}
lemma t9_checked : ((hm3_1_0_11.realAnswer).add hm3_0_1_11.realAnswer).scale (1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 3 (1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_1_0_11.realContains hm3_0_1_11.realContains) (1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := 695136152118674668907297, hi := 695136152119119337631399}
lemma t10_checked : ((hm3_1_0_12.realAnswer).add hm3_0_1_12.realAnswer).scale (1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 3 (1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_1_0_12.realContains hm3_0_1_12.realContains) (1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := 13881874338393649074382, hi := 13881874338469939497891}
lemma t11_checked : ((hm3_1_0_13.realAnswer).add hm3_0_1_13.realAnswer).scale (1) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 3 (1/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_1_0_13.realContains hm3_0_1_13.realContains) (1) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -21940771376996794397866072, hi := 21940771376996794397866072}
lemma t12_contains : t12.Contains (sourcePower true 3 (1/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (1/2) 2 12 coarse_3_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -4043086167462381503002572, hi := 4043086167462381503002572}
lemma t13_contains : t13.Contains (sourcePower true 3 (1/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (1/2) 2 13 coarse_3_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -715864126238454682678554, hi := 715864126238454682678554}
lemma t14_contains : t14.Contains (sourcePower true 3 (1/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (1/2) 2 14 coarse_3_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -122249712386770544494617, hi := 122249712386770544494617}
lemma t15_contains : t15.Contains (sourcePower true 3 (1/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (1/2) 2 15 coarse_3_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -20198686864620612491610, hi := 20198686864620612491610}
lemma t16_contains : t16.Contains (sourcePower true 3 (1/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (1/2) 2 16 coarse_3_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -3236965951437818359099, hi := 3236965951437818359099}
lemma t17_contains : t17.Contains (sourcePower true 3 (1/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (1/2) 2 17 coarse_3_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -504105662040223246579, hi := 504105662040223246579}
lemma t18_contains : t18.Contains (sourcePower true 3 (1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (1/2) 2 18 coarse_3_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -76398703323662302251, hi := 76398703323662302251}
lemma t19_contains : t19.Contains (sourcePower true 3 (1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (1/2) 2 19 coarse_3_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -11279056507469007889, hi := 11279056507469007889}
lemma t20_contains : t20.Contains (sourcePower true 3 (1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (1/2) 2 20 coarse_3_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -1623305987221238879, hi := 1623305987221238879}
lemma t21_contains : t21.Contains (sourcePower true 3 (1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (1/2) 2 21 coarse_3_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -227882158301826892, hi := 227882158301826892}
lemma t22_contains : t22.Contains (sourcePower true 3 (1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (1/2) 2 22 coarse_3_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -31218112438688220, hi := 31218112438688220}
lemma t23_contains : t23.Contains (sourcePower true 3 (1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (1/2) 2 23 coarse_3_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -4175288966584807, hi := 4175288966584807}
lemma t24_contains : t24.Contains (sourcePower true 3 (1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (1/2) 2 24 coarse_3_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -545457456936434, hi := 545457456936434}
lemma t25_contains : t25.Contains (sourcePower true 3 (1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (1/2) 2 25 coarse_3_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -69641010703742, hi := 69641010703742}
lemma t26_contains : t26.Contains (sourcePower true 3 (1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (1/2) 2 26 coarse_3_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -8694835330545, hi := 8694835330545}
lemma t27_contains : t27.Contains (sourcePower true 3 (1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (1/2) 2 27 coarse_3_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -1062269013594, hi := 1062269013594}
lemma t28_contains : t28.Contains (sourcePower true 3 (1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (1/2) 2 28 coarse_3_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 3 (1/2) 2 r.val) := by
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
lemma bound0 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound1 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound2 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound3 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound4 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound5 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound6 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound7 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound8 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound9 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound10 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound11 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound12 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound13 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound14 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound15 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound16 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound17 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound18 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound19 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound20 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound21 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound22 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound23 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound24 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound25 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound26 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound27 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound28 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound (k : Fin 29) : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (1/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 134242755693171941492068971114, hi := 134242755693383098939399762064}
lemma t0_checked : ((hm3_0_0_2.realAnswer).add hm3_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 3 (-1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_0_0_2.realContains hm3_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 275833686480479872442981742926, hi := 275833686480662420323511172408}
lemma t1_checked : ((hm3_0_0_3.realAnswer).add hm3_1_1_3.realAnswer).scale (1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 3 (-1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_0_0_3.realContains hm3_1_1_3.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := 77954534517832470310126785858, hi := 77954534517962028285156133474}
lemma t2_checked : ((hm3_0_0_4.realAnswer).add hm3_1_1_4.realAnswer).scale (-1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 3 (-1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_0_0_4.realContains hm3_1_1_4.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -145813191767457972055451895244, hi := -145813191767376368771332515767}
lemma t3_checked : ((hm3_0_0_5.realAnswer).add hm3_1_1_5.realAnswer).scale (1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 3 (-1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_0_0_5.realContains hm3_1_1_5.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := -73218118132010284790124056321, hi := -73218118131963048791382518818}
lemma t4_checked : ((hm3_0_0_6.realAnswer).add hm3_1_1_6.realAnswer).scale (-1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 3 (-1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_0_0_6.realContains hm3_1_1_6.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 32530952986044377426170027066, hi := 32530952986069700659548210030}
lemma t5_checked : ((hm3_0_0_7.realAnswer).add hm3_1_1_7.realAnswer).scale (1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 3 (-1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_0_0_7.realContains hm3_1_1_7.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := 22957056953530346759025366511, hi := 22957056953542960168256048455}
lemma t6_checked : ((hm3_0_0_8.realAnswer).add hm3_1_1_8.realAnswer).scale (-1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 3 (-1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_0_0_8.realContains hm3_1_1_8.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -5313955653454102411475420919, hi := -5313955653448244771779999321}
lemma t7_checked : ((hm3_0_0_9.realAnswer).add hm3_1_1_9.realAnswer).scale (1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 3 (-1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_0_0_9.realContains hm3_1_1_9.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := -4795585241240922526237426153, hi := -4795585241238391457319253921}
lemma t8_checked : ((hm3_0_0_10.realAnswer).add hm3_1_1_10.realAnswer).scale (-1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 3 (-1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_0_0_10.realContains hm3_1_1_10.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := 564400439267153845423689022, hi := 564400439268167656339021475}
lemma t9_checked : ((hm3_0_0_11.realAnswer).add hm3_1_1_11.realAnswer).scale (1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 3 (-1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_0_0_11.realContains hm3_1_1_11.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := 702508825014331376430164333, hi := 702508825014706593936135892}
lemma t10_checked : ((hm3_0_0_12.realAnswer).add hm3_1_1_12.realAnswer).scale (-1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 3 (-1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_0_0_12.realContains hm3_1_1_12.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -22841239653637216871208438, hi := -22841239653508694869878163}
lemma t11_checked : ((hm3_0_0_13.realAnswer).add hm3_1_1_13.realAnswer).scale (1) 1=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 3 (-1/1) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_0_0_13.realContains hm3_1_1_13.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -89869399560178869853659429231, hi := 89869399560178869853659429231}
lemma t12_contains : t12.Contains (sourcePower false 3 (-1/1) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (-1/1) 2 12 coarse_3_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -33120961883851829272597065973, hi := 33120961883851829272597065973}
lemma t13_contains : t13.Contains (sourcePower false 3 (-1/1) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (-1/1) 2 13 coarse_3_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -11728717844290841521005417025, hi := 11728717844290841521005417025}
lemma t14_contains : t14.Contains (sourcePower false 3 (-1/1) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (-1/1) 2 14 coarse_3_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -4005878575489697201999608859, hi := 4005878575489697201999608859}
lemma t15_contains : t15.Contains (sourcePower false 3 (-1/1) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (-1/1) 2 15 coarse_3_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -1323741142359776460250142926, hi := 1323741142359776460250142926}
lemma t16_contains : t16.Contains (sourcePower false 3 (-1/1) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (-1/1) 2 16 coarse_3_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -424275601186857727963730598, hi := 424275601186857727963730598}
lemma t17_contains : t17.Contains (sourcePower false 3 (-1/1) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (-1/1) 2 17 coarse_3_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -132148274669872282750965635, hi := 132148274669872282750965635}
lemma t18_contains : t18.Contains (sourcePower false 3 (-1/1) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (-1/1) 2 18 coarse_3_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -40054923368156261122308451, hi := 40054923368156261122308451}
lemma t19_contains : t19.Contains (sourcePower false 3 (-1/1) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (-1/1) 2 19 coarse_3_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -11826947956375822415775753, hi := 11826947956375822415775753}
lemma t20_contains : t20.Contains (sourcePower false 3 (-1/1) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (-1/1) 2 20 coarse_3_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -3404319397712995555990714, hi := 3404319397712995555990714}
lemma t21_contains : t21.Contains (sourcePower false 3 (-1/1) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (-1/1) 2 21 coarse_3_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -955807048093985739496594, hi := 955807048093985739496594}
lemma t22_contains : t22.Contains (sourcePower false 3 (-1/1) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (-1/1) 2 22 coarse_3_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -261876507748079506096636, hi := 261876507748079506096636}
lemma t23_contains : t23.Contains (sourcePower false 3 (-1/1) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (-1/1) 2 23 coarse_3_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -70049724854810084957006, hi := 70049724854810084957006}
lemma t24_contains : t24.Contains (sourcePower false 3 (-1/1) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (-1/1) 2 24 coarse_3_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -18302515147666469904221, hi := 18302515147666469904221}
lemma t25_contains : t25.Contains (sourcePower false 3 (-1/1) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (-1/1) 2 25 coarse_3_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -4673529116139955813959, hi := 4673529116139955813959}
lemma t26_contains : t26.Contains (sourcePower false 3 (-1/1) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (-1/1) 2 26 coarse_3_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -1167001043399812052418, hi := 1167001043399812052418}
lemma t27_contains : t27.Contains (sourcePower false 3 (-1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (-1/1) 2 27 coarse_3_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -285150667058617221983, hi := 285150667058617221983}
lemma t28_contains : t28.Contains (sourcePower false 3 (-1/1) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 3 (-1/1) 2 28 coarse_3_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 3 (-1/1) 2 r.val) := by
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
lemma bound0 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound1 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound2 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound3 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound4 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound5 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound6 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound7 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound8 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound9 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound10 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound11 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound12 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound13 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound14 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound15 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound16 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound17 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound18 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound19 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound20 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound21 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound22 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound23 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound24 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound25 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound26 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound27 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound28 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound (k : Fin 29) : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 3 (-1/1) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 109691133335343636536425348365, hi := 109691133335528244037722977195}
lemma t0_checked : ((hm3_1_0_2.realAnswer).add hm3_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 3 (-1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_1_0_2.realContains hm3_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 210513682328318595818784766769, hi := 210513682328484851793031581690}
lemma t1_checked : ((hm3_1_0_3.realAnswer).add hm3_0_1_3.realAnswer).scale (-1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 3 (-1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_1_0_3.realContains hm3_0_1_3.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := 24886934400286556461561258874, hi := 24886934400411407261445359040}
lemma t2_checked : ((hm3_1_0_4.realAnswer).add hm3_0_1_4.realAnswer).scale (1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 3 (-1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_1_0_4.realContains hm3_0_1_4.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -148546322613861130151101495167, hi := -148546322613777317499123544319}
lemma t3_checked : ((hm3_1_0_5.realAnswer).add hm3_0_1_5.realAnswer).scale (-1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 3 (-1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_1_0_5.realContains hm3_0_1_5.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := -57020354107304593772109212887, hi := -57020354107253220895913895427}
lemma t4_checked : ((hm3_1_0_6.realAnswer).add hm3_0_1_6.realAnswer).scale (1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 3 (-1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_1_0_6.realContains hm3_0_1_6.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 39706294106550665918139387697, hi := 39706294106579416649983057877}
lemma t5_checked : ((hm3_1_0_7.realAnswer).add hm3_0_1_7.realAnswer).scale (-1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 3 (-1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_1_0_7.realContains hm3_0_1_7.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := 22902424686047083280346479004, hi := 22902424686061823467719150568}
lemma t6_checked : ((hm3_1_0_8.realAnswer).add hm3_0_1_8.realAnswer).scale (1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 3 (-1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_1_0_8.realContains hm3_0_1_8.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -6048716597825298259282312010, hi := -6048716597818328483895496498}
lemma t7_checked : ((hm3_1_0_9.realAnswer).add hm3_0_1_9.realAnswer).scale (-1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 3 (-1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_1_0_9.realContains hm3_0_1_9.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := -4894454944048062817432783801, hi := -4894454944045019228717699143}
lemma t8_checked : ((hm3_1_0_10.realAnswer).add hm3_0_1_10.realAnswer).scale (1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 3 (-1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_1_0_10.realContains hm3_0_1_10.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := 615176535954502247661088944, hi := 615176535955728577211052542}
lemma t9_checked : ((hm3_1_0_11.realAnswer).add hm3_0_1_11.realAnswer).scale (-1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 3 (-1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_1_0_11.realContains hm3_0_1_11.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := 711819419769522860961072446, hi := 711819419769978201734552253}
lemma t10_checked : ((hm3_1_0_12.realAnswer).add hm3_0_1_12.realAnswer).scale (1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 3 (-1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_1_0_12.realContains hm3_0_1_12.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -28430078645186436091679337, hi := -28430078645030193304336294}
lemma t11_checked : ((hm3_1_0_13.realAnswer).add hm3_0_1_13.realAnswer).scale (-1) 1=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 3 (-1/1) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm3_1_0_13.realContains hm3_0_1_13.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -89869399560178869853659429231, hi := 89869399560178869853659429231}
lemma t12_contains : t12.Contains (sourcePower true 3 (-1/1) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (-1/1) 2 12 coarse_3_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -33120961883851829272597065973, hi := 33120961883851829272597065973}
lemma t13_contains : t13.Contains (sourcePower true 3 (-1/1) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (-1/1) 2 13 coarse_3_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -11728717844290841521005417025, hi := 11728717844290841521005417025}
lemma t14_contains : t14.Contains (sourcePower true 3 (-1/1) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (-1/1) 2 14 coarse_3_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -4005878575489697201999608859, hi := 4005878575489697201999608859}
lemma t15_contains : t15.Contains (sourcePower true 3 (-1/1) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (-1/1) 2 15 coarse_3_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -1323741142359776460250142926, hi := 1323741142359776460250142926}
lemma t16_contains : t16.Contains (sourcePower true 3 (-1/1) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (-1/1) 2 16 coarse_3_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -424275601186857727963730598, hi := 424275601186857727963730598}
lemma t17_contains : t17.Contains (sourcePower true 3 (-1/1) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (-1/1) 2 17 coarse_3_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -132148274669872282750965635, hi := 132148274669872282750965635}
lemma t18_contains : t18.Contains (sourcePower true 3 (-1/1) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (-1/1) 2 18 coarse_3_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -40054923368156261122308451, hi := 40054923368156261122308451}
lemma t19_contains : t19.Contains (sourcePower true 3 (-1/1) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (-1/1) 2 19 coarse_3_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -11826947956375822415775753, hi := 11826947956375822415775753}
lemma t20_contains : t20.Contains (sourcePower true 3 (-1/1) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (-1/1) 2 20 coarse_3_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -3404319397712995555990714, hi := 3404319397712995555990714}
lemma t21_contains : t21.Contains (sourcePower true 3 (-1/1) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (-1/1) 2 21 coarse_3_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -955807048093985739496594, hi := 955807048093985739496594}
lemma t22_contains : t22.Contains (sourcePower true 3 (-1/1) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (-1/1) 2 22 coarse_3_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -261876507748079506096636, hi := 261876507748079506096636}
lemma t23_contains : t23.Contains (sourcePower true 3 (-1/1) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (-1/1) 2 23 coarse_3_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -70049724854810084957006, hi := 70049724854810084957006}
lemma t24_contains : t24.Contains (sourcePower true 3 (-1/1) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (-1/1) 2 24 coarse_3_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -18302515147666469904221, hi := 18302515147666469904221}
lemma t25_contains : t25.Contains (sourcePower true 3 (-1/1) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (-1/1) 2 25 coarse_3_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -4673529116139955813959, hi := 4673529116139955813959}
lemma t26_contains : t26.Contains (sourcePower true 3 (-1/1) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (-1/1) 2 26 coarse_3_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -1167001043399812052418, hi := 1167001043399812052418}
lemma t27_contains : t27.Contains (sourcePower true 3 (-1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (-1/1) 2 27 coarse_3_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -285150667058617221983, hi := 285150667058617221983}
lemma t28_contains : t28.Contains (sourcePower true 3 (-1/1) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 3 (-1/1) 2 28 coarse_3_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 3 (-1/1) 2 r.val) := by
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
lemma bound0 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound1 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound2 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound3 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound4 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound5 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound6 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound7 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound8 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound9 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound10 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound11 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound12 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound13 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound14 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound15 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound16 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound17 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound18 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound19 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound20 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound21 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound22 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound23 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound24 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound25 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound26 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound27 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound28 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound (k : Fin 29) : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 3 (-1/1) 2) k.val := by
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
end SharpPlanar.Bernstein3

end OAI
