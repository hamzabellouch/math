import OAI.Analysis.PlanarPacking.Certificate.LowBlock19_0
import OAI.Analysis.PlanarPacking.Certificate.LowBlock19_1
import OAI.Analysis.PlanarPacking.Certificate.LowBlock19_10
import OAI.Analysis.PlanarPacking.Certificate.LowBlock19_11
import OAI.Analysis.PlanarPacking.Certificate.CoarseBound19

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein19
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 418041623508010471787007878659, hi := 418041623508182959018849675707}
lemma t0_checked : ((hm19_0_0_2.realAnswer).add hm19_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 19 (1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_0_0_2.realContains hm19_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -81811698922435974586121837941, hi := -81811698922302693741357525217}
lemma t1_checked : ((hm19_0_0_3.realAnswer).add hm19_1_1_3.realAnswer).scale (-1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 19 (1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_0_0_3.realContains hm19_1_1_3.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -273168500513395047615580420033, hi := -273168500513316725173450600367}
lemma t2_checked : ((hm19_0_0_4.realAnswer).add hm19_1_1_4.realAnswer).scale (-1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 19 (1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_0_0_4.realContains hm19_1_1_4.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 32043129629272688783760470984, hi := 32043129629309732203635744496}
lemma t3_checked : ((hm19_0_0_5.realAnswer).add hm19_1_1_5.realAnswer).scale (-1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 19 (1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_0_0_5.realContains hm19_1_1_5.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 76307531174983436259852322340, hi := 76307531174998084572440023057}
lemma t4_checked : ((hm19_0_0_6.realAnswer).add hm19_1_1_6.realAnswer).scale (-1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 19 (1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_0_0_6.realContains hm19_1_1_6.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -4523412912462351512597056177, hi := -4523412912457374834462057603}
lemma t5_checked : ((hm19_0_0_7.realAnswer).add hm19_1_1_7.realAnswer).scale (-1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 19 (1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_0_0_7.realContains hm19_1_1_7.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -11987762926207518620806234059, hi := -11987762926206036181936169201}
lemma t6_checked : ((hm19_0_0_8.realAnswer).add hm19_1_1_8.realAnswer).scale (-1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 19 (1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_0_0_8.realContains hm19_1_1_8.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 290474242025353641037453382, hi := 290474242025746905986865921}
lemma t7_checked : ((hm19_0_0_9.realAnswer).add hm19_1_1_9.realAnswer).scale (-1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 19 (1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_0_0_9.realContains hm19_1_1_9.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 1218898688841931724200556925, hi := 1218898688842025791805309213}
lemma t8_checked : ((hm19_0_0_10.realAnswer).add hm19_1_1_10.realAnswer).scale (-1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 19 (1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_0_0_10.realContains hm19_1_1_10.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := -3623493619561941448330514, hi := -3623493619541448677210771}
lemma t9_checked : ((hm19_0_0_11.realAnswer).add hm19_1_1_11.realAnswer).scale (-1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 19 (1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_0_0_11.realContains hm19_1_1_11.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -87438462752857870639303942, hi := -87438462752853770585710718}
lemma t10_checked : ((hm19_0_0_12.realAnswer).add hm19_1_1_12.realAnswer).scale (-1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 19 (1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_0_0_12.realContains hm19_1_1_12.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -898889865421253576160071, hi := -898889865420494725080150}
lemma t11_checked : ((hm19_0_0_13.realAnswer).add hm19_1_1_13.realAnswer).scale (-1) 1=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 19 (1/1) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_0_0_13.realContains hm19_1_1_13.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -415519823301646288216618079, hi := 415519823301646288216618079}
lemma t12_contains : t12.Contains (sourcePower false 19 (1/1) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (1/1) 2 12 coarse_19_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -88441022552632104701542875, hi := 88441022552632104701542875}
lemma t13_contains : t13.Contains (sourcePower false 19 (1/1) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (1/1) 2 13 coarse_19_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -17961769109023805605644033, hi := 17961769109023805605644033}
lemma t14_contains : t14.Contains (sourcePower false 19 (1/1) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (1/1) 2 14 coarse_19_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -3499152986883578905581056, hi := 3499152986883578905581056}
lemma t15_contains : t15.Contains (sourcePower false 19 (1/1) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (1/1) 2 15 coarse_19_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -657025204371517831247787, hi := 657025204371517831247787}
lemma t16_contains : t16.Contains (sourcePower false 19 (1/1) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (1/1) 2 16 coarse_19_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -119404930671123464551117, hi := 119404930671123464551117}
lemma t17_contains : t17.Contains (sourcePower false 19 (1/1) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (1/1) 2 17 coarse_19_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -21074327843674396260647, hi := 21074327843674396260647}
lemma t18_contains : t18.Contains (sourcePower false 19 (1/1) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (1/1) 2 18 coarse_19_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -3621158106959460131472, hi := 3621158106959460131472}
lemma t19_contains : t19.Contains (sourcePower false 19 (1/1) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (1/1) 2 19 coarse_19_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -606685585115109330584, hi := 606685585115109330584}
lemma t20_contains : t20.Contains (sourcePower false 19 (1/1) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (1/1) 2 20 coarse_19_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -99171959366183814819, hi := 99171959366183814819}
lemma t21_contains : t21.Contains (sourcePower false 19 (1/1) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (1/1) 2 21 coarse_19_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -15816651699858251513, hi := 15816651699858251513}
lemma t22_contains : t22.Contains (sourcePower false 19 (1/1) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (1/1) 2 22 coarse_19_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -2460008358849052878, hi := 2460008358849052878}
lemma t23_contains : t23.Contains (sourcePower false 19 (1/1) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (1/1) 2 23 coarse_19_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -372867321116342342, hi := 372867321116342342}
lemma t24_contains : t24.Contains (sourcePower false 19 (1/1) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (1/1) 2 24 coarse_19_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -55036650600723914, hi := 55036650600723914}
lemma t25_contains : t25.Contains (sourcePower false 19 (1/1) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (1/1) 2 25 coarse_19_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -7905972890555824, hi := 7905972890555824}
lemma t26_contains : t26.Contains (sourcePower false 19 (1/1) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (1/1) 2 26 coarse_19_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -1104748937734647, hi := 1104748937734647}
lemma t27_contains : t27.Contains (sourcePower false 19 (1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (1/1) 2 27 coarse_19_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -150128174659659, hi := 150128174659659}
lemma t28_contains : t28.Contains (sourcePower false 19 (1/1) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (1/1) 2 28 coarse_19_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 19 (1/1) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (1/1) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 392499435998557686655700683177, hi := 392499435998699282161749424177}
lemma t0_checked : ((hm19_1_0_2.realAnswer).add hm19_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 19 (1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_1_0_2.realContains hm19_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -71453019841835113115440650969, hi := -71453019841725706234396581531}
lemma t1_checked : ((hm19_1_0_3.realAnswer).add hm19_0_1_3.realAnswer).scale (1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 19 (1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_1_0_3.realContains hm19_0_1_3.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -257655512395533580699579984749, hi := -257655512395469286066226511209}
lemma t2_checked : ((hm19_1_0_4.realAnswer).add hm19_0_1_4.realAnswer).scale (1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 19 (1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_1_0_4.realContains hm19_0_1_4.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 26565145161497646958012625271, hi := 26565145161528057177679541085}
lemma t3_checked : ((hm19_1_0_5.realAnswer).add hm19_0_1_5.realAnswer).scale (1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 19 (1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_1_0_5.realContains hm19_0_1_5.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 72159551303899914921530596953, hi := 72159551303911940833895360770}
lemma t4_checked : ((hm19_1_0_6.realAnswer).add hm19_0_1_6.realAnswer).scale (1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 19 (1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_1_0_6.realContains hm19_0_1_6.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -3254094907058880924229010317, hi := -3254094907054794980919407187}
lemma t5_checked : ((hm19_1_0_7.realAnswer).add hm19_0_1_7.realAnswer).scale (1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 19 (1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_1_0_7.realContains hm19_0_1_7.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -11347025459048271794830667738, hi := -11347025459047054622645133635}
lemma t6_checked : ((hm19_1_0_8.realAnswer).add hm19_0_1_8.realAnswer).scale (1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 19 (1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_1_0_8.realContains hm19_0_1_8.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 114373815928782454023583764, hi := 114373815929105365733717269}
lemma t7_checked : ((hm19_1_0_9.realAnswer).add hm19_0_1_9.realAnswer).scale (1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 19 (1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_1_0_9.realContains hm19_0_1_9.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 1154187779898513168042404589, hi := 1154187779898590411928929085}
lemma t8_checked : ((hm19_1_0_10.realAnswer).add hm19_0_1_10.realAnswer).scale (1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 19 (1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_1_0_10.realContains hm19_0_1_10.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := 12983130781087111940810085, hi := 12983130781103940822387659}
lemma t9_checked : ((hm19_1_0_11.realAnswer).add hm19_0_1_11.realAnswer).scale (1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 19 (1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_1_0_11.realContains hm19_0_1_11.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -82839051474928266842125134, hi := -82839051474924899497510860}
lemma t10_checked : ((hm19_1_0_12.realAnswer).add hm19_0_1_12.realAnswer).scale (1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 19 (1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_1_0_12.realContains hm19_0_1_12.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -2039134302348838813220978, hi := -2039134302348215447477893}
lemma t11_checked : ((hm19_1_0_13.realAnswer).add hm19_0_1_13.realAnswer).scale (1) 1=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 19 (1/1) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_1_0_13.realContains hm19_0_1_13.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -415519823301646288216618079, hi := 415519823301646288216618079}
lemma t12_contains : t12.Contains (sourcePower true 19 (1/1) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (1/1) 2 12 coarse_19_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -88441022552632104701542875, hi := 88441022552632104701542875}
lemma t13_contains : t13.Contains (sourcePower true 19 (1/1) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (1/1) 2 13 coarse_19_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -17961769109023805605644033, hi := 17961769109023805605644033}
lemma t14_contains : t14.Contains (sourcePower true 19 (1/1) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (1/1) 2 14 coarse_19_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -3499152986883578905581056, hi := 3499152986883578905581056}
lemma t15_contains : t15.Contains (sourcePower true 19 (1/1) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (1/1) 2 15 coarse_19_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -657025204371517831247787, hi := 657025204371517831247787}
lemma t16_contains : t16.Contains (sourcePower true 19 (1/1) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (1/1) 2 16 coarse_19_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -119404930671123464551117, hi := 119404930671123464551117}
lemma t17_contains : t17.Contains (sourcePower true 19 (1/1) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (1/1) 2 17 coarse_19_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -21074327843674396260647, hi := 21074327843674396260647}
lemma t18_contains : t18.Contains (sourcePower true 19 (1/1) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (1/1) 2 18 coarse_19_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -3621158106959460131472, hi := 3621158106959460131472}
lemma t19_contains : t19.Contains (sourcePower true 19 (1/1) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (1/1) 2 19 coarse_19_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -606685585115109330584, hi := 606685585115109330584}
lemma t20_contains : t20.Contains (sourcePower true 19 (1/1) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (1/1) 2 20 coarse_19_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -99171959366183814819, hi := 99171959366183814819}
lemma t21_contains : t21.Contains (sourcePower true 19 (1/1) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (1/1) 2 21 coarse_19_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -15816651699858251513, hi := 15816651699858251513}
lemma t22_contains : t22.Contains (sourcePower true 19 (1/1) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (1/1) 2 22 coarse_19_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -2460008358849052878, hi := 2460008358849052878}
lemma t23_contains : t23.Contains (sourcePower true 19 (1/1) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (1/1) 2 23 coarse_19_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -372867321116342342, hi := 372867321116342342}
lemma t24_contains : t24.Contains (sourcePower true 19 (1/1) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (1/1) 2 24 coarse_19_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -55036650600723914, hi := 55036650600723914}
lemma t25_contains : t25.Contains (sourcePower true 19 (1/1) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (1/1) 2 25 coarse_19_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -7905972890555824, hi := 7905972890555824}
lemma t26_contains : t26.Contains (sourcePower true 19 (1/1) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (1/1) 2 26 coarse_19_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -1104748937734647, hi := 1104748937734647}
lemma t27_contains : t27.Contains (sourcePower true 19 (1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (1/1) 2 27 coarse_19_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -150128174659659, hi := 150128174659659}
lemma t28_contains : t28.Contains (sourcePower true 19 (1/1) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (1/1) 2 28 coarse_19_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 19 (1/1) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (1/1) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 418041623508010471787007878659, hi := 418041623508182959018849675707}
lemma t0_checked : ((hm19_0_0_2.realAnswer).add hm19_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 19 (-3/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_0_0_2.realContains hm19_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 122717548383454040612036287825, hi := 122717548383653961879182756912}
lemma t1_checked : ((hm19_0_0_3.realAnswer).add hm19_1_1_3.realAnswer).scale (3) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 19 (-3/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_0_0_3.realContains hm19_1_1_3.realContains) (3) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -614629126155138857135055945075, hi := -614629126154962631640263850825}
lemma t2_checked : ((hm19_0_0_4.realAnswer).add hm19_1_1_4.realAnswer).scale (-9) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 19 (-3/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_0_0_4.realContains hm19_1_1_4.realContains) (-9) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -108145562498920346187270637674, hi := -108145562498795324645191589571}
lemma t3_checked : ((hm19_0_0_5.realAnswer).add hm19_1_1_5.realAnswer).scale (27) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 19 (-3/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_0_0_5.realContains hm19_1_1_5.realContains) (27) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 386306876573353646065502381846, hi := 386306876573427803147977616727}
lemma t4_checked : ((hm19_0_0_6.realAnswer).add hm19_1_1_6.realAnswer).scale (-81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 19 (-3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_0_0_6.realContains hm19_1_1_6.realContains) (-81) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 34349666803973190149196249922, hi := 34349666804010981798783895345}
lemma t5_checked : ((hm19_0_0_7.realAnswer).add hm19_1_1_7.realAnswer).scale (243) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 19 (-3/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_0_0_7.realContains hm19_1_1_7.realContains) (243) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -136548112081332516790121009829, hi := -136548112081315630884866677305}
lemma t6_checked : ((hm19_0_0_8.realAnswer).add hm19_1_1_8.realAnswer).scale (-729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 19 (-3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_0_0_8.realContains hm19_1_1_8.realContains) (-729) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -4963024744611785026509966948, hi := -4963024744605065726163363644}
lemma t7_checked : ((hm19_0_0_9.realAnswer).add hm19_1_1_9.realAnswer).scale (2187) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 19 (-3/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_0_0_9.realContains hm19_1_1_9.realContains) (2187) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 31239040224577789228436929628, hi := 31239040224580200078260288073}
lemma t8_checked : ((hm19_0_0_10.realAnswer).add hm19_1_1_10.realAnswer).scale (-6561) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 19 (-3/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_0_0_10.realContains hm19_1_1_10.realContains) (-6561) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := 139299267409051434206132042, hi := 139299267409839245170877944}
lemma t9_checked : ((hm19_0_0_11.realAnswer).add hm19_1_1_11.realAnswer).scale (19683) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 19 (-3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_0_0_11.realContains hm19_1_1_11.realContains) (19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -5042142370208500393926033664, hi := -5042142370208263964175422057}
lemma t10_checked : ((hm19_0_0_12.realAnswer).add hm19_1_1_12.realAnswer).scale (-59049) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 19 (-3/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_0_0_12.realContains hm19_1_1_12.realContains) (-59049) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := 77751778803537294464733072, hi := 77751778803602933230482470}
lemma t11_checked : ((hm19_0_0_13.realAnswer).add hm19_1_1_13.realAnswer).scale (177147) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 19 (-3/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_0_0_13.realContains hm19_1_1_13.realContains) (177147) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -53912175394348194593781183722, hi := 53912175394348194593781183722}
lemma t12_contains : t12.Contains (sourcePower false 19 (-3/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (-3/2) 2 12 coarse_19_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -17212348193259286506845451795, hi := 17212348193259286506845451795}
lemma t13_contains : t13.Contains (sourcePower false 19 (-3/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (-3/2) 2 13 coarse_19_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -5243565968848784330677590020, hi := 5243565968848784330677590020}
lemma t14_contains : t14.Contains (sourcePower false 19 (-3/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (-3/2) 2 14 coarse_19_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -1532257714464254563700694382, hi := 1532257714464254563700694382}
lemma t15_contains : t15.Contains (sourcePower false 19 (-3/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (-3/2) 2 15 coarse_19_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -431560984230784735538460829, hi := 431560984230784735538460829}
lemma t16_contains : t16.Contains (sourcePower false 19 (-3/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (-3/2) 2 16 coarse_19_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -117645051650028866617248316, hi := 117645051650028866617248316}
lemma t17_contains : t17.Contains (sourcePower false 19 (-3/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (-3/2) 2 17 coarse_19_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -31145577997370339035337953, hi := 31145577997370339035337953}
lemma t18_contains : t18.Contains (sourcePower false 19 (-3/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (-3/2) 2 18 coarse_19_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -8027520243899622043481178, hi := 8027520243899622043481178}
lemma t19_contains : t19.Contains (sourcePower false 19 (-3/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (-3/2) 2 19 coarse_19_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -2017385324946328166284412, hi := 2017385324946328166284412}
lemma t20_contains : t20.Contains (sourcePower false 19 (-3/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (-3/2) 2 20 coarse_19_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -494658337976382597555488, hi := 494658337976382597555488}
lemma t21_contains : t21.Contains (sourcePower false 19 (-3/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (-3/2) 2 21 coarse_19_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -118337461902628652472489, hi := 118337461902628652472489}
lemma t22_contains : t22.Contains (sourcePower false 19 (-3/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (-3/2) 2 22 coarse_19_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -27608037810688158630507, hi := 27608037810688158630507}
lemma t23_contains : t23.Contains (sourcePower false 19 (-3/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (-3/2) 2 23 coarse_19_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -6276890317904993958782, hi := 6276890317904993958782}
lemma t24_contains : t24.Contains (sourcePower false 19 (-3/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (-3/2) 2 24 coarse_19_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -1389739726659286490149, hi := 1389739726659286490149}
lemma t25_contains : t25.Contains (sourcePower false 19 (-3/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (-3/2) 2 25 coarse_19_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -299452577981342345968, hi := 299452577981342345968}
lemma t26_contains : t26.Contains (sourcePower false 19 (-3/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (-3/2) 2 26 coarse_19_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -62766453036154687587, hi := 62766453036154687587}
lemma t27_contains : t27.Contains (sourcePower false 19 (-3/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (-3/2) 2 27 coarse_19_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -12794327338528462519, hi := 12794327338528462519}
lemma t28_contains : t28.Contains (sourcePower false 19 (-3/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 19 (-3/2) 2 28 coarse_19_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 19 (-3/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 19 (-3/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 392499435998557686655700683177, hi := 392499435998699282161749424177}
lemma t0_checked : ((hm19_1_0_2.realAnswer).add hm19_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 19 (-3/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_1_0_2.realContains hm19_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 107179529762588559351594872296, hi := 107179529762752669673160976454}
lemma t1_checked : ((hm19_1_0_3.realAnswer).add hm19_0_1_3.realAnswer).scale (-3) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 19 (-3/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_1_0_3.realContains hm19_0_1_3.realContains) (-3) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -579724902889950556574054965686, hi := -579724902889805893649009650220}
lemma t2_checked : ((hm19_1_0_4.realAnswer).add hm19_0_1_4.realAnswer).scale (9) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 19 (-3/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_1_0_4.realContains hm19_0_1_4.realContains) (9) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -89657364920157192974668451162, hi := -89657364920054558483292610289}
lemma t3_checked : ((hm19_1_0_5.realAnswer).add hm19_0_1_5.realAnswer).scale (-27) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 19 (-3/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_1_0_5.realContains hm19_0_1_5.realContains) (-27) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 365307728475993319290248647074, hi := 365307728476054200471595263899}
lemma t4_checked : ((hm19_1_0_6.realAnswer).add hm19_0_1_6.realAnswer).scale (81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 19 (-3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_1_0_6.realContains hm19_0_1_6.realContains) (81) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 24710783200447349386356748326, hi := 24710783200478377018364047095}
lemma t5_checked : ((hm19_1_0_7.realAnswer).add hm19_0_1_7.realAnswer).scale (-243) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 19 (-3/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_1_0_7.realContains hm19_0_1_7.realContains) (-243) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -129249711869471720912993074704, hi := -129249711869457856561067225311}
lemma t6_checked : ((hm19_1_0_8.realAnswer).add hm19_0_1_8.realAnswer).scale (729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 19 (-3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_1_0_8.realContains hm19_0_1_8.realContains) (729) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -1954183870601198709840934901, hi := -1954183870595681460543575717}
lemma t7_checked : ((hm19_1_0_9.realAnswer).add hm19_0_1_9.realAnswer).scale (-2187) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 19 (-3/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_1_0_9.realContains hm19_0_1_9.realContains) (-2187) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 29580570405914628498149283236, hi := 29580570405916608174475405183}
lemma t8_checked : ((hm19_1_0_10.realAnswer).add hm19_0_1_10.realAnswer).scale (6561) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 19 (-3/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_1_0_10.realContains hm19_0_1_10.realContains) (6561) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := -499115162430603256263781821, hi := -499115162429956297521415826}
lemma t9_checked : ((hm19_1_0_11.realAnswer).add hm19_0_1_11.realAnswer).scale (-19683) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 19 (-3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_1_0_11.realContains hm19_0_1_11.realContains) (-19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -4776917139202186746836569373, hi := -4776917139201992568777850363}
lemma t10_checked : ((hm19_1_0_12.realAnswer).add hm19_0_1_12.realAnswer).scale (59049) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 19 (-3/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_1_0_12.realContains hm19_0_1_12.realContains) (59049) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := 176380138797890293883967925, hi := 176380138797944213498855757}
lemma t11_checked : ((hm19_1_0_13.realAnswer).add hm19_0_1_13.realAnswer).scale (-177147) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 19 (-3/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm19_1_0_13.realContains hm19_0_1_13.realContains) (-177147) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -53912175394348194593781183722, hi := 53912175394348194593781183722}
lemma t12_contains : t12.Contains (sourcePower true 19 (-3/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (-3/2) 2 12 coarse_19_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -17212348193259286506845451795, hi := 17212348193259286506845451795}
lemma t13_contains : t13.Contains (sourcePower true 19 (-3/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (-3/2) 2 13 coarse_19_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -5243565968848784330677590020, hi := 5243565968848784330677590020}
lemma t14_contains : t14.Contains (sourcePower true 19 (-3/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (-3/2) 2 14 coarse_19_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -1532257714464254563700694382, hi := 1532257714464254563700694382}
lemma t15_contains : t15.Contains (sourcePower true 19 (-3/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (-3/2) 2 15 coarse_19_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -431560984230784735538460829, hi := 431560984230784735538460829}
lemma t16_contains : t16.Contains (sourcePower true 19 (-3/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (-3/2) 2 16 coarse_19_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -117645051650028866617248316, hi := 117645051650028866617248316}
lemma t17_contains : t17.Contains (sourcePower true 19 (-3/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (-3/2) 2 17 coarse_19_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -31145577997370339035337953, hi := 31145577997370339035337953}
lemma t18_contains : t18.Contains (sourcePower true 19 (-3/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (-3/2) 2 18 coarse_19_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -8027520243899622043481178, hi := 8027520243899622043481178}
lemma t19_contains : t19.Contains (sourcePower true 19 (-3/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (-3/2) 2 19 coarse_19_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -2017385324946328166284412, hi := 2017385324946328166284412}
lemma t20_contains : t20.Contains (sourcePower true 19 (-3/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (-3/2) 2 20 coarse_19_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -494658337976382597555488, hi := 494658337976382597555488}
lemma t21_contains : t21.Contains (sourcePower true 19 (-3/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (-3/2) 2 21 coarse_19_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -118337461902628652472489, hi := 118337461902628652472489}
lemma t22_contains : t22.Contains (sourcePower true 19 (-3/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (-3/2) 2 22 coarse_19_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -27608037810688158630507, hi := 27608037810688158630507}
lemma t23_contains : t23.Contains (sourcePower true 19 (-3/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (-3/2) 2 23 coarse_19_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -6276890317904993958782, hi := 6276890317904993958782}
lemma t24_contains : t24.Contains (sourcePower true 19 (-3/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (-3/2) 2 24 coarse_19_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -1389739726659286490149, hi := 1389739726659286490149}
lemma t25_contains : t25.Contains (sourcePower true 19 (-3/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (-3/2) 2 25 coarse_19_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -299452577981342345968, hi := 299452577981342345968}
lemma t26_contains : t26.Contains (sourcePower true 19 (-3/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (-3/2) 2 26 coarse_19_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -62766453036154687587, hi := 62766453036154687587}
lemma t27_contains : t27.Contains (sourcePower true 19 (-3/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (-3/2) 2 27 coarse_19_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -12794327338528462519, hi := 12794327338528462519}
lemma t28_contains : t28.Contains (sourcePower true 19 (-3/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 19 (-3/2) 2 28 coarse_19_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 19 (-3/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 19 (-3/2) 2) k.val := by
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
end SharpPlanar.Bernstein19

end OAI
