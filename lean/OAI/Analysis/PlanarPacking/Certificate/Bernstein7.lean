import OAI.Analysis.PlanarPacking.Certificate.LowBlock7_0
import OAI.Analysis.PlanarPacking.Certificate.LowBlock7_1
import OAI.Analysis.PlanarPacking.Certificate.LowBlock7_2
import OAI.Analysis.PlanarPacking.Certificate.LowBlock7_10
import OAI.Analysis.PlanarPacking.Certificate.LowBlock7_11
import OAI.Analysis.PlanarPacking.Certificate.LowBlock7_12
import OAI.Analysis.PlanarPacking.Certificate.CoarseBound7

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein7
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 538463161189387922590478174717, hi := 538463161189561145459590916087}
lemma t0_checked : ((hm7_0_0_2.realAnswer).add hm7_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 7 (1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_2.realContains hm7_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -23752717039540118050992698029, hi := -23752717039405872258168669887}
lemma t1_checked : ((hm7_0_0_3.realAnswer).add hm7_1_1_3.realAnswer).scale (-1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 7 (1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_3.realContains hm7_1_1_3.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -396436122938674150508555192975, hi := -396436122938594838582877136377}
lemma t2_checked : ((hm7_0_0_4.realAnswer).add hm7_1_1_4.realAnswer).scale (-1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 7 (1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_4.realContains hm7_1_1_4.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -10421916090458033712797476826, hi := -10421916090420155320701567466}
lemma t3_checked : ((hm7_0_0_5.realAnswer).add hm7_1_1_5.realAnswer).scale (-1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 7 (1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_5.realContains hm7_1_1_5.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 127254610086394278304183695825, hi := 127254610086409523946588160539}
lemma t4_checked : ((hm7_0_0_6.realAnswer).add hm7_1_1_6.realAnswer).scale (-1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 7 (1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_6.realContains hm7_1_1_6.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 8047126556900597995820213482, hi := 8047126556905944680807851369}
lemma t5_checked : ((hm7_0_0_7.realAnswer).add hm7_1_1_7.realAnswer).scale (-1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 7 (1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_7.realContains hm7_1_1_7.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -23715456158654664197656117590, hi := -23715456158652980073814349199}
lemma t6_checked : ((hm7_0_0_8.realAnswer).add hm7_1_1_8.realAnswer).scale (-1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 7 (1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_8.realContains hm7_1_1_8.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -1640440314645581567618236740, hi := -1640440314645090293008916267}
lemma t7_checked : ((hm7_0_0_9.realAnswer).add hm7_1_1_9.realAnswer).scale (-1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 7 (1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_9.realContains hm7_1_1_9.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 2955636065841791176767972524, hi := 2955636065841928173808456568}
lemma t8_checked : ((hm7_0_0_10.realAnswer).add hm7_1_1_10.realAnswer).scale (-1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 7 (1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_10.realContains hm7_1_1_10.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := 158594978607394331443451750, hi := 158594978607431942110347419}
lemma t9_checked : ((hm7_0_0_11.realAnswer).add hm7_1_1_11.realAnswer).scale (-1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 7 (1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_11.realContains hm7_1_1_11.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -265037200460604883906082275, hi := -265037200460594517695802176}
lemma t10_checked : ((hm7_0_0_12.realAnswer).add hm7_1_1_12.realAnswer).scale (-1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 7 (1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_12.realContains hm7_1_1_12.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -6632127038445349791072783, hi := -6632127038442470795669236}
lemma t11_checked : ((hm7_0_0_13.realAnswer).add hm7_1_1_13.realAnswer).scale (-1) 1=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 7 (1/1) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_13.realContains hm7_1_1_13.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := 17702241063417713968262295, hi := 17702241063418511783664434}
lemma t12_checked : ((hm7_0_0_14.realAnswer).add hm7_1_1_14.realAnswer).scale (-1) 1=t12 := by decide +kernel
lemma t12_contains : t12.Contains (sourcePower false 7 (1/1) 2 12) := by
  rw [← t12_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_14.realContains hm7_1_1_14.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t13 : RBox := {lo := -182214370858058666187002, hi := -182214370857841339584621}
lemma t13_checked : ((hm7_0_0_15.realAnswer).add hm7_1_1_15.realAnswer).scale (-1) 1=t13 := by decide +kernel
lemma t13_contains : t13.Contains (sourcePower false 7 (1/1) 2 13) := by
  rw [← t13_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_15.realContains hm7_1_1_15.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t14 : RBox := {lo := -204281774361712333952676764, hi := 204281774361712333952676764}
lemma t14_contains : t14.Contains (sourcePower false 7 (1/1) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (1/1) 2 14 coarse_7_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -52937841163001576803968807, hi := 52937841163001576803968807}
lemma t15_contains : t15.Contains (sourcePower false 7 (1/1) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (1/1) 2 15 coarse_7_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -13154196706614470209797439, hi := 13154196706614470209797439}
lemma t16_contains : t16.Contains (sourcePower false 7 (1/1) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (1/1) 2 16 coarse_7_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -3139490217511196715330409, hi := 3139490217511196715330409}
lemma t17_contains : t17.Contains (sourcePower false 7 (1/1) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (1/1) 2 17 coarse_7_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -721027148307673611577041, hi := 721027148307673611577041}
lemma t18_contains : t18.Contains (sourcePower false 7 (1/1) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (1/1) 2 18 coarse_7_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -159653917264451567983550, hi := 159653917264451567983550}
lemma t19_contains : t19.Contains (sourcePower false 7 (1/1) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (1/1) 2 19 coarse_7_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -34150320816868495224516, hi := 34150320816868495224516}
lemma t20_contains : t20.Contains (sourcePower false 7 (1/1) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (1/1) 2 20 coarse_7_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -7070434194851407944553, hi := 7070434194851407944553}
lemma t21_contains : t21.Contains (sourcePower false 7 (1/1) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (1/1) 2 21 coarse_7_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -1419603453451501127661, hi := 1419603453451501127661}
lemma t22_contains : t22.Contains (sourcePower false 7 (1/1) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (1/1) 2 22 coarse_7_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -276927823249205454678, hi := 276927823249205454678}
lemma t23_contains : t23.Contains (sourcePower false 7 (1/1) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (1/1) 2 23 coarse_7_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -52580065247005273152, hi := 52580065247005273152}
lemma t24_contains : t24.Contains (sourcePower false 7 (1/1) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (1/1) 2 24 coarse_7_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -9733461848536277803, hi := 9733461848536277803}
lemma t25_contains : t25.Contains (sourcePower false 7 (1/1) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (1/1) 2 25 coarse_7_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -1759524875452051454, hi := 1759524875452051454}
lemma t26_contains : t26.Contains (sourcePower false 7 (1/1) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (1/1) 2 26 coarse_7_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -311059105492441427, hi := 311059105492441427}
lemma t27_contains : t27.Contains (sourcePower false 7 (1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (1/1) 2 27 coarse_7_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -53850542623120176, hi := 53850542623120176}
lemma t28_contains : t28.Contains (sourcePower false 7 (1/1) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (1/1) 2 28 coarse_7_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 7 (1/1) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (1/1) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 534397849612598033175569983629, hi := 534397849612740502416964706407}
lemma t0_checked : ((hm7_1_0_2.realAnswer).add hm7_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 7 (1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_2.realContains hm7_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -25206674455061033616328481260, hi := -25206674454950471840307357829}
lemma t1_checked : ((hm7_1_0_3.realAnswer).add hm7_0_1_3.realAnswer).scale (1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 7 (1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_3.realContains hm7_0_1_3.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -395441560120170911722892618580, hi := -395441560120105423569434556194}
lemma t2_checked : ((hm7_1_0_4.realAnswer).add hm7_0_1_4.realAnswer).scale (1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 7 (1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_4.realContains hm7_0_1_4.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -8292881632020878816502487879, hi := -8292881631989456306789152353}
lemma t3_checked : ((hm7_1_0_5.realAnswer).add hm7_0_1_5.realAnswer).scale (1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 7 (1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_5.realContains hm7_0_1_5.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 127481792154820913948040400561, hi := 127481792154833666014589476393}
lemma t4_checked : ((hm7_1_0_6.realAnswer).add hm7_0_1_6.realAnswer).scale (1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 7 (1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_6.realContains hm7_0_1_6.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 7210939132368625279973923679, hi := 7210939132373161594157593046}
lemma t5_checked : ((hm7_1_0_7.realAnswer).add hm7_0_1_7.realAnswer).scale (1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 7 (1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_7.realContains hm7_0_1_7.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -23851722930667312919853367789, hi := -23851722930665850142689918544}
lemma t6_checked : ((hm7_1_0_8.realAnswer).add hm7_0_1_8.realAnswer).scale (1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 7 (1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_8.realContains hm7_0_1_8.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -1480229689536772614147927299, hi := -1480229689536330337509699582}
lemma t7_checked : ((hm7_1_0_9.realAnswer).add hm7_0_1_9.realAnswer).scale (1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 7 (1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_9.realContains hm7_0_1_9.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 2981934416350600270529350552, hi := 2981934416350729795404338452}
lemma t8_checked : ((hm7_1_0_10.realAnswer).add hm7_0_1_10.realAnswer).scale (1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 7 (1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_10.realContains hm7_0_1_10.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := 139627364117288562052529354, hi := 139627364117326235919474259}
lemma t9_checked : ((hm7_1_0_11.realAnswer).add hm7_0_1_11.realAnswer).scale (1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 7 (1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_11.realContains hm7_0_1_11.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -267987290678848865712313366, hi := -267987290678837868494783274}
lemma t10_checked : ((hm7_1_0_12.realAnswer).add hm7_0_1_12.realAnswer).scale (1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 7 (1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_12.realContains hm7_0_1_12.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -5050321972106187209695201, hi := -5050321972102982449182171}
lemma t11_checked : ((hm7_1_0_13.realAnswer).add hm7_0_1_13.realAnswer).scale (1) 1=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 7 (1/1) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_13.realContains hm7_0_1_13.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := 17924354677857427064879618, hi := 17924354677858346631351808}
lemma t12_checked : ((hm7_1_0_14.realAnswer).add hm7_0_1_14.realAnswer).scale (1) 1=t12 := by decide +kernel
lemma t12_contains : t12.Contains (sourcePower true 7 (1/1) 2 12) := by
  rw [← t12_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_14.realContains hm7_0_1_14.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t13 : RBox := {lo := -283370206079940984826797, hi := -283370206079684794520087}
lemma t13_checked : ((hm7_1_0_15.realAnswer).add hm7_0_1_15.realAnswer).scale (1) 1=t13 := by decide +kernel
lemma t13_contains : t13.Contains (sourcePower true 7 (1/1) 2 13) := by
  rw [← t13_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_15.realContains hm7_0_1_15.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t14 : RBox := {lo := -204281774361712333952676764, hi := 204281774361712333952676764}
lemma t14_contains : t14.Contains (sourcePower true 7 (1/1) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (1/1) 2 14 coarse_7_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -52937841163001576803968807, hi := 52937841163001576803968807}
lemma t15_contains : t15.Contains (sourcePower true 7 (1/1) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (1/1) 2 15 coarse_7_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -13154196706614470209797439, hi := 13154196706614470209797439}
lemma t16_contains : t16.Contains (sourcePower true 7 (1/1) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (1/1) 2 16 coarse_7_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -3139490217511196715330409, hi := 3139490217511196715330409}
lemma t17_contains : t17.Contains (sourcePower true 7 (1/1) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (1/1) 2 17 coarse_7_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -721027148307673611577041, hi := 721027148307673611577041}
lemma t18_contains : t18.Contains (sourcePower true 7 (1/1) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (1/1) 2 18 coarse_7_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -159653917264451567983550, hi := 159653917264451567983550}
lemma t19_contains : t19.Contains (sourcePower true 7 (1/1) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (1/1) 2 19 coarse_7_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -34150320816868495224516, hi := 34150320816868495224516}
lemma t20_contains : t20.Contains (sourcePower true 7 (1/1) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (1/1) 2 20 coarse_7_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -7070434194851407944553, hi := 7070434194851407944553}
lemma t21_contains : t21.Contains (sourcePower true 7 (1/1) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (1/1) 2 21 coarse_7_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -1419603453451501127661, hi := 1419603453451501127661}
lemma t22_contains : t22.Contains (sourcePower true 7 (1/1) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (1/1) 2 22 coarse_7_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -276927823249205454678, hi := 276927823249205454678}
lemma t23_contains : t23.Contains (sourcePower true 7 (1/1) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (1/1) 2 23 coarse_7_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -52580065247005273152, hi := 52580065247005273152}
lemma t24_contains : t24.Contains (sourcePower true 7 (1/1) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (1/1) 2 24 coarse_7_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -9733461848536277803, hi := 9733461848536277803}
lemma t25_contains : t25.Contains (sourcePower true 7 (1/1) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (1/1) 2 25 coarse_7_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -1759524875452051454, hi := 1759524875452051454}
lemma t26_contains : t26.Contains (sourcePower true 7 (1/1) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (1/1) 2 26 coarse_7_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -311059105492441427, hi := 311059105492441427}
lemma t27_contains : t27.Contains (sourcePower true 7 (1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (1/1) 2 27 coarse_7_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -53850542623120176, hi := 53850542623120176}
lemma t28_contains : t28.Contains (sourcePower true 7 (1/1) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (1/1) 2 28 coarse_7_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 7 (1/1) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (1/1) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 538463161189387922590478174717, hi := 538463161189561145459590916087}
lemma t0_checked : ((hm7_0_0_2.realAnswer).add hm7_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 7 (-3/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_2.realContains hm7_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 35629075559108808387253004830, hi := 35629075559310177076489047044}
lemma t1_checked : ((hm7_0_0_3.realAnswer).add hm7_1_1_3.realAnswer).scale (3) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 7 (-3/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_3.realContains hm7_1_1_3.realContains) (3) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -891981276612016838644249184194, hi := -891981276611838386811473556848}
lemma t2_checked : ((hm7_0_0_4.realAnswer).add hm7_1_1_4.realAnswer).scale (-9) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 7 (-3/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_4.realContains hm7_1_1_4.realContains) (-9) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 35173966805168024207367790197, hi := 35173966805295863780691484288}
lemma t3_checked : ((hm7_0_0_5.realAnswer).add hm7_1_1_5.realAnswer).scale (27) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 7 (-3/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_5.realContains hm7_1_1_5.realContains) (27) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 644226463562371033914929960114, hi := 644226463562448214979602562729}
lemma t4_checked : ((hm7_0_0_6.realAnswer).add hm7_1_1_6.realAnswer).scale (-81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 7 (-3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_6.realContains hm7_1_1_6.realContains) (-81) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -61107867291504517419884621334, hi := -61107867291463916030759746128}
lemma t5_checked : ((hm7_0_0_7.realAnswer).add hm7_1_1_7.realAnswer).scale (243) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 7 (-3/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_7.realContains hm7_1_1_7.realContains) (243) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -270133867807175784376426714424, hi := -270133867807156601153291571344}
lemma t6_checked : ((hm7_0_0_8.realAnswer).add hm7_1_1_8.realAnswer).scale (-729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 7 (-3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_8.realContains hm7_1_1_8.realContains) (-729) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 28028460688506347428207030280, hi := 28028460688514741315477216800}
lemma t7_checked : ((hm7_0_0_9.realAnswer).add hm7_1_1_9.realAnswer).scale (2187) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 7 (-3/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_9.realContains hm7_1_1_9.realContains) (2187) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 75749719640578093401463545820, hi := 75749719640581604485770638839}
lemma t8_checked : ((hm7_0_0_10.realAnswer).add hm7_1_1_10.realAnswer).scale (-6561) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 7 (-3/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_10.realContains hm7_1_1_10.realContains) (-6561) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := -6096923757675943196402281735, hi := -6096923757674497316018478115}
lemma t9_checked : ((hm7_0_0_11.realAnswer).add hm7_1_1_11.realAnswer).scale (19683) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 7 (-3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_11.realContains hm7_1_1_11.realContains) (19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -15283380517576423622822511970, hi := -15283380517575825854901779971}
lemma t10_checked : ((hm7_0_0_12.realAnswer).add hm7_1_1_12.realAnswer).scale (-59049) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 7 (-3/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_12.realContains hm7_1_1_12.realContains) (-59049) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := 573662797108871276386922924, hi := 573662797109120302460532369}
lemma t11_checked : ((hm7_0_0_13.realAnswer).add hm7_1_1_13.realAnswer).scale (177147) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 7 (-3/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_13.realContains hm7_1_1_13.realContains) (177147) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := 2296800950435491535402168534, hi := 2296800950435595049028908807}
lemma t12_checked : ((hm7_0_0_14.realAnswer).add hm7_1_1_14.realAnswer).scale (-531441) 4096=t12 := by decide +kernel
lemma t12_contains : t12.Contains (sourcePower false 7 (-3/2) 2 12) := by
  rw [← t12_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_14.realContains hm7_1_1_14.realContains) (-531441) 4096 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t13 : RBox := {lo := 35462470994773703375313929, hi := 35462470994815999371491650}
lemma t13_checked : ((hm7_0_0_15.realAnswer).add hm7_1_1_15.realAnswer).scale (1594323) 8192=t13 := by decide +kernel
lemma t13_contains : t13.Contains (sourcePower false 7 (-3/2) 2 13) := by
  rw [← t13_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_0_0_15.realContains hm7_1_1_15.realContains) (1594323) 8192 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t14 : RBox := {lo := -59635827272770073255206325027, hi := 59635827272770073255206325027}
lemma t14_contains : t14.Contains (sourcePower false 7 (-3/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (-3/2) 2 14 coarse_7_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -23181157215230757642013722002, hi := 23181157215230757642013722002}
lemma t15_contains : t15.Contains (sourcePower false 7 (-3/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (-3/2) 2 15 coarse_7_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -8640213556041747340148343249, hi := 8640213556041747340148343249}
lemma t16_contains : t16.Contains (sourcePower false 7 (-3/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (-3/2) 2 16 coarse_7_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -3093218066606913743155163705, hi := 3093218066606913743155163705}
lemma t17_contains : t17.Contains (sourcePower false 7 (-3/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (-3/2) 2 17 coarse_7_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -1065600167768991214941304342, hi := 1065600167768991214941304342}
lemma t18_contains : t18.Contains (sourcePower false 7 (-3/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (-3/2) 2 18 coarse_7_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -353926841911464894018194304, hi := 353926841911464894018194304}
lemma t19_contains : t19.Contains (sourcePower false 7 (-3/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (-3/2) 2 19 coarse_7_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -113558584130671164338288672, hi := 113558584130671164338288672}
lemma t20_contains : t20.Contains (sourcePower false 7 (-3/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (-3/2) 2 20 coarse_7_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -35266513336522412873203574, hi := 35266513336522412873203574}
lemma t21_contains : t21.Contains (sourcePower false 7 (-3/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (-3/2) 2 21 coarse_7_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -10621228359676316661276951, hi := 10621228359676316661276951}
lemma t22_contains : t22.Contains (sourcePower false 7 (-3/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (-3/2) 2 22 coarse_7_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -3107889364519333518196917, hi := 3107889364519333518196917}
lemma t23_contains : t23.Contains (sourcePower false 7 (-3/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (-3/2) 2 23 coarse_7_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -885138717642571691851745, hi := 885138717642571691851745}
lemma t24_contains : t24.Contains (sourcePower false 7 (-3/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (-3/2) 2 24 coarse_7_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -245781283221030089397521, hi := 245781283221030089397521}
lemma t25_contains : t25.Contains (sourcePower false 7 (-3/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (-3/2) 2 25 coarse_7_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -66645088121390481702150, hi := 66645088121390481702150}
lemma t26_contains : t26.Contains (sourcePower false 7 (-3/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (-3/2) 2 26 coarse_7_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -17672863099913800238592, hi := 17672863099913800238592}
lemma t27_contains : t27.Contains (sourcePower false 7 (-3/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (-3/2) 2 27 coarse_7_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -4589288261443940474514, hi := 4589288261443940474514}
lemma t28_contains : t28.Contains (sourcePower false 7 (-3/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 7 (-3/2) 2 28 coarse_7_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 7 (-3/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 534397849612598033175569983629, hi := 534397849612740502416964706407}
lemma t0_checked : ((hm7_1_0_2.realAnswer).add hm7_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 7 (-3/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_2.realContains hm7_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 37810011682425707760461036743, hi := 37810011682591550424492721890}
lemma t1_checked : ((hm7_1_0_3.realAnswer).add hm7_0_1_3.realAnswer).scale (-3) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 7 (-3/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_3.realContains hm7_0_1_3.realContains) (-3) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -889743510270384551376508391805, hi := -889743510270237203031227751436}
lemma t2_checked : ((hm7_1_0_4.realAnswer).add hm7_0_1_4.realAnswer).scale (9) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 7 (-3/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_4.realContains hm7_0_1_4.realContains) (9) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 27988475507964415035413389191, hi := 27988475508070466005695896592}
lemma t3_checked : ((hm7_1_0_5.realAnswer).add hm7_0_1_5.realAnswer).scale (-27) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 7 (-3/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_5.realContains hm7_0_1_5.realContains) (-27) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 645376572783780876861954527840, hi := 645376572783845434198859224240}
lemma t4_checked : ((hm7_1_0_6.realAnswer).add hm7_0_1_6.realAnswer).scale (81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 7 (-3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_6.realContains hm7_0_1_6.realContains) (81) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -54758069036458695855634222194, hi := -54758069036424248219801982937}
lemma t5_checked : ((hm7_1_0_7.realAnswer).add hm7_0_1_7.realAnswer).scale (-243) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 7 (-3/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_7.realContains hm7_0_1_7.realContains) (-243) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -271686031507132361227704767472, hi := -271686031507115699281577353415}
lemma t6_checked : ((hm7_1_0_8.realAnswer).add hm7_0_1_8.realAnswer).scale (729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 7 (-3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_8.realContains hm7_0_1_8.realContains) (729) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 25291111961062144126044632701, hi := 25291111961069700837043101586}
lemma t7_checked : ((hm7_1_0_9.realAnswer).add hm7_0_1_9.realAnswer).scale (-2187) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 7 (-3/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_9.realContains hm7_0_1_9.realContains) (-2187) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 76423717600298001464621363170, hi := 76423717600301321045499471030}
lemma t8_checked : ((hm7_1_0_10.realAnswer).add hm7_0_1_10.realAnswer).scale (6561) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 7 (-3/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_10.realContains hm7_0_1_10.realContains) (6561) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := -5367744937346352151568382500, hi := -5367744937344903841562373583}
lemma t9_checked : ((hm7_1_0_11.realAnswer).add hm7_0_1_11.realAnswer).scale (-19683) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 7 (-3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_11.realContains hm7_0_1_11.realContains) (-19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -15453497585249361983834367138, hi := -15453497585248727828855915572}
lemma t10_checked : ((hm7_1_0_12.realAnswer).add hm7_0_1_12.realAnswer).scale (59049) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 7 (-3/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_12.realContains hm7_0_1_12.realContains) (59049) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := 436840520699280777307262717, hi := 436840520699557981267517467}
lemma t11_checked : ((hm7_1_0_13.realAnswer).add hm7_0_1_13.realAnswer).scale (-177147) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 7 (-3/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_13.realContains hm7_0_1_13.realContains) (-177147) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := 2325619378504694554879562761, hi := 2325619378504813865261776415}
lemma t12_checked : ((hm7_1_0_14.realAnswer).add hm7_0_1_14.realAnswer).scale (531441) 4096=t12 := by decide +kernel
lemma t12_contains : t12.Contains (sourcePower true 7 (-3/2) 2 12) := by
  rw [← t12_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_14.realContains hm7_0_1_14.realContains) (531441) 4096 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t13 : RBox := {lo := 55149369759226232989947346, hi := 55149369759276092621095395}
lemma t13_checked : ((hm7_1_0_15.realAnswer).add hm7_0_1_15.realAnswer).scale (-1594323) 8192=t13 := by decide +kernel
lemma t13_contains : t13.Contains (sourcePower true 7 (-3/2) 2 13) := by
  rw [← t13_checked]
  convert RBox.contains_scale (RBox.contains_add hm7_1_0_15.realContains hm7_0_1_15.realContains) (-1594323) 8192 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t14 : RBox := {lo := -59635827272770073255206325027, hi := 59635827272770073255206325027}
lemma t14_contains : t14.Contains (sourcePower true 7 (-3/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (-3/2) 2 14 coarse_7_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -23181157215230757642013722002, hi := 23181157215230757642013722002}
lemma t15_contains : t15.Contains (sourcePower true 7 (-3/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (-3/2) 2 15 coarse_7_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -8640213556041747340148343249, hi := 8640213556041747340148343249}
lemma t16_contains : t16.Contains (sourcePower true 7 (-3/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (-3/2) 2 16 coarse_7_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -3093218066606913743155163705, hi := 3093218066606913743155163705}
lemma t17_contains : t17.Contains (sourcePower true 7 (-3/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (-3/2) 2 17 coarse_7_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -1065600167768991214941304342, hi := 1065600167768991214941304342}
lemma t18_contains : t18.Contains (sourcePower true 7 (-3/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (-3/2) 2 18 coarse_7_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -353926841911464894018194304, hi := 353926841911464894018194304}
lemma t19_contains : t19.Contains (sourcePower true 7 (-3/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (-3/2) 2 19 coarse_7_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -113558584130671164338288672, hi := 113558584130671164338288672}
lemma t20_contains : t20.Contains (sourcePower true 7 (-3/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (-3/2) 2 20 coarse_7_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -35266513336522412873203574, hi := 35266513336522412873203574}
lemma t21_contains : t21.Contains (sourcePower true 7 (-3/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (-3/2) 2 21 coarse_7_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -10621228359676316661276951, hi := 10621228359676316661276951}
lemma t22_contains : t22.Contains (sourcePower true 7 (-3/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (-3/2) 2 22 coarse_7_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -3107889364519333518196917, hi := 3107889364519333518196917}
lemma t23_contains : t23.Contains (sourcePower true 7 (-3/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (-3/2) 2 23 coarse_7_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -885138717642571691851745, hi := 885138717642571691851745}
lemma t24_contains : t24.Contains (sourcePower true 7 (-3/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (-3/2) 2 24 coarse_7_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -245781283221030089397521, hi := 245781283221030089397521}
lemma t25_contains : t25.Contains (sourcePower true 7 (-3/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (-3/2) 2 25 coarse_7_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -66645088121390481702150, hi := 66645088121390481702150}
lemma t26_contains : t26.Contains (sourcePower true 7 (-3/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (-3/2) 2 26 coarse_7_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -17672863099913800238592, hi := 17672863099913800238592}
lemma t27_contains : t27.Contains (sourcePower true 7 (-3/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (-3/2) 2 27 coarse_7_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -4589288261443940474514, hi := 4589288261443940474514}
lemma t28_contains : t28.Contains (sourcePower true 7 (-3/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 7 (-3/2) 2 28 coarse_7_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 7 (-3/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 7 (-3/2) 2) k.val := by
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
end SharpPlanar.Bernstein7

end OAI
