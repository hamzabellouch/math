import OAI.Analysis.PlanarPacking.Certificate.LowBlock16_0
import OAI.Analysis.PlanarPacking.Certificate.LowBlock16_1
import OAI.Analysis.PlanarPacking.Certificate.LowBlock16_10
import OAI.Analysis.PlanarPacking.Certificate.LowBlock16_11
import OAI.Analysis.PlanarPacking.Certificate.CoarseBound16

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein16
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 51063328972324674031030566552, hi := 51063328972497182379882261968}
lemma t0_checked : ((hm16_0_0_2.realAnswer).add hm16_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 16 (3/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_0_0_2.realContains hm16_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 163643742167594467696855087402, hi := 163643742167794417355910966972}
lemma t1_checked : ((hm16_0_0_3.realAnswer).add hm16_1_1_3.realAnswer).scale (-3) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 16 (3/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_0_0_3.realContains hm16_1_1_3.realContains) (-3) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := 92782238220659555271129890405, hi := 92782238220835807117556203468}
lemma t2_checked : ((hm16_0_0_4.realAnswer).add hm16_1_1_4.realAnswer).scale (-9) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 16 (3/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_0_0_4.realContains hm16_1_1_4.realContains) (-9) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -147479452025031036836384190134, hi := -147479452024905996244223358259}
lemma t3_checked : ((hm16_0_0_5.realAnswer).add hm16_1_1_5.realAnswer).scale (-27) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 16 (3/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_0_0_5.realContains hm16_1_1_5.realContains) (-27) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := -128045029463135168244522236271, hi := -128045029463060999766258224656}
lemma t4_checked : ((hm16_0_0_6.realAnswer).add hm16_1_1_6.realAnswer).scale (-81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 16 (3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_0_0_6.realContains hm16_1_1_6.realContains) (-81) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 52901672261055195770100367801, hi := 52901672261092993360965922436}
lemma t5_checked : ((hm16_0_0_7.realAnswer).add hm16_1_1_7.realAnswer).scale (-243) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 16 (3/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_0_0_7.realContains hm16_1_1_7.realContains) (-243) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := 61818248685839728150464863822, hi := 61818248685856616868960918935}
lemma t6_checked : ((hm16_0_0_8.realAnswer).add hm16_1_1_8.realAnswer).scale (-729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 16 (3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_0_0_8.realContains hm16_1_1_8.realContains) (-729) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -9292451948952619246443261204, hi := -9292451948945898673299074901}
lemma t7_checked : ((hm16_0_0_9.realAnswer).add hm16_1_1_9.realAnswer).scale (-2187) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 16 (3/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_0_0_9.realContains hm16_1_1_9.realContains) (-2187) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := -16495268084191663046481648242, hi := -16495268084189251625029472982}
lemma t8_checked : ((hm16_0_0_10.realAnswer).add hm16_1_1_10.realAnswer).scale (-6561) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 16 (3/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_0_0_10.realContains hm16_1_1_10.realContains) (-6561) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := 594537075625704089905694739, hi := 594537075626492161890257230}
lemma t9_checked : ((hm16_0_0_11.realAnswer).add hm16_1_1_11.realAnswer).scale (-19683) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 16 (3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_0_0_11.realContains hm16_1_1_11.realContains) (-19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := 2839115048378496582542325352, hi := 2839115048378733132523427643}
lemma t10_checked : ((hm16_0_0_12.realAnswer).add hm16_1_1_12.realAnswer).scale (-59049) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 16 (3/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_0_0_12.realContains hm16_1_1_12.realContains) (-59049) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := 93850436036362335684848347, hi := 93850436036428029193217261}
lemma t11_checked : ((hm16_0_0_13.realAnswer).add hm16_1_1_13.realAnswer).scale (-177147) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 16 (3/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_0_0_13.realContains hm16_1_1_13.realContains) (-177147) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -61839186594498546985068715579, hi := 61839186594498546985068715579}
lemma t12_contains : t12.Contains (sourcePower false 16 (3/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (3/2) 2 12 coarse_16_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -20500998507632111319484518539, hi := 20500998507632111319484518539}
lemma t13_contains : t13.Contains (sourcePower false 16 (3/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (3/2) 2 13 coarse_16_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -6523208948461922490851005092, hi := 6523208948461922490851005092}
lemma t14_contains : t14.Contains (sourcePower false 16 (3/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (3/2) 2 14 coarse_16_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -2001108592322595368095247195, hi := 2001108592322595368095247195}
lemma t15_contains : t15.Contains (sourcePower false 16 (3/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (3/2) 2 15 coarse_16_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -593882974596011604139733432, hi := 593882974596011604139733432}
lemma t16_contains : t16.Contains (sourcePower false 16 (3/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (3/2) 2 16 coarse_16_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -170914791314823074313359263, hi := 170914791314823074313359263}
lemma t17_contains : t17.Contains (sourcePower false 16 (3/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (3/2) 2 17 coarse_16_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -47763463222836881166984422, hi := 47763463222836881166984422}
lemma t18_contains : t18.Contains (sourcePower false 16 (3/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (3/2) 2 18 coarse_16_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -12968152058503371238596043, hi := 12968152058503371238596043}
lemma t19_contains : t19.Contains (sourcePower false 16 (3/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (3/2) 2 19 coarse_16_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -3420604834478252576726273, hi := 3420604834478252576726273}
lemma t20_contains : t20.Contains (sourcePower false 16 (3/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (3/2) 2 20 coarse_16_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -876206515302459865725797, hi := 876206515302459865725797}
lemma t21_contains : t21.Contains (sourcePower false 16 (3/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (3/2) 2 21 coarse_16_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -217861827796249410693090, hi := 217861827796249410693090}
lemma t22_contains : t22.Contains (sourcePower false 16 (3/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (3/2) 2 22 coarse_16_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -52558745128403565729773, hi := 52558745128403565729773}
lemma t23_contains : t23.Contains (sourcePower false 16 (3/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (3/2) 2 23 coarse_16_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -12299393946913104075874, hi := 12299393946913104075874}
lemma t24_contains : t24.Contains (sourcePower false 16 (3/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (3/2) 2 24 coarse_16_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -2791704545697118689729, hi := 2791704545697118689729}
lemma t25_contains : t25.Contains (sourcePower false 16 (3/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (3/2) 2 25 coarse_16_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -614700496900798892964, hi := 614700496900798892964}
lemma t26_contains : t26.Contains (sourcePower false 16 (3/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (3/2) 2 26 coarse_16_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -131343900200550587389, hi := 131343900200550587389}
lemma t27_contains : t27.Contains (sourcePower false 16 (3/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (3/2) 2 27 coarse_16_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -27247313584658673303, hi := 27247313584658673303}
lemma t28_contains : t28.Contains (sourcePower false 16 (3/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (3/2) 2 28 coarse_16_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 16 (3/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (3/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 46127650728312799393830087411, hi := 46127650728454435494370449805}
lemma t0_checked : ((hm16_1_0_2.realAnswer).add hm16_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 16 (3/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_1_0_2.realContains hm16_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 148429716731693475200093008701, hi := 148429716731857633132777811894}
lemma t1_checked : ((hm16_1_0_3.realAnswer).add hm16_0_1_3.realAnswer).scale (3) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 16 (3/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_1_0_3.realContains hm16_0_1_3.realContains) (3) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := 86055431382250791464584032005, hi := 86055431382395496639326915413}
lemma t2_checked : ((hm16_1_0_4.realAnswer).add hm16_0_1_4.realAnswer).scale (9) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 16 (3/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_1_0_4.realContains hm16_0_1_4.realContains) (9) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -131232715979030111267158435668, hi := -131232715978927446603478288885}
lemma t3_checked : ((hm16_1_0_5.realAnswer).add hm16_0_1_5.realAnswer).scale (27) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 16 (3/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_1_0_5.realContains hm16_0_1_5.realContains) (27) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := -117143213135571484923620644179, hi := -117143213135510585577590236922}
lemma t4_checked : ((hm16_1_0_6.realAnswer).add hm16_0_1_6.realAnswer).scale (81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 16 (3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_1_0_6.realContains hm16_0_1_6.realContains) (81) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 45224126096886651293158318446, hi := 45224126096917688485512964990}
lemma t5_checked : ((hm16_1_0_7.realAnswer).add hm16_0_1_7.realAnswer).scale (243) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 16 (3/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_1_0_7.realContains hm16_0_1_7.realContains) (243) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := 55973725023143821634074679589, hi := 55973725023157690552575167627}
lemma t6_checked : ((hm16_1_0_8.realAnswer).add hm16_0_1_8.realAnswer).scale (729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 16 (3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_1_0_8.realContains hm16_0_1_8.realContains) (729) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -7106267733427155088812772709, hi := -7106267733421635789921980057}
lemma t7_checked : ((hm16_1_0_9.realAnswer).add hm16_0_1_9.realAnswer).scale (2187) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 16 (3/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_1_0_9.realContains hm16_0_1_9.realContains) (2187) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := -14748606002970944571372606034, hi := -14748606002968963998757626946}
lemma t8_checked : ((hm16_1_0_10.realAnswer).add hm16_0_1_10.realAnswer).scale (6561) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 16 (3/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_1_0_10.realContains hm16_0_1_10.realContains) (6561) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := 162403924362462454626460325, hi := 162403924363109803665507765}
lemma t9_checked : ((hm16_1_0_11.realAnswer).add hm16_0_1_11.realAnswer).scale (19683) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 16 (3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_1_0_11.realContains hm16_0_1_11.realContains) (19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := 2496986637181665923419889481, hi := 2496986637181860272075753862}
lemma t10_checked : ((hm16_1_0_12.realAnswer).add hm16_0_1_12.realAnswer).scale (59049) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 16 (3/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_1_0_12.realContains hm16_0_1_12.realContains) (59049) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := 158096700721604579358317962, hi := 158096700721658572999621470}
lemma t11_checked : ((hm16_1_0_13.realAnswer).add hm16_0_1_13.realAnswer).scale (177147) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 16 (3/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_1_0_13.realContains hm16_0_1_13.realContains) (177147) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -61839186594498546985068715579, hi := 61839186594498546985068715579}
lemma t12_contains : t12.Contains (sourcePower true 16 (3/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (3/2) 2 12 coarse_16_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -20500998507632111319484518539, hi := 20500998507632111319484518539}
lemma t13_contains : t13.Contains (sourcePower true 16 (3/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (3/2) 2 13 coarse_16_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -6523208948461922490851005092, hi := 6523208948461922490851005092}
lemma t14_contains : t14.Contains (sourcePower true 16 (3/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (3/2) 2 14 coarse_16_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -2001108592322595368095247195, hi := 2001108592322595368095247195}
lemma t15_contains : t15.Contains (sourcePower true 16 (3/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (3/2) 2 15 coarse_16_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -593882974596011604139733432, hi := 593882974596011604139733432}
lemma t16_contains : t16.Contains (sourcePower true 16 (3/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (3/2) 2 16 coarse_16_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -170914791314823074313359263, hi := 170914791314823074313359263}
lemma t17_contains : t17.Contains (sourcePower true 16 (3/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (3/2) 2 17 coarse_16_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -47763463222836881166984422, hi := 47763463222836881166984422}
lemma t18_contains : t18.Contains (sourcePower true 16 (3/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (3/2) 2 18 coarse_16_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -12968152058503371238596043, hi := 12968152058503371238596043}
lemma t19_contains : t19.Contains (sourcePower true 16 (3/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (3/2) 2 19 coarse_16_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -3420604834478252576726273, hi := 3420604834478252576726273}
lemma t20_contains : t20.Contains (sourcePower true 16 (3/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (3/2) 2 20 coarse_16_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -876206515302459865725797, hi := 876206515302459865725797}
lemma t21_contains : t21.Contains (sourcePower true 16 (3/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (3/2) 2 21 coarse_16_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -217861827796249410693090, hi := 217861827796249410693090}
lemma t22_contains : t22.Contains (sourcePower true 16 (3/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (3/2) 2 22 coarse_16_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -52558745128403565729773, hi := 52558745128403565729773}
lemma t23_contains : t23.Contains (sourcePower true 16 (3/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (3/2) 2 23 coarse_16_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -12299393946913104075874, hi := 12299393946913104075874}
lemma t24_contains : t24.Contains (sourcePower true 16 (3/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (3/2) 2 24 coarse_16_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -2791704545697118689729, hi := 2791704545697118689729}
lemma t25_contains : t25.Contains (sourcePower true 16 (3/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (3/2) 2 25 coarse_16_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -614700496900798892964, hi := 614700496900798892964}
lemma t26_contains : t26.Contains (sourcePower true 16 (3/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (3/2) 2 26 coarse_16_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -131343900200550587389, hi := 131343900200550587389}
lemma t27_contains : t27.Contains (sourcePower true 16 (3/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (3/2) 2 27 coarse_16_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -27247313584658673303, hi := 27247313584658673303}
lemma t28_contains : t28.Contains (sourcePower true 16 (3/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (3/2) 2 28 coarse_16_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 16 (3/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (3/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 51063328972324674031030566552, hi := 51063328972497182379882261968}
lemma t0_checked : ((hm16_0_0_2.realAnswer).add hm16_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 16 (-1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_0_0_2.realContains hm16_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -54547914055931472451970322324, hi := -54547914055864822565618362467}
lemma t1_checked : ((hm16_0_0_3.realAnswer).add hm16_1_1_3.realAnswer).scale (1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 16 (-1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_0_0_3.realContains hm16_1_1_3.realContains) (1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := 10309137580073283919014432267, hi := 10309137580092867457506244830}
lemma t2_checked : ((hm16_0_0_4.realAnswer).add hm16_1_1_4.realAnswer).scale (-1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 16 (-1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_0_0_4.realContains hm16_1_1_4.realContains) (-1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 5462201926848370231267531787, hi := 5462201926853001364310525561}
lemma t3_checked : ((hm16_0_0_5.realAnswer).add hm16_1_1_5.realAnswer).scale (1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 16 (-1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_0_0_5.realContains hm16_1_1_5.realContains) (1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := -1580802832878211953636076991, hi := -1580802832877296293410595366}
lemma t4_checked : ((hm16_0_0_6.realAnswer).add hm16_1_1_6.realAnswer).scale (-1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 16 (-1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_0_0_6.realContains hm16_1_1_6.realContains) (-1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -217702354983921783378460587, hi := -217702354983766237737038550}
lemma t5_checked : ((hm16_0_0_7.realAnswer).add hm16_1_1_7.realAnswer).scale (1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 16 (-1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_0_0_7.realContains hm16_1_1_7.realContains) (1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := 84798695042304153841515588, hi := 84798695042327320807902496}
lemma t6_checked : ((hm16_0_0_8.realAnswer).add hm16_1_1_8.realAnswer).scale (-1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 16 (-1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_0_0_8.realContains hm16_1_1_8.realContains) (-1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 4248949222197484532829938, hi := 4248949222200557497230573}
lemma t7_checked : ((hm16_0_0_9.realAnswer).add hm16_1_1_9.realAnswer).scale (1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 16 (-1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_0_0_9.realContains hm16_1_1_9.realContains) (1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := -2514139320864451005407964, hi := -2514139320864083466701641}
lemma t8_checked : ((hm16_0_0_10.realAnswer).add hm16_1_1_10.realAnswer).scale (-1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 16 (-1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_0_0_10.realContains hm16_1_1_10.realContains) (-1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := -30205612743306008326488, hi := -30205612743265970121713}
lemma t9_checked : ((hm16_0_0_11.realAnswer).add hm16_1_1_11.realAnswer).scale (1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 16 (-1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_0_0_11.realContains hm16_1_1_11.realContains) (1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := 48080662642525641120803, hi := 48080662642529647115505}
lemma t10_checked : ((hm16_0_0_12.realAnswer).add hm16_1_1_12.realAnswer).scale (-1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 16 (-1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_0_0_12.realContains hm16_1_1_12.realContains) (-1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -529788458378792918837, hi := -529788458378422077059}
lemma t11_checked : ((hm16_0_0_13.realAnswer).add hm16_1_1_13.realAnswer).scale (1) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 16 (-1/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_0_0_13.realContains hm16_1_1_13.realContains) (1) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -116361339442193107014831, hi := 116361339442193107014831}
lemma t12_contains : t12.Contains (sourcePower false 16 (-1/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (-1/2) 2 12 coarse_16_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -12858748514342521132471, hi := 12858748514342521132471}
lemma t13_contains : t13.Contains (sourcePower false 16 (-1/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (-1/2) 2 13 coarse_16_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -1363840942406677210505, hi := 1363840942406677210505}
lemma t14_contains : t14.Contains (sourcePower false 16 (-1/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (-1/2) 2 14 coarse_16_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -139460698457561636444, hi := 139460698457561636444}
lemma t15_contains : t15.Contains (sourcePower false 16 (-1/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (-1/2) 2 15 coarse_16_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -13796241869293868031, hi := 13796241869293868031}
lemma t16_contains : t16.Contains (sourcePower false 16 (-1/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (-1/2) 2 16 coarse_16_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -1323482852618229035, hi := 1323482852618229035}
lemma t17_contains : t17.Contains (sourcePower false 16 (-1/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (-1/2) 2 17 coarse_16_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -123285847235706941, hi := 123285847235706941}
lemma t18_contains : t18.Contains (sourcePower false 16 (-1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (-1/2) 2 18 coarse_16_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -11157689062837503, hi := 11157689062837503}
lemma t19_contains : t19.Contains (sourcePower false 16 (-1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (-1/2) 2 19 coarse_16_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -981019885685285, hi := 981019885685285}
lemma t20_contains : t20.Contains (sourcePower false 16 (-1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (-1/2) 2 20 coarse_16_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -83764524801244, hi := 83764524801244}
lemma t21_contains : t21.Contains (sourcePower false 16 (-1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (-1/2) 2 21 coarse_16_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -6942462444250, hi := 6942462444250}
lemma t22_contains : t22.Contains (sourcePower false 16 (-1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (-1/2) 2 22 coarse_16_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -558285218147, hi := 558285218147}
lemma t23_contains : t23.Contains (sourcePower false 16 (-1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (-1/2) 2 23 coarse_16_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -43548539931, hi := 43548539931}
lemma t24_contains : t24.Contains (sourcePower false 16 (-1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (-1/2) 2 24 coarse_16_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -3294868496, hi := 3294868496}
lemma t25_contains : t25.Contains (sourcePower false 16 (-1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (-1/2) 2 25 coarse_16_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -241830427, hi := 241830427}
lemma t26_contains : t26.Contains (sourcePower false 16 (-1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (-1/2) 2 26 coarse_16_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -17224080, hi := 17224080}
lemma t27_contains : t27.Contains (sourcePower false 16 (-1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (-1/2) 2 27 coarse_16_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -1191047, hi := 1191047}
lemma t28_contains : t28.Contains (sourcePower false 16 (-1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 16 (-1/2) 2 28 coarse_16_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 16 (-1/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 16 (-1/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 46127650728312799393830087411, hi := 46127650728454435494370449805}
lemma t0_checked : ((hm16_1_0_2.realAnswer).add hm16_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 16 (-1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_1_0_2.realContains hm16_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -49476572243952544377592603965, hi := -49476572243897825066697669567}
lemma t1_checked : ((hm16_1_0_3.realAnswer).add hm16_0_1_3.realAnswer).scale (-1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 16 (-1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_1_0_3.realContains hm16_0_1_3.realContains) (-1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := 9561714598027865718287114667, hi := 9561714598043944071036323935}
lemma t2_checked : ((hm16_1_0_4.realAnswer).add hm16_0_1_4.realAnswer).scale (1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 16 (-1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_1_0_4.realContains hm16_0_1_4.realContains) (1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 4860470962182498022351047736, hi := 4860470962186300417302164284}
lemma t3_checked : ((hm16_1_0_5.realAnswer).add hm16_0_1_5.realAnswer).scale (-1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 16 (-1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_1_0_5.realContains hm16_0_1_5.realContains) (-1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := -1446212507846561542266921534, hi := -1446212507845809698488768357}
lemma t4_checked : ((hm16_1_0_6.realAnswer).add hm16_0_1_6.realAnswer).scale (1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 16 (-1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_1_0_6.realContains hm16_0_1_6.realContains) (1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -186107514802130405290176811, hi := -186107514802002680218758512}
lemma t5_checked : ((hm16_1_0_7.realAnswer).add hm16_0_1_7.realAnswer).scale (-1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 16 (-1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_1_0_7.realContains hm16_0_1_7.realContains) (-1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := 76781515806781648332064032, hi := 76781515806800672911625745}
lemma t6_checked : ((hm16_1_0_8.realAnswer).add hm16_0_1_8.realAnswer).scale (1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 16 (-1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_1_0_8.realContains hm16_0_1_8.realContains) (1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 3249322237504177315922258, hi := 3249322237506701000828886}
lemma t7_checked : ((hm16_1_0_9.realAnswer).add hm16_0_1_9.realAnswer).scale (-1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 16 (-1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_1_0_9.realContains hm16_0_1_9.realContains) (-1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := -2247920439410294859224601, hi := -2247920439409992988684290}
lemma t8_checked : ((hm16_1_0_10.realAnswer).add hm16_0_1_10.realAnswer).scale (1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 16 (-1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_1_0_10.realContains hm16_0_1_10.realContains) (1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := -8250974158568805754484, hi := -8250974158535917016027}
lemma t9_checked : ((hm16_1_0_11.realAnswer).add hm16_0_1_11.realAnswer).scale (-1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 16 (-1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_1_0_11.realContains hm16_0_1_11.realContains) (-1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := 42286687957148570228452, hi := 42286687957151861540005}
lemma t10_checked : ((hm16_1_0_12.realAnswer).add hm16_0_1_12.realAnswer).scale (1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 16 (-1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_1_0_12.realContains hm16_0_1_12.realContains) (1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -892460502981470603508, hi := -892460502981165807822}
lemma t11_checked : ((hm16_1_0_13.realAnswer).add hm16_0_1_13.realAnswer).scale (-1) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 16 (-1/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm16_1_0_13.realContains hm16_0_1_13.realContains) (-1) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -116361339442193107014831, hi := 116361339442193107014831}
lemma t12_contains : t12.Contains (sourcePower true 16 (-1/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (-1/2) 2 12 coarse_16_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -12858748514342521132471, hi := 12858748514342521132471}
lemma t13_contains : t13.Contains (sourcePower true 16 (-1/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (-1/2) 2 13 coarse_16_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -1363840942406677210505, hi := 1363840942406677210505}
lemma t14_contains : t14.Contains (sourcePower true 16 (-1/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (-1/2) 2 14 coarse_16_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -139460698457561636444, hi := 139460698457561636444}
lemma t15_contains : t15.Contains (sourcePower true 16 (-1/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (-1/2) 2 15 coarse_16_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -13796241869293868031, hi := 13796241869293868031}
lemma t16_contains : t16.Contains (sourcePower true 16 (-1/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (-1/2) 2 16 coarse_16_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -1323482852618229035, hi := 1323482852618229035}
lemma t17_contains : t17.Contains (sourcePower true 16 (-1/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (-1/2) 2 17 coarse_16_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -123285847235706941, hi := 123285847235706941}
lemma t18_contains : t18.Contains (sourcePower true 16 (-1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (-1/2) 2 18 coarse_16_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -11157689062837503, hi := 11157689062837503}
lemma t19_contains : t19.Contains (sourcePower true 16 (-1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (-1/2) 2 19 coarse_16_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -981019885685285, hi := 981019885685285}
lemma t20_contains : t20.Contains (sourcePower true 16 (-1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (-1/2) 2 20 coarse_16_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -83764524801244, hi := 83764524801244}
lemma t21_contains : t21.Contains (sourcePower true 16 (-1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (-1/2) 2 21 coarse_16_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -6942462444250, hi := 6942462444250}
lemma t22_contains : t22.Contains (sourcePower true 16 (-1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (-1/2) 2 22 coarse_16_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -558285218147, hi := 558285218147}
lemma t23_contains : t23.Contains (sourcePower true 16 (-1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (-1/2) 2 23 coarse_16_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -43548539931, hi := 43548539931}
lemma t24_contains : t24.Contains (sourcePower true 16 (-1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (-1/2) 2 24 coarse_16_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -3294868496, hi := 3294868496}
lemma t25_contains : t25.Contains (sourcePower true 16 (-1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (-1/2) 2 25 coarse_16_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -241830427, hi := 241830427}
lemma t26_contains : t26.Contains (sourcePower true 16 (-1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (-1/2) 2 26 coarse_16_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -17224080, hi := 17224080}
lemma t27_contains : t27.Contains (sourcePower true 16 (-1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (-1/2) 2 27 coarse_16_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -1191047, hi := 1191047}
lemma t28_contains : t28.Contains (sourcePower true 16 (-1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 16 (-1/2) 2 28 coarse_16_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 16 (-1/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 16 (-1/2) 2) k.val := by
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
end SharpPlanar.Bernstein16

end OAI
