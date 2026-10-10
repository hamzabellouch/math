import OAI.Analysis.PlanarPacking.Certificate.LowBlock9_0
import OAI.Analysis.PlanarPacking.Certificate.LowBlock9_1
import OAI.Analysis.PlanarPacking.Certificate.LowBlock9_2
import OAI.Analysis.PlanarPacking.Certificate.LowBlock9_10
import OAI.Analysis.PlanarPacking.Certificate.LowBlock9_11
import OAI.Analysis.PlanarPacking.Certificate.LowBlock9_12
import OAI.Analysis.PlanarPacking.Certificate.CoarseBound9

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein9
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 605365557382180493631069218907, hi := 605365557382352959360858647297}
lemma t0_checked : ((hm9_0_0_2.realAnswer).add hm9_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 9 (3/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_2.realContains hm9_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 169565919880559690283463010170, hi := 169565919880759686781405130432}
lemma t1_checked : ((hm9_0_0_3.realAnswer).add hm9_1_1_3.realAnswer).scale (-3) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 9 (3/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_3.realContains hm9_1_1_3.realContains) (-3) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -931795867709845887899869622298, hi := -931795867709669445009309258651}
lemma t2_checked : ((hm9_0_0_4.realAnswer).add hm9_1_1_4.realAnswer).scale (-9) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 9 (3/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_4.realContains hm9_1_1_4.realContains) (-9) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -145312854860992720572786584200, hi := -145312854860867351899625310514}
lemma t3_checked : ((hm9_0_0_5.realAnswer).add hm9_1_1_5.realAnswer).scale (-27) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 9 (3/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_5.realContains hm9_1_1_5.realContains) (-27) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 622132053362007275702123884390, hi := 622132053362081846847430086627}
lemma t4_checked : ((hm9_0_0_6.realAnswer).add hm9_1_1_6.realAnswer).scale (-81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 9 (3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_6.realContains hm9_1_1_6.realContains) (-81) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 35706268276574729192001551923, hi := 35706268276612925140483172263}
lemma t5_checked : ((hm9_0_0_7.realAnswer).add hm9_1_1_7.realAnswer).scale (-243) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 9 (3/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_7.realContains hm9_1_1_7.realContains) (-243) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -236855394506246711047709000212, hi := -236855394506229487175726976258}
lemma t6_checked : ((hm9_0_0_8.realAnswer).add hm9_1_1_8.realAnswer).scale (-729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 9 (3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_8.realContains hm9_1_1_8.realContains) (-729) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 3258090993264099459765015992, hi := 3258090993271067195810697014}
lemma t7_checked : ((hm9_0_0_9.realAnswer).add hm9_1_1_9.realAnswer).scale (-2187) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 9 (3/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_9.realContains hm9_1_1_9.realContains) (-2187) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 58450554917120036656318194012, hi := 58450554917122611006537779629}
lemma t8_checked : ((hm9_0_0_10.realAnswer).add hm9_1_1_10.realAnswer).scale (-6561) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 9 (3/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_10.realContains hm9_1_1_10.realContains) (-6561) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := -4032488213219993910130210758, hi := -4032488213219108526718906656}
lemma t9_checked : ((hm9_0_0_11.realAnswer).add hm9_1_1_11.realAnswer).scale (-19683) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 9 (3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_11.realContains hm9_1_1_11.realContains) (-19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -10046495091273870911863894100, hi := -10046495091273581170000809595}
lemma t10_checked : ((hm9_0_0_12.realAnswer).add hm9_1_1_12.realAnswer).scale (-59049) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 9 (3/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_12.realContains hm9_1_1_12.realContains) (-59049) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := 1167131754046480829117473878, hi := 1167131754046573335887279891}
lemma t11_checked : ((hm9_0_0_13.realAnswer).add hm9_1_1_13.realAnswer).scale (-177147) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 9 (3/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_13.realContains hm9_1_1_13.realContains) (-177147) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := 1254286673237585191266652113, hi := 1254286673237614749437573759}
lemma t12_checked : ((hm9_0_0_14.realAnswer).add hm9_1_1_14.realAnswer).scale (-531441) 4096=t12 := by decide +kernel
lemma t12_contains : t12.Contains (sourcePower false 9 (3/2) 2 12) := by
  rw [← t12_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_14.realContains hm9_1_1_14.realContains) (-531441) 4096 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t13 : RBox := {lo := -201245381137807538532278116, hi := -201245381137797880812617639}
lemma t13_checked : ((hm9_0_0_15.realAnswer).add hm9_1_1_15.realAnswer).scale (-1594323) 8192=t13 := by decide +kernel
lemma t13_contains : t13.Contains (sourcePower false 9 (3/2) 2 13) := by
  rw [← t13_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_15.realContains hm9_1_1_15.realContains) (-1594323) 8192 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t14 : RBox := {lo := -24725698809176516053168060546, hi := 24725698809176516053168060546}
lemma t14_contains : t14.Contains (sourcePower false 9 (3/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (3/2) 2 14 coarse_9_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -8955548517723090074167299394, hi := 8955548517723090074167299394}
lemma t15_contains : t15.Contains (sourcePower false 9 (3/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (3/2) 2 15 coarse_9_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -3117343267724612720253941592, hi := 3117343267724612720253941592}
lemma t16_contains : t16.Contains (sourcePower false 9 (3/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (3/2) 2 16 coarse_9_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -1043611529103946578452946112, hi := 1043611529103946578452946112}
lemma t17_contains : t17.Contains (sourcePower false 9 (3/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (3/2) 2 17 coarse_9_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -336330703192688062311941054, hi := 336330703192688062311941054}
lemma t18_contains : t18.Contains (sourcePower false 9 (3/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (3/2) 2 18 coarse_9_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -104464247929191556467561863, hi := 104464247929191556467561863}
lemma t19_contains : t19.Contains (sourcePower false 9 (3/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (3/2) 2 19 coarse_9_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -31311921055406004370038208, hi := 31311921055406004370038208}
lemma t20_contains : t20.Contains (sourcePower false 9 (3/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (3/2) 2 20 coarse_9_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -9069918620381098445985624, hi := 9069918620381098445985624}
lemma t21_contains : t21.Contains (sourcePower false 9 (3/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (3/2) 2 21 coarse_9_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -2542619576258117963444198, hi := 2542619576258117963444198}
lemma t22_contains : t22.Contains (sourcePower false 9 (3/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (3/2) 2 22 coarse_9_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -690845821005163497155363, hi := 690845821005163497155363}
lemma t23_contains : t23.Contains (sourcePower false 9 (3/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (3/2) 2 23 coarse_9_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -182193425404558644194995, hi := 182193425404558644194995}
lemma t24_contains : t24.Contains (sourcePower false 9 (3/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (3/2) 2 24 coarse_9_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -46703709063382411011594, hi := 46703709063382411011594}
lemma t25_contains : t25.Contains (sourcePower false 9 (3/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (3/2) 2 25 coarse_9_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -11652904893164252489548, hi := 11652904893164252489548}
lemma t26_contains : t26.Contains (sourcePower false 9 (3/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (3/2) 2 26 coarse_9_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -2833736695269006434692, hi := 2833736695269006434692}
lemma t27_contains : t27.Contains (sourcePower false 9 (3/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (3/2) 2 27 coarse_9_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -672493511073217294268, hi := 672493511073217294268}
lemma t28_contains : t28.Contains (sourcePower false 9 (3/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (3/2) 2 28 coarse_9_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 9 (3/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (3/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 591165432265968608758287079912, hi := 591165432266110259605276998427}
lemma t0_checked : ((hm9_1_0_2.realAnswer).add hm9_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 9 (3/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_2.realContains hm9_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 155001729746009109798635320134, hi := 155001729746173399385591304305}
lemma t1_checked : ((hm9_1_0_3.realAnswer).add hm9_0_1_3.realAnswer).scale (3) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 9 (3/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_3.realContains hm9_0_1_3.realContains) (3) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -915134525199863478120788667543, hi := -915134525199718475194284673725}
lemma t2_checked : ((hm9_1_0_4.realAnswer).add hm9_0_1_4.realAnswer).scale (9) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 9 (3/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_4.realContains hm9_0_1_4.realContains) (9) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -126183521945859327441938410424, hi := -126183521945756216977481464812}
lemma t3_checked : ((hm9_1_0_5.realAnswer).add hm9_0_1_5.realAnswer).scale (27) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 9 (3/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_5.realContains hm9_0_1_5.realContains) (27) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 613506120086188790114456588199, hi := 613506120086250207421621517384}
lemma t4_checked : ((hm9_1_0_6.realAnswer).add hm9_0_1_6.realAnswer).scale (81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 9 (3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_6.realContains hm9_0_1_6.realContains) (81) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 24494390619679776732597695897, hi := 24494390619711313196862567832}
lemma t5_checked : ((hm9_1_0_7.realAnswer).add hm9_0_1_7.realAnswer).scale (243) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 9 (3/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_7.realContains hm9_0_1_7.realContains) (243) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -234189388031273117819028211240, hi := -234189388031258834422975863898}
lemma t6_checked : ((hm9_1_0_8.realAnswer).add hm9_0_1_8.realAnswer).scale (729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 9 (3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_8.realContains hm9_0_1_8.realContains) (729) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 7169031003612025130043747904, hi := 7169031003617847917899650727}
lemma t7_checked : ((hm9_1_0_9.realAnswer).add hm9_0_1_9.realAnswer).scale (2187) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 9 (3/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_9.realContains hm9_0_1_9.realContains) (2187) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 57876400345449285183859756859, hi := 57876400345451465035146314387}
lemma t8_checked : ((hm9_1_0_10.realAnswer).add hm9_0_1_10.realAnswer).scale (6561) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 9 (3/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_10.realContains hm9_0_1_10.realContains) (6561) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := -4943241685584564863198770381, hi := -4943241685583798748354525310}
lemma t9_checked : ((hm9_1_0_11.realAnswer).add hm9_0_1_11.realAnswer).scale (19683) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 9 (3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_11.realContains hm9_0_1_11.realContains) (19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -9951228001178267868760853552, hi := -9951228001178008679087383083}
lemma t10_checked : ((hm9_1_0_12.realAnswer).add hm9_0_1_12.realAnswer).scale (59049) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 9 (3/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_12.realContains hm9_0_1_12.realContains) (59049) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := 1318108745620848407039940569, hi := 1318108745620935064311596400}
lemma t11_checked : ((hm9_1_0_13.realAnswer).add hm9_0_1_13.realAnswer).scale (177147) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 9 (3/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_13.realContains hm9_0_1_13.realContains) (177147) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := 1241325247514899819877639881, hi := 1241325247514929094071635838}
lemma t12_checked : ((hm9_1_0_14.realAnswer).add hm9_0_1_14.realAnswer).scale (531441) 4096=t12 := by decide +kernel
lemma t12_contains : t12.Contains (sourcePower true 9 (3/2) 2 12) := by
  rw [← t12_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_14.realContains hm9_0_1_14.realContains) (531441) 4096 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t13 : RBox := {lo := -219801453023136476948551981, hi := -219801453023126353177856461}
lemma t13_checked : ((hm9_1_0_15.realAnswer).add hm9_0_1_15.realAnswer).scale (1594323) 8192=t13 := by decide +kernel
lemma t13_contains : t13.Contains (sourcePower true 9 (3/2) 2 13) := by
  rw [← t13_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_15.realContains hm9_0_1_15.realContains) (1594323) 8192 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t14 : RBox := {lo := -24725698809176516053168060546, hi := 24725698809176516053168060546}
lemma t14_contains : t14.Contains (sourcePower true 9 (3/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (3/2) 2 14 coarse_9_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -8955548517723090074167299394, hi := 8955548517723090074167299394}
lemma t15_contains : t15.Contains (sourcePower true 9 (3/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (3/2) 2 15 coarse_9_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -3117343267724612720253941592, hi := 3117343267724612720253941592}
lemma t16_contains : t16.Contains (sourcePower true 9 (3/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (3/2) 2 16 coarse_9_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -1043611529103946578452946112, hi := 1043611529103946578452946112}
lemma t17_contains : t17.Contains (sourcePower true 9 (3/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (3/2) 2 17 coarse_9_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -336330703192688062311941054, hi := 336330703192688062311941054}
lemma t18_contains : t18.Contains (sourcePower true 9 (3/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (3/2) 2 18 coarse_9_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -104464247929191556467561863, hi := 104464247929191556467561863}
lemma t19_contains : t19.Contains (sourcePower true 9 (3/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (3/2) 2 19 coarse_9_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -31311921055406004370038208, hi := 31311921055406004370038208}
lemma t20_contains : t20.Contains (sourcePower true 9 (3/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (3/2) 2 20 coarse_9_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -9069918620381098445985624, hi := 9069918620381098445985624}
lemma t21_contains : t21.Contains (sourcePower true 9 (3/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (3/2) 2 21 coarse_9_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -2542619576258117963444198, hi := 2542619576258117963444198}
lemma t22_contains : t22.Contains (sourcePower true 9 (3/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (3/2) 2 22 coarse_9_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -690845821005163497155363, hi := 690845821005163497155363}
lemma t23_contains : t23.Contains (sourcePower true 9 (3/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (3/2) 2 23 coarse_9_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -182193425404558644194995, hi := 182193425404558644194995}
lemma t24_contains : t24.Contains (sourcePower true 9 (3/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (3/2) 2 24 coarse_9_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -46703709063382411011594, hi := 46703709063382411011594}
lemma t25_contains : t25.Contains (sourcePower true 9 (3/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (3/2) 2 25 coarse_9_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -11652904893164252489548, hi := 11652904893164252489548}
lemma t26_contains : t26.Contains (sourcePower true 9 (3/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (3/2) 2 26 coarse_9_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -2833736695269006434692, hi := 2833736695269006434692}
lemma t27_contains : t27.Contains (sourcePower true 9 (3/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (3/2) 2 27 coarse_9_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -672493511073217294268, hi := 672493511073217294268}
lemma t28_contains : t28.Contains (sourcePower true 9 (3/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (3/2) 2 28 coarse_9_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 9 (3/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (3/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 605365557382180493631069218907, hi := 605365557382352959360858647297}
lemma t0_checked : ((hm9_0_0_2.realAnswer).add hm9_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 9 (-1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_2.realContains hm9_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -113043946587173124520936753621, hi := -113043946587039793522308673447}
lemma t1_checked : ((hm9_0_0_3.realAnswer).add hm9_1_1_3.realAnswer).scale (1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 9 (-1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_3.realContains hm9_1_1_3.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -414131496759931505733275387688, hi := -414131496759853086670804114956}
lemma t2_checked : ((hm9_0_0_4.realAnswer).add hm9_1_1_4.realAnswer).scale (-1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 9 (-1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_4.realContains hm9_1_1_4.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 43055660699516252414703795708, hi := 43055660699553398688233061985}
lemma t3_checked : ((hm9_0_0_5.realAnswer).add hm9_1_1_5.realAnswer).scale (1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 9 (-1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_5.realContains hm9_1_1_5.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 122890282145581684089308421608, hi := 122890282145596414192084955383}
lemma t4_checked : ((hm9_0_0_6.realAnswer).add hm9_1_1_6.realAnswer).scale (-1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 9 (-1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_6.realContains hm9_1_1_6.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -4702060019965488084343463014, hi := -4702060019960458165201850459}
lemma t5_checked : ((hm9_0_0_7.realAnswer).add hm9_1_1_7.realAnswer).scale (1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 9 (-1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_7.realContains hm9_1_1_7.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -20793889229629340887590364902, hi := -20793889229627828778115948533}
lemma t6_checked : ((hm9_0_0_8.realAnswer).add hm9_1_1_8.realAnswer).scale (-1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 9 (-1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_8.realContains hm9_1_1_8.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -190688453195563146348316972, hi := -190688453195155341037915888}
lemma t7_checked : ((hm9_0_0_9.realAnswer).add hm9_1_1_9.realAnswer).scale (1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 9 (-1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_9.realContains hm9_1_1_9.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 2280649605057571922575439364, hi := 2280649605057672369710969606}
lemma t8_checked : ((hm9_0_0_10.realAnswer).add hm9_1_1_10.realAnswer).scale (-1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 9 (-1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_10.realContains hm9_1_1_10.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := 104894272477172360193064076, hi := 104894272477195391047435244}
lemma t9_checked : ((hm9_0_0_11.realAnswer).add hm9_1_1_11.realAnswer).scale (1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 9 (-1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_11.realContains hm9_1_1_11.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -174221595174591336241911422, hi := -174221595174586311674724873}
lemma t10_checked : ((hm9_0_0_12.realAnswer).add hm9_1_1_12.realAnswer).scale (-1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 9 (-1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_12.realContains hm9_1_1_12.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -13493233485677895713148680, hi := -13493233485676826240538008}
lemma t11_checked : ((hm9_0_0_13.realAnswer).add hm9_1_1_13.realAnswer).scale (1) 1=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 9 (-1/1) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_13.realContains hm9_1_1_13.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := 9667222163102110946329333, hi := 9667222163102338761398353}
lemma t12_checked : ((hm9_0_0_14.realAnswer).add hm9_1_1_14.realAnswer).scale (-1) 1=t12 := by decide +kernel
lemma t12_contains : t12.Contains (sourcePower false 9 (-1/1) 2 12) := by
  rw [← t12_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_14.realContains hm9_1_1_14.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t13 : RBox := {lo := 1034045273310891356153655, hi := 1034045273310940979749036}
lemma t13_checked : ((hm9_0_0_15.realAnswer).add hm9_1_1_15.realAnswer).scale (1) 1=t13 := by decide +kernel
lemma t13_contains : t13.Contains (sourcePower false 9 (-1/1) 2 13) := by
  rw [← t13_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_0_0_15.realContains hm9_1_1_15.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t14 : RBox := {lo := -84697569499101507665030968, hi := 84697569499101507665030968}
lemma t14_contains : t14.Contains (sourcePower false 9 (-1/1) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (-1/1) 2 14 coarse_9_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -20451412349996429383110091, hi := 20451412349996429383110091}
lemma t15_contains : t15.Contains (sourcePower false 9 (-1/1) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (-1/1) 2 15 coarse_9_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -4745964469479573583190281, hi := 4745964469479573583190281}
lemma t16_contains : t16.Contains (sourcePower false 9 (-1/1) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (-1/1) 2 16 coarse_9_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -1059223150761490721759307, hi := 1059223150761490721759307}
lemma t17_contains : t17.Contains (sourcePower false 9 (-1/1) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (-1/1) 2 17 coarse_9_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -227574633663074075069637, hi := 227574633663074075069637}
lemma t18_contains : t18.Contains (sourcePower false 9 (-1/1) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (-1/1) 2 18 coarse_9_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -47123089918544105667460, hi := 47123089918544105667460}
lemma t19_contains : t19.Contains (sourcePower false 9 (-1/1) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (-1/1) 2 19 coarse_9_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -9416392055435665704734, hi := 9416392055435665704734}
lemma t20_contains : t20.Contains (sourcePower false 9 (-1/1) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (-1/1) 2 20 coarse_9_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -1818389647599499070968, hi := 1818389647599499070968}
lemma t21_contains : t21.Contains (sourcePower false 9 (-1/1) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (-1/1) 2 21 coarse_9_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -339839367824252017804, hi := 339839367824252017804}
lemma t22_contains : t22.Contains (sourcePower false 9 (-1/1) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (-1/1) 2 22 coarse_9_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -61557670487205021490, hi := 61557670487205021490}
lemma t23_contains : t23.Contains (sourcePower false 9 (-1/1) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (-1/1) 2 23 coarse_9_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -10822871042022909343, hi := 10822871042022909343}
lemma t24_contains : t24.Contains (sourcePower false 9 (-1/1) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (-1/1) 2 24 coarse_9_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -1849566266381483885, hi := 1849566266381483885}
lemma t25_contains : t25.Contains (sourcePower false 9 (-1/1) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (-1/1) 2 25 coarse_9_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -307653221096403378, hi := 307653221096403378}
lemma t26_contains : t26.Contains (sourcePower false 9 (-1/1) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (-1/1) 2 26 coarse_9_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -49876445975286458, hi := 49876445975286458}
lemma t27_contains : t27.Contains (sourcePower false 9 (-1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (-1/1) 2 27 coarse_9_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -7891014557979819, hi := 7891014557979819}
lemma t28_contains : t28.Contains (sourcePower false 9 (-1/1) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 9 (-1/1) 2 28 coarse_9_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 9 (-1/1) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 9 (-1/1) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 591165432265968608758287079912, hi := 591165432266110259605276998427}
lemma t0_checked : ((hm9_1_0_2.realAnswer).add hm9_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 9 (-1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_2.realContains hm9_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -103334486497448932923727536203, hi := -103334486497339406532423546756}
lemma t1_checked : ((hm9_1_0_3.realAnswer).add hm9_0_1_3.realAnswer).scale (-1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 9 (-1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_3.realContains hm9_0_1_3.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -406726455644383768053683852241, hi := -406726455644319322308570966100}
lemma t2_checked : ((hm9_1_0_4.realAnswer).add hm9_0_1_4.realAnswer).scale (1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 9 (-1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_4.realContains hm9_0_1_4.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 37387710206149990215550063648, hi := 37387710206180541464278047533}
lemma t3_checked : ((hm9_1_0_5.realAnswer).add hm9_0_1_5.realAnswer).scale (-1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 9 (-1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_5.realContains hm9_0_1_5.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 121186394091099020269522289027, hi := 121186394091111152083283262693}
lemma t4_checked : ((hm9_1_0_6.realAnswer).add hm9_0_1_6.realAnswer).scale (1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 9 (-1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_6.realContains hm9_0_1_6.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -3225598764735646182302889591, hi := -3225598764731493232276239789}
lemma t5_checked : ((hm9_1_0_7.realAnswer).add hm9_0_1_7.realAnswer).scale (-1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 9 (-1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_7.realContains hm9_0_1_7.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -20559836534981453416210981508, hi := -20559836534980199455515027832}
lemma t6_checked : ((hm9_1_0_8.realAnswer).add hm9_0_1_8.realAnswer).scale (1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 9 (-1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_8.realContains hm9_0_1_8.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -419586633956600152487953952, hi := -419586633956259358319890138}
lemma t7_checked : ((hm9_1_0_9.realAnswer).add hm9_0_1_9.realAnswer).scale (-1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 9 (-1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_9.realContains hm9_0_1_9.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 2258246988025456029121795116, hi := 2258246988025541083523465399}
lemma t8_checked : ((hm9_1_0_10.realAnswer).add hm9_0_1_10.realAnswer).scale (1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 9 (-1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_10.realContains hm9_0_1_10.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := 128585060357613420675583852, hi := 128585060357633349080819511}
lemma t9_checked : ((hm9_1_0_11.realAnswer).add hm9_0_1_11.realAnswer).scale (-1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 9 (-1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_11.realContains hm9_0_1_11.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -172569518081704115185881455, hi := -172569518081699620440405092}
lemma t10_checked : ((hm9_1_0_12.realAnswer).add hm9_0_1_12.realAnswer).scale (1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 9 (-1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_12.realContains hm9_0_1_12.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -15238681496337363950335876, hi := -15238681496336362103889980}
lemma t11_checked : ((hm9_1_0_13.realAnswer).add hm9_0_1_13.realAnswer).scale (-1) 1=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 9 (-1/1) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_13.realContains hm9_0_1_13.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := 9567323962247981736860372, hi := 9567323962248207363220791}
lemma t12_checked : ((hm9_1_0_14.realAnswer).add hm9_0_1_14.realAnswer).scale (1) 1=t12 := by decide +kernel
lemma t12_contains : t12.Contains (sourcePower true 9 (-1/1) 2 12) := by
  rw [← t12_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_14.realContains hm9_0_1_14.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t13 : RBox := {lo := 1129390658709340005276848, hi := 1129390658709392023550145}
lemma t13_checked : ((hm9_1_0_15.realAnswer).add hm9_0_1_15.realAnswer).scale (-1) 1=t13 := by decide +kernel
lemma t13_contains : t13.Contains (sourcePower true 9 (-1/1) 2 13) := by
  rw [← t13_checked]
  convert RBox.contains_scale (RBox.contains_add hm9_1_0_15.realContains hm9_0_1_15.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t14 : RBox := {lo := -84697569499101507665030968, hi := 84697569499101507665030968}
lemma t14_contains : t14.Contains (sourcePower true 9 (-1/1) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (-1/1) 2 14 coarse_9_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -20451412349996429383110091, hi := 20451412349996429383110091}
lemma t15_contains : t15.Contains (sourcePower true 9 (-1/1) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (-1/1) 2 15 coarse_9_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -4745964469479573583190281, hi := 4745964469479573583190281}
lemma t16_contains : t16.Contains (sourcePower true 9 (-1/1) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (-1/1) 2 16 coarse_9_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -1059223150761490721759307, hi := 1059223150761490721759307}
lemma t17_contains : t17.Contains (sourcePower true 9 (-1/1) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (-1/1) 2 17 coarse_9_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -227574633663074075069637, hi := 227574633663074075069637}
lemma t18_contains : t18.Contains (sourcePower true 9 (-1/1) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (-1/1) 2 18 coarse_9_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -47123089918544105667460, hi := 47123089918544105667460}
lemma t19_contains : t19.Contains (sourcePower true 9 (-1/1) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (-1/1) 2 19 coarse_9_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -9416392055435665704734, hi := 9416392055435665704734}
lemma t20_contains : t20.Contains (sourcePower true 9 (-1/1) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (-1/1) 2 20 coarse_9_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -1818389647599499070968, hi := 1818389647599499070968}
lemma t21_contains : t21.Contains (sourcePower true 9 (-1/1) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (-1/1) 2 21 coarse_9_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -339839367824252017804, hi := 339839367824252017804}
lemma t22_contains : t22.Contains (sourcePower true 9 (-1/1) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (-1/1) 2 22 coarse_9_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -61557670487205021490, hi := 61557670487205021490}
lemma t23_contains : t23.Contains (sourcePower true 9 (-1/1) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (-1/1) 2 23 coarse_9_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -10822871042022909343, hi := 10822871042022909343}
lemma t24_contains : t24.Contains (sourcePower true 9 (-1/1) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (-1/1) 2 24 coarse_9_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -1849566266381483885, hi := 1849566266381483885}
lemma t25_contains : t25.Contains (sourcePower true 9 (-1/1) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (-1/1) 2 25 coarse_9_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -307653221096403378, hi := 307653221096403378}
lemma t26_contains : t26.Contains (sourcePower true 9 (-1/1) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (-1/1) 2 26 coarse_9_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -49876445975286458, hi := 49876445975286458}
lemma t27_contains : t27.Contains (sourcePower true 9 (-1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (-1/1) 2 27 coarse_9_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -7891014557979819, hi := 7891014557979819}
lemma t28_contains : t28.Contains (sourcePower true 9 (-1/1) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 9 (-1/1) 2 28 coarse_9_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 9 (-1/1) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 9 (-1/1) 2) k.val := by
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
end SharpPlanar.Bernstein9

end OAI
