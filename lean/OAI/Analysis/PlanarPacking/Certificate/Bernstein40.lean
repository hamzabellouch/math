import OAI.Analysis.PlanarPacking.Certificate.LowBlock40_0
import OAI.Analysis.PlanarPacking.Certificate.LowBlock40_1
import OAI.Analysis.PlanarPacking.Certificate.LowBlock40_10
import OAI.Analysis.PlanarPacking.Certificate.MixedBound40
import OAI.Analysis.PlanarPacking.Certificate.CoarseBound40

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein40
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 51527189501890079450888269406, hi := 51527189502139728089012543348}
lemma t0_checked : ((hm40_0_0_2.realAnswer).add hm40_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 40 (3/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_0_0_2.realContains hm40_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 163257349005113162391136791969, hi := 163257349005397066694763899676}
lemma t1_checked : ((hm40_0_0_3.realAnswer).add hm40_1_1_3.realAnswer).scale (-3) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 40 (3/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_0_0_3.realContains hm40_1_1_3.realContains) (-3) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr2 : RBox := {lo := -1378005254342885432796058460, hi := 1378005254342885432796058460}
lemma tr2_contains : tr2.Contains (fullMoment true true 40 4) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 4 40 mixed_40_4) <;> norm_num [tr2,precision]
noncomputable def t2 : RBox := {lo := 83543377372653557933545260267, hi := 89744401017444835140922174437}
lemma t2_checked : ((hm40_0_0_4.realAnswer).add tr2).scale (-9) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 40 (3/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_0_0_4.realContains tr2_contains) (-9) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr3 : RBox := {lo := -1127662331737765183970897290, hi := 1127662331737765183970897290}
lemma tr3_contains : tr3.Contains (fullMoment true true 40 5) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 5 40 mixed_40_5) <;> norm_num [tr3,precision]
noncomputable def t3 : RBox := {lo := -158882124292789256973025315895, hi := -151270403553383759186317313350}
lemma t3_checked : ((hm40_0_0_5.realAnswer).add tr3).scale (-27) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 40 (3/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_0_0_5.realContains tr3_contains) (-27) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr4 : RBox := {lo := -770206922867263530745282246, hi := 770206922867263530745282246}
lemma tr4_contains : tr4.Contains (fullMoment true true 40 6) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 6 40 mixed_40_6) <;> norm_num [tr4,precision]
noncomputable def t4 : RBox := {lo := -128354913863081125238050050180, hi := -120556568768946041507644431813}
lemma t4_checked : ((hm40_0_0_6.realAnswer).add tr4).scale (-81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 40 (3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_0_0_6.realContains tr4_contains) (-81) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr5 : RBox := {lo := -451541240469518315478157760, hi := 451541240469518315478157760}
lemma tr5_contains : tr5.Contains (fullMoment true true 40 7) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 7 40 mixed_40_7) <;> norm_num [tr5,precision]
noncomputable def t5 : RBox := {lo := 58600097061403100437198366477, hi := 65457879651086942964199521971}
lemma t5_checked : ((hm40_0_0_7.realAnswer).add tr5).scale (-243) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 40 (3/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_0_0_7.realContains tr5_contains) (-243) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr6 : RBox := {lo := -231919502450331624380412515, hi := 231919502450331624380412515}
lemma tr6_contains : tr6.Contains (fullMoment true true 40 8) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 8 40 mixed_40_8) <;> norm_num [tr6,precision]
noncomputable def t6 : RBox := {lo := 59211466313684077033197628956, hi := 64494882478904417476703817609}
lemma t6_checked : ((hm40_0_0_8.realAnswer).add tr6).scale (-729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 40 (3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_0_0_8.realContains tr6_contains) (-729) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr7 : RBox := {lo := -105999991106160182956535889, hi := 105999991106160182956535889}
lemma tr7_contains : tr7.Contains (fullMoment true true 40 9) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 9 40 mixed_40_9) <;> norm_num [tr7,precision]
noncomputable def t7 : RBox := {lo := -15834476240752524456905481979, hi := -12212257794662248874294000011}
lemma t7_checked : ((hm40_0_0_9.realAnswer).add tr7).scale (-2187) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 40 (3/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_0_0_9.realContains tr7_contains) (-2187) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -43645893453395484376071552, hi := 43645893453395484376071552}
lemma tr8_contains : tr8.Contains (fullMoment true true 40 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 10 40 mixed_40_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := -18200868006310246800158692147, hi := -15963674983277721121686340352}
lemma t8_checked : ((hm40_0_0_10.realAnswer).add tr8).scale (-6561) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 40 (3/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_0_0_10.realContains tr8_contains) (-6561) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -16351797364128125134540904, hi := 16351797364128125134540904}
lemma tr9_contains : tr9.Contains (fullMoment true true 40 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 11 40 mixed_40_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := 1426806523037837882125503753, hi := 2684042568031663925593167247}
lemma t9_checked : ((hm40_0_0_11.realAnswer).add tr9).scale (-19683) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 40 (3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_0_0_11.realContains tr9_contains) (-19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -5619945822412676134103778, hi := 5619945822412676134103778}
lemma tr10_contains : tr10.Contains (fullMoment true true 40 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 12 40 mixed_40_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := 2744767027786655953900195155, hi := 3392915818544113390712227322}
lemma t10_checked : ((hm40_0_0_12.realAnswer).add tr10).scale (-59049) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 40 (3/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_0_0_12.realContains tr10_contains) (-59049) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -1784145647367326687478989, hi := 1784145647367326687478989}
lemma tr11_contains : tr11.Contains (fullMoment true true 40 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 13 40 mixed_40_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := -367177817251386361556666683, hi := -58529331905413898135406720}
lemma t11_checked : ((hm40_0_0_13.realAnswer).add tr11).scale (-177147) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 40 (3/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_0_0_13.realContains tr11_contains) (-177147) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -46701938752094289344693015302, hi := 46701938752094289344693015302}
lemma t12_contains : t12.Contains (sourcePower false 40 (3/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (3/2) 2 12 coarse_40_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -14226944918381974251029064191, hi := 14226944918381974251029064191}
lemma t13_contains : t13.Contains (sourcePower false 40 (3/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (3/2) 2 13 coarse_40_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -4084415447830513492880711507, hi := 4084415447830513492880711507}
lemma t14_contains : t14.Contains (sourcePower false 40 (3/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (3/2) 2 14 coarse_40_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -1108565585779813984855987127, hi := 1108565585779813984855987127}
lemma t15_contains : t15.Contains (sourcePower false 40 (3/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (3/2) 2 15 coarse_40_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -285264936549415184266627703, hi := 285264936549415184266627703}
lemma t16_contains : t16.Contains (sourcePower false 40 (3/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (3/2) 2 16 coarse_40_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -69779472687187080016182321, hi := 69779472687187080016182321}
lemma t17_contains : t17.Contains (sourcePower false 40 (3/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (3/2) 2 17 coarse_40_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -16264874903222436903988511, hi := 16264874903222436903988511}
lemma t18_contains : t18.Contains (sourcePower false 40 (3/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (3/2) 2 18 coarse_40_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -3620774099258225813167868, hi := 3620774099258225813167868}
lemma t19_contains : t19.Contains (sourcePower false 40 (3/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (3/2) 2 19 coarse_40_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -771458127210527778096725, hi := 771458127210527778096725}
lemma t20_contains : t20.Contains (sourcePower false 40 (3/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (3/2) 2 20 coarse_40_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -157645020874272310770310, hi := 157645020874272310770310}
lemma t21_contains : t21.Contains (sourcePower false 40 (3/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (3/2) 2 21 coarse_40_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -30958614408405690714176, hi := 30958614408405690714176}
lemma t22_contains : t22.Contains (sourcePower false 40 (3/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (3/2) 2 22 coarse_40_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -5854476527190135979518, hi := 5854476527190135979518}
lemma t23_contains : t23.Contains (sourcePower false 40 (3/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (3/2) 2 23 coarse_40_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -1068277418013106576834, hi := 1068277418013106576834}
lemma t24_contains : t24.Contains (sourcePower false 40 (3/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (3/2) 2 24 coarse_40_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -188487704728201524407, hi := 188487704728201524407}
lemma t25_contains : t25.Contains (sourcePower false 40 (3/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (3/2) 2 25 coarse_40_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -32228882231906787482, hi := 32228882231906787482}
lemma t26_contains : t26.Contains (sourcePower false 40 (3/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (3/2) 2 26 coarse_40_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -5352951031644319619, hi := 5352951031644319619}
lemma t27_contains : t27.Contains (sourcePower false 40 (3/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (3/2) 2 27 coarse_40_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -865811656978999856, hi := 865811656978999856}
lemma t28_contains : t28.Contains (sourcePower false 40 (3/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (3/2) 2 28 coarse_40_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 40 (3/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (3/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 55542678676135530126746154943, hi := 55542678676303547981879035176}
lemma t0_checked : ((hm40_1_0_2.realAnswer).add hm40_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 40 (3/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_1_0_2.realContains hm40_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 176294512741228386695047530922, hi := 176294512741422523645577181080}
lemma t1_checked : ((hm40_1_0_3.realAnswer).add hm40_0_1_3.realAnswer).scale (3) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 40 (3/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_1_0_3.realContains hm40_0_1_3.realContains) (3) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr2 : RBox := {lo := -1378005254342885432796058460, hi := 1378005254342885432796058460}
lemma tr2_contains : tr2.Contains (fullMoment false true 40 4) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 4 40 mixed_40_4) <;> norm_num [tr2,precision]
noncomputable def t2 : RBox := {lo := 91224876236734049914703070335, hi := 97425899881447900859689773634}
lemma t2_checked : ((hm40_1_0_4.realAnswer).add tr2).scale (9) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 40 (3/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_1_0_4.realContains tr2_contains) (9) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr3 : RBox := {lo := -1127662331737765183970897290, hi := 1127662331737765183970897290}
lemma tr3_contains : tr3.Contains (fullMoment false true 40 5) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 5 40 mixed_40_5) <;> norm_num [tr3,precision]
noncomputable def t3 : RBox := {lo := -170514417887930876063912793341, hi := -162902697148579824231517608900}
lemma t3_checked : ((hm40_1_0_5.realAnswer).add tr3).scale (27) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 40 (3/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_1_0_5.realContains tr3_contains) (27) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr4 : RBox := {lo := -770206922867263530745282246, hi := 770206922867263530745282246}
lemma tr4_contains : tr4.Contains (fullMoment false true 40 6) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 6 40 mixed_40_6) <;> norm_num [tr4,precision]
noncomputable def t4 : RBox := {lo := -138962324581811896435280419470, hi := -131163979487709010165925685600}
lemma t4_checked : ((hm40_1_0_6.realAnswer).add tr4).scale (81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 40 (3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_1_0_6.realContains tr4_contains) (81) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr5 : RBox := {lo := -451541240469518315478157760, hi := 451541240469518315478157760}
lemma tr5_contains : tr5.Contains (fullMoment false true 40 7) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 7 40 mixed_40_7) <;> norm_num [tr5,precision]
noncomputable def t5 : RBox := {lo := 62733695221372301084137056469, hi := 69591477811039733933411734255}
lemma t5_checked : ((hm40_1_0_7.realAnswer).add tr5).scale (243) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 40 (3/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_1_0_7.realContains tr5_contains) (243) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr6 : RBox := {lo := -231919502450331624380412515, hi := 231919502450331624380412515}
lemma tr6_contains : tr6.Contains (fullMoment false true 40 8) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 8 40 mixed_40_8) <;> norm_num [tr6,precision]
noncomputable def t6 : RBox := {lo := 64406523241659875117285998811, hi := 69689939406872867821585394830}
lemma t6_checked : ((hm40_1_0_8.realAnswer).add tr6).scale (729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 40 (3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_1_0_8.realContains tr6_contains) (729) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr7 : RBox := {lo := -105999991106160182956535889, hi := 105999991106160182956535889}
lemma tr7_contains : tr7.Contains (fullMoment false true 40 9) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 9 40 mixed_40_9) <;> norm_num [tr7,precision]
noncomputable def t7 : RBox := {lo := -16572847711492542502252919739, hi := -12950629265405201787764488114}
lemma t7_checked : ((hm40_1_0_9.realAnswer).add tr7).scale (2187) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 40 (3/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_1_0_9.realContains tr7_contains) (2187) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -43645893453395484376071552, hi := 43645893453395484376071552}
lemma tr8_contains : tr8.Contains (fullMoment false true 40 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 10 40 mixed_40_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := -19621010918030115925218891941, hi := -17383817894998648781765411563}
lemma t8_checked : ((hm40_1_0_10.realAnswer).add tr8).scale (6561) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 40 (3/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_1_0_10.realContains tr8_contains) (6561) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -16351797364128125134540904, hi := 16351797364128125134540904}
lemma tr9_contains : tr9.Contains (fullMoment false true 40 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 11 40 mixed_40_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := 1488133253270539957355761609, hi := 2745369298264017799839076596}
lemma t9_checked : ((hm40_1_0_11.realAnswer).add tr9).scale (19683) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 40 (3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_1_0_11.realContains tr9_contains) (19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -5619945822412676134103778, hi := 5619945822412676134103778}
lemma tr10_contains : tr10.Contains (fullMoment false true 40 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 12 40 mixed_40_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := 2997976234318846561036298146, hi := 3646125025076198668351286782}
lemma t10_checked : ((hm40_1_0_12.realAnswer).add tr10).scale (59049) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 40 (3/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_1_0_12.realContains tr10_contains) (59049) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -1784145647367326687478989, hi := 1784145647367326687478989}
lemma tr11_contains : tr11.Contains (fullMoment false true 40 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 13 40 mixed_40_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := -365892306114699728667126851, hi := -57243820768756769616437610}
lemma t11_checked : ((hm40_1_0_13.realAnswer).add tr11).scale (177147) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 40 (3/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_1_0_13.realContains tr11_contains) (177147) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -46701938752094289344693015302, hi := 46701938752094289344693015302}
lemma t12_contains : t12.Contains (sourcePower true 40 (3/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (3/2) 2 12 coarse_40_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -14226944918381974251029064191, hi := 14226944918381974251029064191}
lemma t13_contains : t13.Contains (sourcePower true 40 (3/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (3/2) 2 13 coarse_40_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -4084415447830513492880711507, hi := 4084415447830513492880711507}
lemma t14_contains : t14.Contains (sourcePower true 40 (3/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (3/2) 2 14 coarse_40_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -1108565585779813984855987127, hi := 1108565585779813984855987127}
lemma t15_contains : t15.Contains (sourcePower true 40 (3/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (3/2) 2 15 coarse_40_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -285264936549415184266627703, hi := 285264936549415184266627703}
lemma t16_contains : t16.Contains (sourcePower true 40 (3/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (3/2) 2 16 coarse_40_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -69779472687187080016182321, hi := 69779472687187080016182321}
lemma t17_contains : t17.Contains (sourcePower true 40 (3/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (3/2) 2 17 coarse_40_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -16264874903222436903988511, hi := 16264874903222436903988511}
lemma t18_contains : t18.Contains (sourcePower true 40 (3/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (3/2) 2 18 coarse_40_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -3620774099258225813167868, hi := 3620774099258225813167868}
lemma t19_contains : t19.Contains (sourcePower true 40 (3/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (3/2) 2 19 coarse_40_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -771458127210527778096725, hi := 771458127210527778096725}
lemma t20_contains : t20.Contains (sourcePower true 40 (3/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (3/2) 2 20 coarse_40_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -157645020874272310770310, hi := 157645020874272310770310}
lemma t21_contains : t21.Contains (sourcePower true 40 (3/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (3/2) 2 21 coarse_40_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -30958614408405690714176, hi := 30958614408405690714176}
lemma t22_contains : t22.Contains (sourcePower true 40 (3/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (3/2) 2 22 coarse_40_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -5854476527190135979518, hi := 5854476527190135979518}
lemma t23_contains : t23.Contains (sourcePower true 40 (3/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (3/2) 2 23 coarse_40_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -1068277418013106576834, hi := 1068277418013106576834}
lemma t24_contains : t24.Contains (sourcePower true 40 (3/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (3/2) 2 24 coarse_40_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -188487704728201524407, hi := 188487704728201524407}
lemma t25_contains : t25.Contains (sourcePower true 40 (3/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (3/2) 2 25 coarse_40_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -32228882231906787482, hi := 32228882231906787482}
lemma t26_contains : t26.Contains (sourcePower true 40 (3/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (3/2) 2 26 coarse_40_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -5352951031644319619, hi := 5352951031644319619}
lemma t27_contains : t27.Contains (sourcePower true 40 (3/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (3/2) 2 27 coarse_40_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -865811656978999856, hi := 865811656978999856}
lemma t28_contains : t28.Contains (sourcePower true 40 (3/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (3/2) 2 28 coarse_40_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 40 (3/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (3/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 51527189501890079450888269406, hi := 51527189502139728089012543348}
lemma t0_checked : ((hm40_0_0_2.realAnswer).add hm40_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 40 (-1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_0_0_2.realContains hm40_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -54419116335132355564921299892, hi := -54419116335037720797045597323}
lemma t1_checked : ((hm40_0_0_3.realAnswer).add hm40_1_1_3.realAnswer).scale (1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 40 (-1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_0_0_3.realContains hm40_1_1_3.realContains) (1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr2 : RBox := {lo := -1378005254342885432796058460, hi := 1378005254342885432796058460}
lemma tr2_contains : tr2.Contains (fullMoment true true 40 4) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 4 40 mixed_40_4) <;> norm_num [tr2,precision]
noncomputable def t2 : RBox := {lo := 9282597485850395325949473363, hi := 9971600113049426126769130493}
lemma t2_checked : ((hm40_0_0_4.realAnswer).add tr2).scale (-1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 40 (-1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_0_0_4.realContains tr2_contains) (-1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr3 : RBox := {lo := -1127662331737765183970897290, hi := 1127662331737765183970897290}
lemma tr3_contains : tr3.Contains (fullMoment true true 40 5) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 5 40 mixed_40_5) <;> norm_num [tr3,precision]
noncomputable def t3 : RBox := {lo := 5602607539014213303196937531, hi := 5884523121955157665667604293}
lemma t3_checked : ((hm40_0_0_5.realAnswer).add tr3).scale (1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 40 (-1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_0_0_5.realContains tr3_contains) (1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr4 : RBox := {lo := -770206922867263530745282246, hi := 770206922867263530745282246}
lemma tr4_contains : tr4.Contains (fullMoment true true 40 6) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 6 40 mixed_40_6) <;> norm_num [tr4,precision]
noncomputable def t4 : RBox := {lo := -1584628566210878089358642595, hi := -1488352700851185697625239898}
lemma t4_checked : ((hm40_0_0_6.realAnswer).add tr4).scale (-1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 40 (-1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_0_0_6.realContains tr4_contains) (-1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr5 : RBox := {lo := -451541240469518315478157760, hi := 451541240469518315478157760}
lemma tr5_contains : tr5.Contains (fullMoment true true 40 7) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 7 40 mixed_40_7) <;> norm_num [tr5,precision]
noncomputable def t5 : RBox := {lo := -269373990333691123309463054, hi := -241152662804127985338264882}
lemma t5_checked : ((hm40_0_0_7.realAnswer).add tr5).scale (1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 40 (-1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_0_0_7.realContains tr5_contains) (1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr6 : RBox := {lo := -231919502450331624380412515, hi := 231919502450331624380412515}
lemma tr6_contains : tr6.Contains (fullMoment true true 40 8) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 8 40 mixed_40_8) <;> norm_num [tr6,precision]
noncomputable def t6 : RBox := {lo := 81222861884340297713576994, hi := 88470346335945702985876294}
lemma t6_checked : ((hm40_0_0_8.realAnswer).add tr6).scale (-1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 40 (-1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_0_0_8.realContains tr6_contains) (-1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr7 : RBox := {lo := -105999991106160182956535889, hi := 105999991106160182956535889}
lemma tr7_contains : tr7.Contains (fullMoment true true 40 9) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 9 40 mixed_40_9) <;> norm_num [tr7,precision]
noncomputable def t7 : RBox := {lo := 5584022768478394547002286, hi := 7240272629516472088205525}
lemma t7_checked : ((hm40_0_0_9.realAnswer).add tr7).scale (1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 40 (-1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_0_0_9.realContains tr7_contains) (1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -43645893453395484376071552, hi := 43645893453395484376071552}
lemma tr8_contains : tr8.Contains (fullMoment true true 40 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 10 40 mixed_40_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := -2774099680888621673549565, hi := -2433116138283450864454555}
lemma t8_checked : ((hm40_0_0_10.realAnswer).add tr8).scale (-1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 40 (-1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_0_0_10.realContains tr8_contains) (-1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -16351797364128125134540904, hi := 16351797364128125134540904}
lemma tr9_contains : tr9.Contains (fullMoment true true 40 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 11 40 mixed_40_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -136363489713542850459441, hi := -72489281259860685979043}
lemma t9_checked : ((hm40_0_0_11.realAnswer).add tr9).scale (1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 40 (-1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_0_0_11.realContains tr9_contains) (1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -5619945822412676134103778, hi := 5619945822412676134103778}
lemma tr10_contains : tr10.Contains (fullMoment true true 40 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 12 40 mixed_40_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := 46482870629251231246933, hi := 57459327313656681581606}
lemma t10_checked : ((hm40_0_0_12.realAnswer).add tr10).scale (-1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 40 (-1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_0_0_12.realContains tr10_contains) (-1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -1784145647367326687478989, hi := 1784145647367326687478989}
lemma tr11_contains : tr11.Contains (fullMoment true true 40 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 13 40 mixed_40_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := 330399791728981569743, hi := 2072729525486665659349}
lemma t11_checked : ((hm40_0_0_13.realAnswer).add tr11).scale (1) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 40 (-1/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_0_0_13.realContains tr11_contains) (1) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -87877937065627773063601, hi := 87877937065627773063601}
lemma t12_contains : t12.Contains (sourcePower false 40 (-1/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (-1/2) 2 12 coarse_40_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -8923502275499992317134, hi := 8923502275499992317134}
lemma t13_contains : t13.Contains (sourcePower false 40 (-1/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (-1/2) 2 13 coarse_40_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -853949805618751343127, hi := 853949805618751343127}
lemma t14_contains : t14.Contains (sourcePower false 40 (-1/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (-1/2) 2 14 coarse_40_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -77257841714342004228, hi := 77257841714342004228}
lemma t15_contains : t15.Contains (sourcePower false 40 (-1/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (-1/2) 2 15 coarse_40_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -6626867968629136335, hi := 6626867968629136335}
lemma t16_contains : t16.Contains (sourcePower false 40 (-1/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (-1/2) 2 16 coarse_40_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -540339047637620529, hi := 540339047637620529}
lemma t17_contains : t17.Contains (sourcePower false 40 (-1/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (-1/2) 2 17 coarse_40_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -41982485090566382, hi := 41982485090566382}
lemma t18_contains : t18.Contains (sourcePower false 40 (-1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (-1/2) 2 18 coarse_40_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -3115283610497797, hi := 3115283610497797}
lemma t19_contains : t19.Contains (sourcePower false 40 (-1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (-1/2) 2 19 coarse_40_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -221252030090899, hi := 221252030090899}
lemma t20_contains : t20.Contains (sourcePower false 40 (-1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (-1/2) 2 20 coarse_40_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -15070716811844, hi := 15070716811844}
lemma t21_contains : t21.Contains (sourcePower false 40 (-1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (-1/2) 2 21 coarse_40_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -986538211079, hi := 986538211079}
lemma t22_contains : t22.Contains (sourcePower false 40 (-1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (-1/2) 2 22 coarse_40_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -62186943337, hi := 62186943337}
lemma t23_contains : t23.Contains (sourcePower false 40 (-1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (-1/2) 2 23 coarse_40_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -3782456437, hi := 3782456437}
lemma t24_contains : t24.Contains (sourcePower false 40 (-1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (-1/2) 2 24 coarse_40_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -222459860, hi := 222459860}
lemma t25_contains : t25.Contains (sourcePower false 40 (-1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (-1/2) 2 25 coarse_40_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -12679223, hi := 12679223}
lemma t26_contains : t26.Contains (sourcePower false 40 (-1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (-1/2) 2 26 coarse_40_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -701972, hi := 701972}
lemma t27_contains : t27.Contains (sourcePower false 40 (-1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (-1/2) 2 27 coarse_40_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -37847, hi := 37847}
lemma t28_contains : t28.Contains (sourcePower false 40 (-1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 40 (-1/2) 2 28 coarse_40_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 40 (-1/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 40 (-1/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 55542678676135530126746154943, hi := 55542678676303547981879035176}
lemma t0_checked : ((hm40_1_0_2.realAnswer).add hm40_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 40 (-1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_1_0_2.realContains hm40_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -58764837580474174548525727027, hi := -58764837580409462231682510307}
lemma t1_checked : ((hm40_1_0_3.realAnswer).add hm40_0_1_3.realAnswer).scale (-1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 40 (-1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_1_0_3.realContains hm40_0_1_3.realContains) (-1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr2 : RBox := {lo := -1378005254342885432796058460, hi := 1378005254342885432796058460}
lemma tr2_contains : tr2.Contains (fullMoment false true 40 4) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 4 40 mixed_40_4) <;> norm_num [tr2,precision]
noncomputable def t2 : RBox := {lo := 10136097359637116657189230037, hi := 10825099986827544539965530404}
lemma t2_checked : ((hm40_1_0_4.realAnswer).add tr2).scale (1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 40 (-1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_1_0_4.realContains tr2_contains) (1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr3 : RBox := {lo := -1127662331737765183970897290, hi := 1127662331737765183970897290}
lemma tr3_contains : tr3.Contains (fullMoment false true 40 5) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 5 40 mixed_40_5) <;> norm_num [tr3,precision]
noncomputable def t3 : RBox := {lo := 6033433227725178675241392922, hi := 6315348810664106520885659013}
lemma t3_checked : ((hm40_1_0_5.realAnswer).add tr3).scale (-1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 40 (-1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_1_0_5.realContains tr3_contains) (-1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr4 : RBox := {lo := -770206922867263530745282246, hi := 770206922867263530745282246}
lemma tr4_contains : tr4.Contains (fullMoment false true 40 6) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 6 40 mixed_40_6) <;> norm_num [tr4,precision]
noncomputable def t4 : RBox := {lo := -1715584254096443165867659500, hi := -1619308388737148273653403525}
lemma t4_checked : ((hm40_1_0_6.realAnswer).add tr4).scale (1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 40 (-1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_1_0_6.realContains tr4_contains) (1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr5 : RBox := {lo := -451541240469518315478157760, hi := 451541240469518315478157760}
lemma tr5_contains : tr5.Contains (fullMoment false true 40 7) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 7 40 mixed_40_7) <;> norm_num [tr5,precision]
noncomputable def t5 : RBox := {lo := -286384682349957752812393969, hi := -258163354820462144379164841}
lemma t5_checked : ((hm40_1_0_7.realAnswer).add tr5).scale (-1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 40 (-1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_1_0_7.realContains tr5_contains) (-1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr6 : RBox := {lo := -231919502450331624380412515, hi := 231919502450331624380412515}
lemma tr6_contains : tr6.Contains (fullMoment false true 40 8) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 8 40 mixed_40_8) <;> norm_num [tr6,precision]
noncomputable def t6 : RBox := {lo := 88349140249190500846757200, hi := 95596624700785826915755000}
lemma t6_checked : ((hm40_1_0_8.realAnswer).add tr6).scale (1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 40 (-1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_1_0_8.realContains tr6_contains) (1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr7 : RBox := {lo := -105999991106160182956535889, hi := 105999991106160182956535889}
lemma tr7_contains : tr7.Contains (fullMoment false true 40 9) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 9 40 mixed_40_9) <;> norm_num [tr7,precision]
noncomputable def t7 : RBox := {lo := 5921641182169731041501823, hi := 7577891043206466621972072}
lemma t7_checked : ((hm40_1_0_9.realAnswer).add tr7).scale (-1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 40 (-1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_1_0_9.realContains tr7_contains) (-1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -43645893453395484376071552, hi := 43645893453395484376071552}
lemma tr8_contains : tr8.Contains (fullMoment false true 40 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 10 40 mixed_40_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := -2990551885083084274534201, hi := -2649568342478074802890628}
lemma t8_checked : ((hm40_1_0_10.realAnswer).add tr8).scale (1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 40 (-1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_1_0_10.realContains tr8_contains) (1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -16351797364128125134540904, hi := 16351797364128125134540904}
lemma tr9_contains : tr9.Contains (fullMoment false true 40 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 11 40 mixed_40_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -139479210398009337999242, hi := -75605001944344863961579}
lemma t9_checked : ((hm40_1_0_11.realAnswer).add tr9).scale (-1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 40 (-1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_1_0_11.realContains tr9_contains) (-1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -5619945822412676134103778, hi := 5619945822412676134103778}
lemma tr10_contains : tr10.Contains (fullMoment false true 40 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 12 40 mixed_40_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := 50770990775776838914059, hi := 61747447460180505484450}
lemma t10_checked : ((hm40_1_0_12.realAnswer).add tr10).scale (1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 40 (-1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_1_0_12.realContains tr10_contains) (1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -1784145647367326687478989, hi := 1784145647367326687478989}
lemma tr11_contains : tr11.Contains (fullMoment false true 40 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 13 40 mixed_40_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := 323143043736313737271, hi := 2065472777493831273842}
lemma t11_checked : ((hm40_1_0_13.realAnswer).add tr11).scale (-1) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 40 (-1/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm40_1_0_13.realContains tr11_contains) (-1) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -87877937065627773063601, hi := 87877937065627773063601}
lemma t12_contains : t12.Contains (sourcePower true 40 (-1/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (-1/2) 2 12 coarse_40_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -8923502275499992317134, hi := 8923502275499992317134}
lemma t13_contains : t13.Contains (sourcePower true 40 (-1/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (-1/2) 2 13 coarse_40_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -853949805618751343127, hi := 853949805618751343127}
lemma t14_contains : t14.Contains (sourcePower true 40 (-1/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (-1/2) 2 14 coarse_40_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -77257841714342004228, hi := 77257841714342004228}
lemma t15_contains : t15.Contains (sourcePower true 40 (-1/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (-1/2) 2 15 coarse_40_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -6626867968629136335, hi := 6626867968629136335}
lemma t16_contains : t16.Contains (sourcePower true 40 (-1/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (-1/2) 2 16 coarse_40_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -540339047637620529, hi := 540339047637620529}
lemma t17_contains : t17.Contains (sourcePower true 40 (-1/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (-1/2) 2 17 coarse_40_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -41982485090566382, hi := 41982485090566382}
lemma t18_contains : t18.Contains (sourcePower true 40 (-1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (-1/2) 2 18 coarse_40_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -3115283610497797, hi := 3115283610497797}
lemma t19_contains : t19.Contains (sourcePower true 40 (-1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (-1/2) 2 19 coarse_40_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -221252030090899, hi := 221252030090899}
lemma t20_contains : t20.Contains (sourcePower true 40 (-1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (-1/2) 2 20 coarse_40_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -15070716811844, hi := 15070716811844}
lemma t21_contains : t21.Contains (sourcePower true 40 (-1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (-1/2) 2 21 coarse_40_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -986538211079, hi := 986538211079}
lemma t22_contains : t22.Contains (sourcePower true 40 (-1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (-1/2) 2 22 coarse_40_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -62186943337, hi := 62186943337}
lemma t23_contains : t23.Contains (sourcePower true 40 (-1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (-1/2) 2 23 coarse_40_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -3782456437, hi := 3782456437}
lemma t24_contains : t24.Contains (sourcePower true 40 (-1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (-1/2) 2 24 coarse_40_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -222459860, hi := 222459860}
lemma t25_contains : t25.Contains (sourcePower true 40 (-1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (-1/2) 2 25 coarse_40_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -12679223, hi := 12679223}
lemma t26_contains : t26.Contains (sourcePower true 40 (-1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (-1/2) 2 26 coarse_40_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -701972, hi := 701972}
lemma t27_contains : t27.Contains (sourcePower true 40 (-1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (-1/2) 2 27 coarse_40_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -37847, hi := 37847}
lemma t28_contains : t28.Contains (sourcePower true 40 (-1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 40 (-1/2) 2 28 coarse_40_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 40 (-1/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 40 (-1/2) 2) k.val := by
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
end SharpPlanar.Bernstein40

end OAI
