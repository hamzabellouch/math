import OAI.Analysis.PlanarPacking.Certificate.LowBlock24_0
import OAI.Analysis.PlanarPacking.Certificate.LowBlock24_1
import OAI.Analysis.PlanarPacking.Certificate.LowBlock24_10
import OAI.Analysis.PlanarPacking.Certificate.LowBlock24_11
import OAI.Analysis.PlanarPacking.Certificate.MixedBound24
import OAI.Analysis.PlanarPacking.Certificate.CoarseBound24

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein24
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 56184223714027815290723755404, hi := 56184223714200634473775091433}
lemma t0_checked : ((hm24_0_0_2.realAnswer).add hm24_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 24 (1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_0_0_2.realContains hm24_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -59868745884035434218966874355, hi := -59868745883968673676876534670}
lemma t1_checked : ((hm24_0_0_3.realAnswer).add hm24_1_1_3.realAnswer).scale (-1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 24 (1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_0_0_3.realContains hm24_1_1_3.realContains) (-1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := 11031000183303260760566174535, hi := 11031000183322875720102892426}
lemma t2_checked : ((hm24_0_0_4.realAnswer).add hm24_1_1_4.realAnswer).scale (-1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 24 (1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_0_0_4.realContains hm24_1_1_4.realContains) (-1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 6187511833106429069719787220, hi := 6187511833111067549927752152}
lemma t3_checked : ((hm24_0_0_5.realAnswer).add hm24_1_1_5.realAnswer).scale (-1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 24 (1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_0_0_5.realContains hm24_1_1_5.realContains) (-1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := -1737659287071442056634042277, hi := -1737659287070524943549657359}
lemma t4_checked : ((hm24_0_0_6.realAnswer).add hm24_1_1_6.realAnswer).scale (-1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 24 (1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_0_0_6.realContains hm24_1_1_6.realContains) (-1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -263473699464644947859604727, hi := -263473699464489154079855935}
lemma t5_checked : ((hm24_0_0_7.realAnswer).add hm24_1_1_7.realAnswer).scale (-1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 24 (1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_0_0_7.realContains hm24_1_1_7.realContains) (-1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := 95616783629652836183313307, hi := 95616783629676040341774047}
lemma t6_checked : ((hm24_0_0_8.realAnswer).add hm24_1_1_8.realAnswer).scale (-1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 24 (1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_0_0_8.realContains hm24_1_1_8.realContains) (-1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 6071265818763913287893261, hi := 6071265818766991194890756}
lemma t7_checked : ((hm24_0_0_9.realAnswer).add hm24_1_1_9.realAnswer).scale (-1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 24 (1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_0_0_9.realContains hm24_1_1_9.realContains) (-1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := -2926726183987974246652059, hi := -2926726183987606123156233}
lemma t8_checked : ((hm24_0_0_10.realAnswer).add hm24_1_1_10.realAnswer).scale (-1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 24 (1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_0_0_10.realContains hm24_1_1_10.realContains) (-1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := -82271876530885740039855, hi := -82271876530845640563759}
lemma t9_checked : ((hm24_0_0_11.realAnswer).add hm24_1_1_11.realAnswer).scale (-1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 24 (1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_0_0_11.realContains hm24_1_1_11.realContains) (-1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -185486386187469648751994235, hi := 185486386187469648751994235}
lemma tr10_contains : tr10.Contains (fullMoment true true 24 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 12 24 mixed_24_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -124086872703215010463964, hi := 238191225319190658504733}
lemma t10_checked : ((hm24_0_0_12.realAnswer).add tr10).scale (-1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 24 (1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_0_0_12.realContains tr10_contains) (-1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -58997102609725292366925614, hi := 58997102609725292366925614}
lemma tr11_contains : tr11.Contains (fullMoment true true 24 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 13 24 mixed_24_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := -27650510125182466740477, hi := 29963847892127760219069}
lemma t11_checked : ((hm24_0_0_13.realAnswer).add tr11).scale (-1) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 24 (1/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_0_0_13.realContains tr11_contains) (-1) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -92005094558355516319346, hi := 92005094558355516319346}
lemma t12_contains : t12.Contains (sourcePower false 24 (1/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (1/2) 2 12 coarse_24_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -9492764401100362812387, hi := 9492764401100362812387}
lemma t13_contains : t13.Contains (sourcePower false 24 (1/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (1/2) 2 13 coarse_24_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -927581682407947607361, hi := 927581682407947607361}
lemma t14_contains : t14.Contains (sourcePower false 24 (1/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (1/2) 2 14 coarse_24_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -86223802489917842930, hi := 86223802489917842930}
lemma t15_contains : t15.Contains (sourcePower false 24 (1/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (1/2) 2 15 coarse_24_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -7658197989607200361, hi := 7658197989607200361}
lemma t16_contains : t16.Contains (sourcePower false 24 (1/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (1/2) 2 16 coarse_24_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -652747664927167744, hi := 652747664927167744}
lemma t17_contains : t17.Contains (sourcePower false 24 (1/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (1/2) 2 17 coarse_24_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -53623681422163501, hi := 53623681422163501}
lemma t18_contains : t18.Contains (sourcePower false 24 (1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (1/2) 2 18 coarse_24_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -4263623176223224, hi := 4263623176223224}
lemma t19_contains : t19.Contains (sourcePower false 24 (1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (1/2) 2 19 coarse_24_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -329394523921959, hi := 329394523921959}
lemma t20_contains : t20.Contains (sourcePower false 24 (1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (1/2) 2 20 coarse_24_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -24813157369210, hi := 24813157369210}
lemma t21_contains : t21.Contains (sourcePower false 24 (1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (1/2) 2 21 coarse_24_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -1827741453474, hi := 1827741453474}
lemma t22_contains : t22.Contains (sourcePower false 24 (1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (1/2) 2 22 coarse_24_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -131921188015, hi := 131921188015}
lemma t23_contains : t23.Contains (sourcePower false 24 (1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (1/2) 2 23 coarse_24_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -9341435340, hi := 9341435340}
lemma t24_contains : t24.Contains (sourcePower false 24 (1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (1/2) 2 24 coarse_24_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -649223786, hi := 649223786}
lemma t25_contains : t25.Contains (sourcePower false 24 (1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (1/2) 2 25 coarse_24_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -44274198, hi := 44274198}
lemma t26_contains : t26.Contains (sourcePower false 24 (1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (1/2) 2 26 coarse_24_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -2960569, hi := 2960569}
lemma t27_contains : t27.Contains (sourcePower false 24 (1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (1/2) 2 27 coarse_24_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -193934, hi := 193934}
lemma t28_contains : t28.Contains (sourcePower false 24 (1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (1/2) 2 28 coarse_24_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 24 (1/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (1/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 55707558187076143185639554670, hi := 55707558187217860403941610293}
lemma t0_checked : ((hm24_1_0_2.realAnswer).add hm24_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 24 (1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_1_0_2.realContains hm24_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -59128602531392021613379739619, hi := -59128602531337272160459467172}
lemma t1_checked : ((hm24_1_0_3.realAnswer).add hm24_0_1_3.realAnswer).scale (1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 24 (1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_1_0_3.realContains hm24_0_1_3.realContains) (1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := 10684431994838973414905762527, hi := 10684431994855060487034403663}
lemma t2_checked : ((hm24_1_0_4.realAnswer).add hm24_0_1_4.realAnswer).scale (1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 24 (1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_1_0_4.realContains hm24_0_1_4.realContains) (1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 6186589610185928988767128154, hi := 6186589610189733436996142539}
lemma t3_checked : ((hm24_1_0_5.realAnswer).add hm24_0_1_5.realAnswer).scale (1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 24 (1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_1_0_5.realContains hm24_0_1_5.realContains) (1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := -1698518011926227031510010436, hi := -1698518011925474782452765191}
lemma t4_checked : ((hm24_1_0_6.realAnswer).add hm24_0_1_6.realAnswer).scale (1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 24 (1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_1_0_6.realContains hm24_0_1_6.realContains) (1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -269012808335484253185851566, hi := -269012808335356459724083924}
lemma t5_checked : ((hm24_1_0_7.realAnswer).add hm24_0_1_7.realAnswer).scale (1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 24 (1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_1_0_7.realContains hm24_0_1_7.realContains) (1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := 93896449598905752814327072, hi := 93896449598924787333920047}
lemma t6_checked : ((hm24_1_0_8.realAnswer).add hm24_0_1_8.realAnswer).scale (1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 24 (1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_1_0_8.realContains hm24_0_1_8.realContains) (1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 6438326101583658030761871, hi := 6438326101586182952570596}
lemma t7_checked : ((hm24_1_0_9.realAnswer).add hm24_0_1_9.realAnswer).scale (1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 24 (1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_1_0_9.realContains hm24_0_1_9.realContains) (1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := -2886556070332220908785551, hi := -2886556070331918911728886}
lemma t8_checked : ((hm24_1_0_10.realAnswer).add hm24_0_1_10.realAnswer).scale (1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 24 (1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_1_0_10.realContains hm24_0_1_10.realContains) (1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := -94132080047305870085061, hi := -94132080047272972228660}
lemma t9_checked : ((hm24_1_0_11.realAnswer).add hm24_0_1_11.realAnswer).scale (1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 24 (1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_1_0_11.realContains hm24_0_1_11.realContains) (1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -185486386187469648751994235, hi := 185486386187469648751994235}
lemma tr10_contains : tr10.Contains (fullMoment false true 24 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 12 24 mixed_24_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -125023940880328252207948, hi := 237254157142076695970327}
lemma t10_checked : ((hm24_1_0_12.realAnswer).add tr10).scale (1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 24 (1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_1_0_12.realContains tr10_contains) (1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -58997102609725292366925614, hi := 58997102609725292366925614}
lemma tr11_contains : tr11.Contains (fullMoment false true 24 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 13 24 mixed_24_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := -27442525004042190656057, hi := 30171833013267969621905}
lemma t11_checked : ((hm24_1_0_13.realAnswer).add tr11).scale (1) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 24 (1/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_1_0_13.realContains tr11_contains) (1) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -92005094558355516319346, hi := 92005094558355516319346}
lemma t12_contains : t12.Contains (sourcePower true 24 (1/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (1/2) 2 12 coarse_24_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -9492764401100362812387, hi := 9492764401100362812387}
lemma t13_contains : t13.Contains (sourcePower true 24 (1/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (1/2) 2 13 coarse_24_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -927581682407947607361, hi := 927581682407947607361}
lemma t14_contains : t14.Contains (sourcePower true 24 (1/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (1/2) 2 14 coarse_24_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -86223802489917842930, hi := 86223802489917842930}
lemma t15_contains : t15.Contains (sourcePower true 24 (1/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (1/2) 2 15 coarse_24_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -7658197989607200361, hi := 7658197989607200361}
lemma t16_contains : t16.Contains (sourcePower true 24 (1/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (1/2) 2 16 coarse_24_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -652747664927167744, hi := 652747664927167744}
lemma t17_contains : t17.Contains (sourcePower true 24 (1/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (1/2) 2 17 coarse_24_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -53623681422163501, hi := 53623681422163501}
lemma t18_contains : t18.Contains (sourcePower true 24 (1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (1/2) 2 18 coarse_24_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -4263623176223224, hi := 4263623176223224}
lemma t19_contains : t19.Contains (sourcePower true 24 (1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (1/2) 2 19 coarse_24_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -329394523921959, hi := 329394523921959}
lemma t20_contains : t20.Contains (sourcePower true 24 (1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (1/2) 2 20 coarse_24_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -24813157369210, hi := 24813157369210}
lemma t21_contains : t21.Contains (sourcePower true 24 (1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (1/2) 2 21 coarse_24_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -1827741453474, hi := 1827741453474}
lemma t22_contains : t22.Contains (sourcePower true 24 (1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (1/2) 2 22 coarse_24_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -131921188015, hi := 131921188015}
lemma t23_contains : t23.Contains (sourcePower true 24 (1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (1/2) 2 23 coarse_24_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -9341435340, hi := 9341435340}
lemma t24_contains : t24.Contains (sourcePower true 24 (1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (1/2) 2 24 coarse_24_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -649223786, hi := 649223786}
lemma t25_contains : t25.Contains (sourcePower true 24 (1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (1/2) 2 25 coarse_24_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -44274198, hi := 44274198}
lemma t26_contains : t26.Contains (sourcePower true 24 (1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (1/2) 2 26 coarse_24_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -2960569, hi := 2960569}
lemma t27_contains : t27.Contains (sourcePower true 24 (1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (1/2) 2 27 coarse_24_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -193934, hi := 193934}
lemma t28_contains : t28.Contains (sourcePower true 24 (1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (1/2) 2 28 coarse_24_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 24 (1/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 56184223714027815290723755404, hi := 56184223714200634473775091433}
lemma t0_checked : ((hm24_0_0_2.realAnswer).add hm24_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 24 (-3/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_0_0_2.realContains hm24_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 179606237651906021030629604011, hi := 179606237652106302656900623064}
lemma t1_checked : ((hm24_0_0_3.realAnswer).add hm24_1_1_3.realAnswer).scale (3) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 24 (-3/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_0_0_3.realContains hm24_1_1_3.realContains) (3) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := 99279001649729346845095570819, hi := 99279001649905881480926031828}
lemma t2_checked : ((hm24_0_0_4.realAnswer).add hm24_1_1_4.realAnswer).scale (-9) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 24 (-3/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_0_0_4.realContains hm24_1_1_4.realContains) (-9) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -167062819493998823848049308088, hi := -167062819493873584882434254960}
lemma t3_checked : ((hm24_0_0_5.realAnswer).add hm24_1_1_5.realAnswer).scale (27) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 24 (-3/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_0_0_5.realContains hm24_1_1_5.realContains) (27) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := -140750402252786806587357424407, hi := -140750402252712520427522246094}
lemma t4_checked : ((hm24_0_0_6.realAnswer).add hm24_1_1_6.realAnswer).scale (-81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 24 (-3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_0_0_6.realContains hm24_1_1_6.realContains) (-81) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 64024108969870864441404992205, hi := 64024108969908722329883948661}
lemma t5_checked : ((hm24_0_0_7.realAnswer).add hm24_1_1_7.realAnswer).scale (243) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 24 (-3/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_0_0_7.realContains hm24_1_1_7.realContains) (243) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := 69704635266016917577635401372, hi := 69704635266033833409153279705}
lemma t6_checked : ((hm24_0_0_8.realAnswer).add hm24_1_1_8.realAnswer).scale (-729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 24 (-3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_0_0_8.realContains hm24_1_1_8.realContains) (-729) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -13277858345643409743226081254, hi := -13277858345636678360622563327}
lemma t7_checked : ((hm24_0_0_9.realAnswer).add hm24_1_1_9.realAnswer).scale (2187) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 24 (-3/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_0_0_9.realContains hm24_1_1_9.realContains) (2187) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := -19202250493145099032284153205, hi := -19202250493142683774028046122}
lemma t8_checked : ((hm24_0_0_10.realAnswer).add hm24_1_1_10.realAnswer).scale (-6561) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 24 (-3/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_0_0_10.realContains hm24_1_1_10.realContains) (-6561) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := 1619357345756634743216474355, hi := 1619357345757424021204447705}
lemma t9_checked : ((hm24_0_0_11.realAnswer).add hm24_1_1_11.realAnswer).scale (19683) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 24 (-3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_0_0_11.realContains hm24_1_1_11.realContains) (19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -185486386187469648751994235, hi := 185486386187469648751994235}
lemma tr10_contains : tr10.Contains (fullMoment true true 24 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 12 24 mixed_24_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -7327205746252143152886601356, hi := 14064953663872889194045939648}
lemma t10_checked : ((hm24_0_0_12.realAnswer).add tr10).scale (-59049) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 24 (-3/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_0_0_12.realContains tr10_contains) (-59049) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -58997102609725292366925614, hi := 58997102609725292366925614}
lemma tr11_contains : tr11.Contains (fullMoment true true 24 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 13 24 mixed_24_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := -5308005762546756339527350146, hi := 4898204917145698435675215457}
lemma t11_checked : ((hm24_0_0_13.realAnswer).add tr11).scale (177147) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 24 (-3/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_0_0_13.realContains tr11_contains) (177147) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -48895279457187013948269047943, hi := 48895279457187013948269047943}
lemma t12_contains : t12.Contains (sourcePower false 24 (-3/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (-3/2) 2 12 coarse_24_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -15134532618255533740132000351, hi := 15134532618255533740132000351}
lemma t13_contains : t13.Contains (sourcePower false 24 (-3/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (-3/2) 2 13 coarse_24_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -4436594431925058759630009084, hi := 4436594431925058759630009084}
lemma t14_contains : t14.Contains (sourcePower false 24 (-3/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (-3/2) 2 14 coarse_24_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -1237217323114199565829174978, hi := 1237217323114199565829174978}
lemma t15_contains : t15.Contains (sourcePower false 24 (-3/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (-3/2) 2 15 coarse_24_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -329660312221382053495992951, hi := 329660312221382053495992951}
lemma t16_contains : t16.Contains (sourcePower false 24 (-3/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (-3/2) 2 16 coarse_24_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -84295939846563825576348090, hi := 84295939846563825576348090}
lemma t17_contains : t17.Contains (sourcePower false 24 (-3/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (-3/2) 2 17 coarse_24_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -20774912878554798685150661, hi := 20774912878554798685150661}
lemma t18_contains : t18.Contains (sourcePower false 24 (-3/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (-3/2) 2 18 coarse_24_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -4955444927532403499927245, hi := 4955444927532403499927245}
lemma t19_contains : t19.Contains (sourcePower false 24 (-3/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (-3/2) 2 19 coarse_24_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -1148527687785906431688423, hi := 1148527687785906431688423}
lemma t20_contains : t20.Contains (sourcePower false 24 (-3/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (-3/2) 2 20 coarse_24_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -259554390163556698989919, hi := 259554390163556698989919}
lemma t21_contains : t21.Contains (sourcePower false 24 (-3/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (-3/2) 2 21 coarse_24_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -57356463501299681808300, hi := 57356463501299681808300}
lemma t22_contains : t22.Contains (sourcePower false 24 (-3/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (-3/2) 2 22 coarse_24_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -12419479994321041648233, hi := 12419479994321041648233}
lemma t23_contains : t23.Contains (sourcePower false 24 (-3/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (-3/2) 2 23 coarse_24_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -2638297253070937662254, hi := 2638297253070937662254}
lemma t24_contains : t24.Contains (sourcePower false 24 (-3/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (-3/2) 2 24 coarse_24_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -550079918257030980703, hi := 550079918257030980703}
lemma t25_contains : t25.Contains (sourcePower false 24 (-3/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (-3/2) 2 25 coarse_24_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -112539070762571183662, hi := 112539070762571183662}
lemma t26_contains : t26.Contains (sourcePower false 24 (-3/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (-3/2) 2 26 coarse_24_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -22576099940430149943, hi := 22576099940430149943}
lemma t27_contains : t27.Contains (sourcePower false 24 (-3/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (-3/2) 2 27 coarse_24_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -4436570569074936528, hi := 4436570569074936528}
lemma t28_contains : t28.Contains (sourcePower false 24 (-3/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 24 (-3/2) 2 28 coarse_24_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 24 (-3/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 24 (-3/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 55707558187076143185639554670, hi := 55707558187217860403941610293}
lemma t0_checked : ((hm24_1_0_2.realAnswer).add hm24_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 24 (-3/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_1_0_2.realContains hm24_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 177385807594011816481378401517, hi := 177385807594176064840139218856}
lemma t1_checked : ((hm24_1_0_3.realAnswer).add hm24_0_1_3.realAnswer).scale (-3) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 24 (-3/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_1_0_3.realContains hm24_0_1_3.realContains) (-3) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := 96159887953550760734151862745, hi := 96159887953695544383309632961}
lemma t2_checked : ((hm24_1_0_4.realAnswer).add hm24_0_1_4.realAnswer).scale (9) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 24 (-3/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_1_0_4.realContains hm24_0_1_4.realContains) (9) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -167037919475122802798895848547, hi := -167037919475020082696712460174}
lemma t3_checked : ((hm24_1_0_5.realAnswer).add hm24_0_1_5.realAnswer).scale (-27) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 24 (-3/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_1_0_5.realContains hm24_0_1_5.realContains) (-27) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := -137579958966024389552310845286, hi := -137579958965963457378673980546}
lemma t4_checked : ((hm24_1_0_6.realAnswer).add hm24_0_1_6.realAnswer).scale (81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 24 (-3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_1_0_6.realContains hm24_0_1_6.realContains) (81) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 65370112425491619712952393547, hi := 65370112425522673524161930341}
lemma t5_checked : ((hm24_1_0_7.realAnswer).add hm24_0_1_7.realAnswer).scale (-243) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 24 (-3/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_1_0_7.realContains hm24_0_1_7.realContains) (-243) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := 68450511757602293801644435875, hi := 68450511757616169966427713728}
lemma t6_checked : ((hm24_1_0_8.realAnswer).add hm24_0_1_8.realAnswer).scale (729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 24 (-3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_1_0_8.realContains hm24_0_1_8.realContains) (729) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -14080619184168982117271891641, hi := -14080619184163460113276212645}
lemma t7_checked : ((hm24_1_0_9.realAnswer).add hm24_0_1_9.realAnswer).scale (-2187) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 24 (-3/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_1_0_9.realContains hm24_0_1_9.realContains) (-2187) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := -18938694377449701382541995037, hi := -18938694377447719979853222199}
lemma t8_checked : ((hm24_1_0_10.realAnswer).add hm24_0_1_10.realAnswer).scale (6561) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 24 (-3/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_1_0_10.realContains hm24_0_1_10.realContains) (6561) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := 1852801731570473912376719931, hi := 1852801731571121440884244015}
lemma t9_checked : ((hm24_1_0_11.realAnswer).add hm24_0_1_11.realAnswer).scale (-19683) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 24 (-3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_1_0_11.realContains hm24_0_1_11.realContains) (-19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -185486386187469648751994235, hi := 185486386187469648751994235}
lemma tr10_contains : tr10.Contains (fullMoment false true 24 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 12 24 mixed_24_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -7382538685042502964627119780, hi := 14009620725082486820351820167}
lemma t10_checked : ((hm24_1_0_12.realAnswer).add tr10).scale (59049) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 24 (-3/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_1_0_12.realContains tr10_contains) (59049) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -58997102609725292366925614, hi := 58997102609725292366925614}
lemma tr11_contains : tr11.Contains (fullMoment false true 24 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 13 24 mixed_24_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := -5344849702801381014611530388, hi := 4861360976891061948148389426}
lemma t11_checked : ((hm24_1_0_13.realAnswer).add tr11).scale (-177147) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 24 (-3/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm24_1_0_13.realContains tr11_contains) (-177147) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -48895279457187013948269047943, hi := 48895279457187013948269047943}
lemma t12_contains : t12.Contains (sourcePower true 24 (-3/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (-3/2) 2 12 coarse_24_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -15134532618255533740132000351, hi := 15134532618255533740132000351}
lemma t13_contains : t13.Contains (sourcePower true 24 (-3/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (-3/2) 2 13 coarse_24_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -4436594431925058759630009084, hi := 4436594431925058759630009084}
lemma t14_contains : t14.Contains (sourcePower true 24 (-3/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (-3/2) 2 14 coarse_24_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -1237217323114199565829174978, hi := 1237217323114199565829174978}
lemma t15_contains : t15.Contains (sourcePower true 24 (-3/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (-3/2) 2 15 coarse_24_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -329660312221382053495992951, hi := 329660312221382053495992951}
lemma t16_contains : t16.Contains (sourcePower true 24 (-3/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (-3/2) 2 16 coarse_24_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -84295939846563825576348090, hi := 84295939846563825576348090}
lemma t17_contains : t17.Contains (sourcePower true 24 (-3/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (-3/2) 2 17 coarse_24_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -20774912878554798685150661, hi := 20774912878554798685150661}
lemma t18_contains : t18.Contains (sourcePower true 24 (-3/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (-3/2) 2 18 coarse_24_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -4955444927532403499927245, hi := 4955444927532403499927245}
lemma t19_contains : t19.Contains (sourcePower true 24 (-3/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (-3/2) 2 19 coarse_24_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -1148527687785906431688423, hi := 1148527687785906431688423}
lemma t20_contains : t20.Contains (sourcePower true 24 (-3/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (-3/2) 2 20 coarse_24_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -259554390163556698989919, hi := 259554390163556698989919}
lemma t21_contains : t21.Contains (sourcePower true 24 (-3/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (-3/2) 2 21 coarse_24_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -57356463501299681808300, hi := 57356463501299681808300}
lemma t22_contains : t22.Contains (sourcePower true 24 (-3/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (-3/2) 2 22 coarse_24_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -12419479994321041648233, hi := 12419479994321041648233}
lemma t23_contains : t23.Contains (sourcePower true 24 (-3/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (-3/2) 2 23 coarse_24_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -2638297253070937662254, hi := 2638297253070937662254}
lemma t24_contains : t24.Contains (sourcePower true 24 (-3/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (-3/2) 2 24 coarse_24_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -550079918257030980703, hi := 550079918257030980703}
lemma t25_contains : t25.Contains (sourcePower true 24 (-3/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (-3/2) 2 25 coarse_24_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -112539070762571183662, hi := 112539070762571183662}
lemma t26_contains : t26.Contains (sourcePower true 24 (-3/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (-3/2) 2 26 coarse_24_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -22576099940430149943, hi := 22576099940430149943}
lemma t27_contains : t27.Contains (sourcePower true 24 (-3/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (-3/2) 2 27 coarse_24_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -4436570569074936528, hi := 4436570569074936528}
lemma t28_contains : t28.Contains (sourcePower true 24 (-3/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 24 (-3/2) 2 28 coarse_24_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 24 (-3/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (-3/2) 2) k.val := by
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
end SharpPlanar.Bernstein24

end OAI
