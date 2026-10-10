import OAI.Analysis.PlanarPacking.Certificate.LowBlock25_0
import OAI.Analysis.PlanarPacking.Certificate.LowBlock25_1
import OAI.Analysis.PlanarPacking.Certificate.LowBlock25_10
import OAI.Analysis.PlanarPacking.Certificate.LowBlock25_11
import OAI.Analysis.PlanarPacking.Certificate.MixedBound25
import OAI.Analysis.PlanarPacking.Certificate.CoarseBound25

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein25
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 29655977112444124283700827689, hi := 29655977112617091880525618752}
lemma t0_checked : ((hm25_0_0_2.realAnswer).add hm25_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 25 (1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_0_0_2.realContains hm25_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 24052765476858387398727985203, hi := 24052765476992015827436991939}
lemma t1_checked : ((hm25_0_0_3.realAnswer).add hm25_1_1_3.realAnswer).scale (-1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 25 (1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_0_0_3.realContains hm25_1_1_3.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -38183550462389263217353379800, hi := -38183550462310742101608049055}
lemma t2_checked : ((hm25_0_0_4.realAnswer).add hm25_1_1_4.realAnswer).scale (-1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 25 (1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_0_0_4.realContains hm25_1_1_4.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -19362943412857082348347183575, hi := -19362943412819945837649640479}
lemma t3_checked : ((hm25_0_0_5.realAnswer).add hm25_1_1_5.realAnswer).scale (-1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 25 (1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_0_0_5.realContains hm25_1_1_5.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 21171041745851008316290120569, hi := 21171041745865693462806059000}
lemma t4_checked : ((hm25_0_0_6.realAnswer).add hm25_1_1_6.realAnswer).scale (-1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 25 (1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_0_0_6.realContains hm25_1_1_6.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 3965327252413217832059442043, hi := 3965327252418207112829606790}
lemma t5_checked : ((hm25_0_0_7.realAnswer).add hm25_1_1_7.realAnswer).scale (-1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 25 (1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_0_0_7.realContains hm25_1_1_7.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -4935150960199374917168861381, hi := -4935150960197888679457895399}
lemma t6_checked : ((hm25_0_0_8.realAnswer).add hm25_1_1_8.realAnswer).scale (-1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 25 (1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_0_0_8.realContains hm25_1_1_8.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -378844461502999264828875486, hi := -378844461502604976050347415}
lemma t7_checked : ((hm25_0_0_9.realAnswer).add hm25_1_1_9.realAnswer).scale (-1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 25 (1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_0_0_9.realContains hm25_1_1_9.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -1142567497394338112201783090, hi := 1142567497394338112201783090}
lemma tr8_contains : tr8.Contains (fullMoment true true 25 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 10 25 mixed_25_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := -503864974496040793348982304, hi := 1781270020292729747064924144}
lemma t8_checked : ((hm25_0_0_10.realAnswer).add tr8).scale (-1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 25 (1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_0_0_10.realContains tr8_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -429035170759864269207836261, hi := 429035170759864269207836261}
lemma tr9_contains : tr9.Contains (fullMoment true true 25 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 11 25 mixed_25_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -398518728801133769593338404, hi := 459551612718615316606923582}
lemma t9_checked : ((hm25_0_0_11.realAnswer).add tr9).scale (-1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 25 (1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_0_0_11.realContains tr9_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -147751113260532258274768477, hi := 147751113260532258274768477}
lemma tr10_contains : tr10.Contains (fullMoment true true 25 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 12 25 mixed_25_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -200767112318810163341042426, hi := 94735114202258464323806212}
lemma t10_checked : ((hm25_0_0_12.realAnswer).add tr10).scale (-1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 25 (1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_0_0_12.realContains tr10_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -1709635599354057588977945053, hi := 1709635599354057588977945053}
lemma t11_contains : t11.Contains (sourcePower false 25 (1/1) 2 11) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (1/1) 2 11 coarse_25_13) <;> norm_num [t11,precision]
noncomputable def t12 : RBox := {lo := -373303454578363789549965966, hi := 373303454578363789549965966}
lemma t12_contains : t12.Contains (sourcePower false 25 (1/1) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (1/1) 2 12 coarse_25_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -76785249843842576607819054, hi := 76785249843842576607819054}
lemma t13_contains : t13.Contains (sourcePower false 25 (1/1) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (1/1) 2 13 coarse_25_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -14944038864773772626460091, hi := 14944038864773772626460091}
lemma t14_contains : t14.Contains (sourcePower false 25 (1/1) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (1/1) 2 14 coarse_25_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -2763638568673854239576766, hi := 2763638568673854239576766}
lemma t15_contains : t15.Contains (sourcePower false 25 (1/1) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (1/1) 2 15 coarse_25_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -487679883890270618281306, hi := 487679883890270618281306}
lemma t16_contains : t16.Contains (sourcePower false 25 (1/1) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (1/1) 2 16 coarse_25_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -82459113489707738598146, hi := 82459113489707738598146}
lemma t17_contains : t17.Contains (sourcePower false 25 (1/1) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (1/1) 2 17 coarse_25_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -13415358447817719868817, hi := 13415358447817719868817}
lemma t18_contains : t18.Contains (sourcePower false 25 (1/1) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (1/1) 2 18 coarse_25_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -2108727150330305406116, hi := 2108727150330305406116}
lemma t19_contains : t19.Contains (sourcePower false 25 (1/1) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (1/1) 2 19 coarse_25_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -321538539951788029867, hi := 321538539951788029867}
lemma t20_contains : t20.Contains (sourcePower false 25 (1/1) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (1/1) 2 20 coarse_25_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -47737694023601780598, hi := 47737694023601780598}
lemma t21_contains : t21.Contains (sourcePower false 25 (1/1) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (1/1) 2 21 coarse_25_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -6923525363928755660, hi := 6923525363928755660}
lemma t22_contains : t22.Contains (sourcePower false 25 (1/1) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (1/1) 2 22 coarse_25_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -983493777958713191, hi := 983493777958713191}
lemma t23_contains : t23.Contains (sourcePower false 25 (1/1) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (1/1) 2 23 coarse_25_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -137086330848278101, hi := 137086330848278101}
lemma t24_contains : t24.Contains (sourcePower false 25 (1/1) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (1/1) 2 24 coarse_25_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -18768592723534679, hi := 18768592723534679}
lemma t25_contains : t25.Contains (sourcePower false 25 (1/1) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (1/1) 2 25 coarse_25_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -2524547656204976, hi := 2524547656204976}
lemma t26_contains : t26.Contains (sourcePower false 25 (1/1) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (1/1) 2 26 coarse_25_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -333485942635723, hi := 333485942635723}
lemma t27_contains : t27.Contains (sourcePower false 25 (1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (1/1) 2 27 coarse_25_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -43227396073138, hi := 43227396073138}
lemma t28_contains : t28.Contains (sourcePower false 25 (1/1) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (1/1) 2 28 coarse_25_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 25 (1/1) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (1/1) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 29638183521361191053993960230, hi := 29638183521502957680243285541}
lemma t0_checked : ((hm25_1_0_2.realAnswer).add hm25_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 25 (1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_1_0_2.realContains hm25_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 24261152379661021849680624064, hi := 24261152379770558305534220332}
lemma t1_checked : ((hm25_1_0_3.realAnswer).add hm25_0_1_3.realAnswer).scale (1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 25 (1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_1_0_3.realContains hm25_0_1_3.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -37990553124485490674124929406, hi := -37990553124421120526813504660}
lemma t2_checked : ((hm25_1_0_4.realAnswer).add hm25_0_1_4.realAnswer).scale (1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 25 (1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_1_0_4.realContains hm25_0_1_4.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -19646468994740787714457424895, hi := -19646468994710341817009928549}
lemma t3_checked : ((hm25_1_0_5.realAnswer).add hm25_0_1_5.realAnswer).scale (1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 25 (1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_1_0_5.realContains hm25_0_1_5.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 21026861620643615506068559885, hi := 21026861620655655587008236366}
lemma t4_checked : ((hm25_1_0_6.realAnswer).add hm25_0_1_6.realAnswer).scale (1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 25 (1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_1_0_6.realContains hm25_0_1_6.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 4128498544941416258465355730, hi := 4128498544945507057100507137}
lemma t5_checked : ((hm25_1_0_7.realAnswer).add hm25_0_1_7.realAnswer).scale (1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 25 (1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_1_0_7.realContains hm25_0_1_7.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -4910245760980149188392355564, hi := -4910245760978930551804536380}
lemma t6_checked : ((hm25_1_0_8.realAnswer).add hm25_0_1_8.realAnswer).scale (1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 25 (1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_1_0_8.realContains hm25_0_1_8.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -416871061591267258873337488, hi := -416871061590943952547896317}
lemma t7_checked : ((hm25_1_0_9.realAnswer).add hm25_0_1_9.realAnswer).scale (1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 25 (1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_1_0_9.realContains hm25_0_1_9.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -1142567497394338112201783090, hi := 1142567497394338112201783090}
lemma tr8_contains : tr8.Contains (fullMoment false true 25 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 10 25 mixed_25_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := -509332298757771549635289121, hi := 1775802696030982007558737419}
lemma t8_checked : ((hm25_1_0_10.realAnswer).add tr8).scale (1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 25 (1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_1_0_10.realContains tr8_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -429035170759864269207836261, hi := 429035170759864269207836261}
lemma tr9_contains : tr9.Contains (fullMoment false true 25 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 11 25 mixed_25_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -393965622491575124144032021, hi := 464104719028170261934683912}
lemma t9_checked : ((hm25_1_0_11.realAnswer).add tr9).scale (1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 25 (1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_1_0_11.realContains tr9_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -147751113260532258274768477, hi := 147751113260532258274768477}
lemma tr10_contains : tr10.Contains (fullMoment false true 25 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 12 25 mixed_25_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -200430389231047175666789199, hi := 95071837290020711647146340}
lemma t10_checked : ((hm25_1_0_12.realAnswer).add tr10).scale (1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 25 (1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_1_0_12.realContains tr10_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -1709635599354057588977945053, hi := 1709635599354057588977945053}
lemma t11_contains : t11.Contains (sourcePower true 25 (1/1) 2 11) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (1/1) 2 11 coarse_25_13) <;> norm_num [t11,precision]
noncomputable def t12 : RBox := {lo := -373303454578363789549965966, hi := 373303454578363789549965966}
lemma t12_contains : t12.Contains (sourcePower true 25 (1/1) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (1/1) 2 12 coarse_25_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -76785249843842576607819054, hi := 76785249843842576607819054}
lemma t13_contains : t13.Contains (sourcePower true 25 (1/1) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (1/1) 2 13 coarse_25_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -14944038864773772626460091, hi := 14944038864773772626460091}
lemma t14_contains : t14.Contains (sourcePower true 25 (1/1) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (1/1) 2 14 coarse_25_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -2763638568673854239576766, hi := 2763638568673854239576766}
lemma t15_contains : t15.Contains (sourcePower true 25 (1/1) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (1/1) 2 15 coarse_25_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -487679883890270618281306, hi := 487679883890270618281306}
lemma t16_contains : t16.Contains (sourcePower true 25 (1/1) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (1/1) 2 16 coarse_25_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -82459113489707738598146, hi := 82459113489707738598146}
lemma t17_contains : t17.Contains (sourcePower true 25 (1/1) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (1/1) 2 17 coarse_25_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -13415358447817719868817, hi := 13415358447817719868817}
lemma t18_contains : t18.Contains (sourcePower true 25 (1/1) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (1/1) 2 18 coarse_25_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -2108727150330305406116, hi := 2108727150330305406116}
lemma t19_contains : t19.Contains (sourcePower true 25 (1/1) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (1/1) 2 19 coarse_25_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -321538539951788029867, hi := 321538539951788029867}
lemma t20_contains : t20.Contains (sourcePower true 25 (1/1) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (1/1) 2 20 coarse_25_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -47737694023601780598, hi := 47737694023601780598}
lemma t21_contains : t21.Contains (sourcePower true 25 (1/1) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (1/1) 2 21 coarse_25_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -6923525363928755660, hi := 6923525363928755660}
lemma t22_contains : t22.Contains (sourcePower true 25 (1/1) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (1/1) 2 22 coarse_25_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -983493777958713191, hi := 983493777958713191}
lemma t23_contains : t23.Contains (sourcePower true 25 (1/1) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (1/1) 2 23 coarse_25_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -137086330848278101, hi := 137086330848278101}
lemma t24_contains : t24.Contains (sourcePower true 25 (1/1) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (1/1) 2 24 coarse_25_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -18768592723534679, hi := 18768592723534679}
lemma t25_contains : t25.Contains (sourcePower true 25 (1/1) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (1/1) 2 25 coarse_25_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -2524547656204976, hi := 2524547656204976}
lemma t26_contains : t26.Contains (sourcePower true 25 (1/1) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (1/1) 2 26 coarse_25_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -333485942635723, hi := 333485942635723}
lemma t27_contains : t27.Contains (sourcePower true 25 (1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (1/1) 2 27 coarse_25_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -43227396073138, hi := 43227396073138}
lemma t28_contains : t28.Contains (sourcePower true 25 (1/1) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (1/1) 2 28 coarse_25_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 25 (1/1) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (1/1) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 29655977112444124283700827689, hi := 29655977112617091880525618752}
lemma t0_checked : ((hm25_0_0_2.realAnswer).add hm25_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 25 (-1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_0_0_2.realContains hm25_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -12026382738496007913718495970, hi := -12026382738429193699363992601}
lemma t1_checked : ((hm25_0_0_3.realAnswer).add hm25_1_1_3.realAnswer).scale (1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 25 (-1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_0_0_3.realContains hm25_1_1_3.realContains) (1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -9545887615597315804338344950, hi := -9545887615577685525402012263}
lemma t2_checked : ((hm25_0_0_4.realAnswer).add hm25_1_1_4.realAnswer).scale (-1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 25 (-1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_0_0_4.realContains hm25_1_1_4.realContains) (-1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 2420367926602493229706205059, hi := 2420367926607135293543397947}
lemma t3_checked : ((hm25_0_0_5.realAnswer).add hm25_1_1_5.realAnswer).scale (1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 25 (-1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_0_0_5.realContains hm25_1_1_5.realContains) (1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 1323190109115688019768132535, hi := 1323190109116605841425378688}
lemma t4_checked : ((hm25_0_0_6.realAnswer).add hm25_1_1_6.realAnswer).scale (-1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 25 (-1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_0_0_6.realContains hm25_1_1_6.realContains) (-1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -123916476638068972275925213, hi := -123916476637913057251857563}
lemma t5_checked : ((hm25_0_0_7.realAnswer).add hm25_1_1_7.realAnswer).scale (1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 25 (-1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_0_0_7.realContains hm25_1_1_7.realContains) (1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -77111733753115233080763460, hi := -77111733753092010616529615}
lemma t6_checked : ((hm25_0_0_8.realAnswer).add hm25_1_1_8.realAnswer).scale (-1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 25 (-1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_0_0_8.realContains hm25_1_1_8.realContains) (-1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 2959722355489101375393339, hi := 2959722355492181756475590}
lemma t7_checked : ((hm25_0_0_9.realAnswer).add hm25_1_1_9.realAnswer).scale (1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 25 (-1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_0_0_9.realContains hm25_1_1_9.realContains) (1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -1142567497394338112201783090, hi := 1142567497394338112201783090}
lemma tr8_contains : tr8.Contains (fullMoment true true 25 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 10 25 mixed_25_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := -1968222556625159349019463, hi := 6958086016768475574472360}
lemma t8_checked : ((hm25_0_0_10.realAnswer).add tr8).scale (-1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 25 (-1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_0_0_10.realContains tr8_contains) (-1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -429035170759864269207836261, hi := 429035170759864269207836261}
lemma tr9_contains : tr9.Contains (fullMoment true true 25 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 11 25 mixed_25_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -897561743591045540247898, hi := 778356892189714393736990}
lemma t9_checked : ((hm25_0_0_11.realAnswer).add tr9).scale (1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 25 (-1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_0_0_11.realContains tr9_contains) (1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -147751113260532258274768477, hi := 147751113260532258274768477}
lemma tr10_contains : tr10.Contains (fullMoment true true 25 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 12 25 mixed_25_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -196061633123838050137737, hi := 92514759963143031566218}
lemma t10_checked : ((hm25_0_0_12.realAnswer).add tr10).scale (-1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 25 (-1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_0_0_12.realContains tr10_contains) (-1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -834783007497098432118138, hi := 834783007497098432118138}
lemma t11_contains : t11.Contains (sourcePower false 25 (-1/2) 2 11) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (-1/2) 2 11 coarse_25_13) <;> norm_num [t11,precision]
noncomputable def t12 : RBox := {lo := -91138538715420847058098, hi := 91138538715420847058098}
lemma t12_contains : t12.Contains (sourcePower false 25 (-1/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (-1/2) 2 12 coarse_25_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -9373199443828439527322, hi := 9373199443828439527322}
lemma t13_contains : t13.Contains (sourcePower false 25 (-1/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (-1/2) 2 13 coarse_25_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -912111747117539833158, hi := 912111747117539833158}
lemma t14_contains : t14.Contains (sourcePower false 25 (-1/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (-1/2) 2 14 coarse_25_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -84339555928767524402, hi := 84339555928767524402}
lemma t15_contains : t15.Contains (sourcePower false 25 (-1/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (-1/2) 2 15 coarse_25_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -7441404478306131261, hi := 7441404478306131261}
lemma t16_contains : t16.Contains (sourcePower false 25 (-1/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (-1/2) 2 16 coarse_25_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -629113109510099325, hi := 629113109510099325}
lemma t17_contains : t17.Contains (sourcePower false 25 (-1/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (-1/2) 2 17 coarse_25_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -51175531188269501, hi := 51175531188269501}
lemma t18_contains : t18.Contains (sourcePower false 25 (-1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (-1/2) 2 18 coarse_25_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -4022077847157108, hi := 4022077847157108}
lemma t19_contains : t19.Contains (sourcePower false 25 (-1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (-1/2) 2 19 coarse_25_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -306643047286786, hi := 306643047286786}
lemma t20_contains : t20.Contains (sourcePower false 25 (-1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (-1/2) 2 20 coarse_25_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -22763106357385, hi := 22763106357385}
lemma t21_contains : t21.Contains (sourcePower false 25 (-1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (-1/2) 2 21 coarse_25_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -1650697079642, hi := 1650697079642}
lemma t22_contains : t22.Contains (sourcePower false 25 (-1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (-1/2) 2 22 coarse_25_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -117241594549, hi := 117241594549}
lemma t23_contains : t23.Contains (sourcePower false 25 (-1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (-1/2) 2 23 coarse_25_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -8170982054, hi := 8170982054}
lemma t24_contains : t24.Contains (sourcePower false 25 (-1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (-1/2) 2 24 coarse_25_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -559347652, hi := 559347652}
lemma t25_contains : t25.Contains (sourcePower false 25 (-1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (-1/2) 2 25 coarse_25_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -37618692, hi := 37618692}
lemma t26_contains : t26.Contains (sourcePower false 25 (-1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (-1/2) 2 26 coarse_25_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -2484664, hi := 2484664}
lemma t27_contains : t27.Contains (sourcePower false 25 (-1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (-1/2) 2 27 coarse_25_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -161035, hi := 161035}
lemma t28_contains : t28.Contains (sourcePower false 25 (-1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 25 (-1/2) 2 28 coarse_25_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 25 (-1/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 25 (-1/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 29638183521361191053993960230, hi := 29638183521502957680243285541}
lemma t0_checked : ((hm25_1_0_2.realAnswer).add hm25_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 25 (-1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_1_0_2.realContains hm25_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -12130576189885279152767110166, hi := -12130576189830510924840312032}
lemma t1_checked : ((hm25_1_0_3.realAnswer).add hm25_0_1_3.realAnswer).scale (-1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 25 (-1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_1_0_3.realContains hm25_0_1_3.realContains) (-1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -9497638281121372668531232352, hi := -9497638281105280131703376165}
lemma t2_checked : ((hm25_1_0_4.realAnswer).add hm25_0_1_4.realAnswer).scale (1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 25 (-1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_1_0_4.realContains hm25_0_1_4.realContains) (1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 2455808624338792727126241068, hi := 2455808624342598464307178112}
lemma t3_checked : ((hm25_1_0_5.realAnswer).add hm25_0_1_5.realAnswer).scale (-1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 25 (-1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_1_0_5.realContains hm25_0_1_5.realContains) (-1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 1314178851290225969129284992, hi := 1314178851290978474188014773}
lemma t4_checked : ((hm25_1_0_6.realAnswer).add hm25_0_1_6.realAnswer).scale (1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 25 (-1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_1_0_6.realContains hm25_0_1_6.realContains) (1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -129015579529547095534390849, hi := -129015579529419258077042366}
lemma t5_checked : ((hm25_1_0_7.realAnswer).add hm25_0_1_7.realAnswer).scale (-1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 25 (-1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_1_0_7.realContains hm25_0_1_7.realContains) (-1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -76722590015314831068630556, hi := -76722590015295789871945880}
lemma t6_checked : ((hm25_1_0_8.realAnswer).add hm25_0_1_8.realAnswer).scale (1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 25 (-1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_1_0_8.realContains hm25_0_1_8.realContains) (1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 3256805168679249629280439, hi := 3256805168681775459947950}
lemma t7_checked : ((hm25_1_0_9.realAnswer).add hm25_0_1_9.realAnswer).scale (-1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 25 (-1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_1_0_9.realContains hm25_0_1_9.realContains) (-1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -1142567497394338112201783090, hi := 1142567497394338112201783090}
lemma tr8_contains : tr8.Contains (fullMoment false true 25 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 10 25 mixed_25_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := -1989579292022545115762849, hi := 6936729281371023467026319}
lemma t8_checked : ((hm25_1_0_10.realAnswer).add tr8).scale (1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 25 (-1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_1_0_10.realContains tr8_contains) (1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -429035170759864269207836261, hi := 429035170759864269207836261}
lemma tr9_contains : tr9.Contains (fullMoment false true 25 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 11 25 mixed_25_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -906454529351895042841180, hi := 769464106428857664343813}
lemma t9_checked : ((hm25_1_0_11.realAnswer).add tr9).scale (-1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 25 (-1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_1_0_11.realContains tr9_contains) (-1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -147751113260532258274768477, hi := 147751113260532258274768477}
lemma tr10_contains : tr10.Contains (fullMoment false true 25 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 12 25 mixed_25_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -195732801983444507487099, hi := 92843591103535851217917}
lemma t10_checked : ((hm25_1_0_12.realAnswer).add tr10).scale (1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 25 (-1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm25_1_0_12.realContains tr10_contains) (1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -834783007497098432118138, hi := 834783007497098432118138}
lemma t11_contains : t11.Contains (sourcePower true 25 (-1/2) 2 11) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (-1/2) 2 11 coarse_25_13) <;> norm_num [t11,precision]
noncomputable def t12 : RBox := {lo := -91138538715420847058098, hi := 91138538715420847058098}
lemma t12_contains : t12.Contains (sourcePower true 25 (-1/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (-1/2) 2 12 coarse_25_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -9373199443828439527322, hi := 9373199443828439527322}
lemma t13_contains : t13.Contains (sourcePower true 25 (-1/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (-1/2) 2 13 coarse_25_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -912111747117539833158, hi := 912111747117539833158}
lemma t14_contains : t14.Contains (sourcePower true 25 (-1/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (-1/2) 2 14 coarse_25_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -84339555928767524402, hi := 84339555928767524402}
lemma t15_contains : t15.Contains (sourcePower true 25 (-1/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (-1/2) 2 15 coarse_25_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -7441404478306131261, hi := 7441404478306131261}
lemma t16_contains : t16.Contains (sourcePower true 25 (-1/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (-1/2) 2 16 coarse_25_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -629113109510099325, hi := 629113109510099325}
lemma t17_contains : t17.Contains (sourcePower true 25 (-1/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (-1/2) 2 17 coarse_25_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -51175531188269501, hi := 51175531188269501}
lemma t18_contains : t18.Contains (sourcePower true 25 (-1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (-1/2) 2 18 coarse_25_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -4022077847157108, hi := 4022077847157108}
lemma t19_contains : t19.Contains (sourcePower true 25 (-1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (-1/2) 2 19 coarse_25_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -306643047286786, hi := 306643047286786}
lemma t20_contains : t20.Contains (sourcePower true 25 (-1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (-1/2) 2 20 coarse_25_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -22763106357385, hi := 22763106357385}
lemma t21_contains : t21.Contains (sourcePower true 25 (-1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (-1/2) 2 21 coarse_25_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -1650697079642, hi := 1650697079642}
lemma t22_contains : t22.Contains (sourcePower true 25 (-1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (-1/2) 2 22 coarse_25_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -117241594549, hi := 117241594549}
lemma t23_contains : t23.Contains (sourcePower true 25 (-1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (-1/2) 2 23 coarse_25_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -8170982054, hi := 8170982054}
lemma t24_contains : t24.Contains (sourcePower true 25 (-1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (-1/2) 2 24 coarse_25_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -559347652, hi := 559347652}
lemma t25_contains : t25.Contains (sourcePower true 25 (-1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (-1/2) 2 25 coarse_25_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -37618692, hi := 37618692}
lemma t26_contains : t26.Contains (sourcePower true 25 (-1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (-1/2) 2 26 coarse_25_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -2484664, hi := 2484664}
lemma t27_contains : t27.Contains (sourcePower true 25 (-1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (-1/2) 2 27 coarse_25_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -161035, hi := 161035}
lemma t28_contains : t28.Contains (sourcePower true 25 (-1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 25 (-1/2) 2 28 coarse_25_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 25 (-1/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 25 (-1/2) 2) k.val := by
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
end SharpPlanar.Bernstein25

end OAI
