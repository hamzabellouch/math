import OAI.Analysis.PlanarPacking.Certificate.LowBlock33_0
import OAI.Analysis.PlanarPacking.Certificate.LowBlock33_1
import OAI.Analysis.PlanarPacking.Certificate.LowBlock33_10
import OAI.Analysis.PlanarPacking.Certificate.MixedBound33
import OAI.Analysis.PlanarPacking.Certificate.CoarseBound33

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein33
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 395227717385759961591205982004, hi := 395227717385939799419758436240}
lemma t0_checked : ((hm33_0_0_2.realAnswer).add hm33_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 33 (3/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_0_0_2.realContains hm33_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 129937201918270946082577168839, hi := 129937201918478844357427499864}
lemma t1_checked : ((hm33_0_0_3.realAnswer).add hm33_1_1_3.realAnswer).scale (-3) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 33 (3/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_0_0_3.realContains hm33_1_1_3.realContains) (-3) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -572554774795451885208224186353, hi := -572554774795268821943915788754}
lemma t2_checked : ((hm33_0_0_4.realAnswer).add hm33_1_1_4.realAnswer).scale (-9) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 33 (3/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_0_0_4.realContains hm33_1_1_4.realContains) (-9) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -122017634357690900372539731556, hi := -122017634357561078953523258493}
lemma t3_checked : ((hm33_0_0_5.realAnswer).add hm33_1_1_5.realAnswer).scale (-27) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 33 (3/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_0_0_5.realContains hm33_1_1_5.realContains) (-27) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 354589043272525642262193430557, hi := 354589043272602641512315520165}
lemma t4_checked : ((hm33_0_0_6.realAnswer).add hm33_1_1_6.realAnswer).scale (-81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 33 (3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_0_0_6.realContains hm33_1_1_6.realContains) (-81) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 44946035146666974401429061265, hi := 44946035146706219937809932805}
lemma t5_checked : ((hm33_0_0_7.realAnswer).add hm33_1_1_7.realAnswer).scale (-243) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 33 (3/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_0_0_7.realContains hm33_1_1_7.realContains) (-243) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr6 : RBox := {lo := -1033339679297547063192977693, hi := 1033339679297547063192977693}
lemma tr6_contains : tr6.Contains (fullMoment true true 33 8) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 8 33 mixed_33_8) <;> norm_num [tr6,precision]
noncomputable def t6 : RBox := {lo := -134671973237440369753504968627, hi := -111131203668425585128689678836}
lemma t6_checked : ((hm33_0_0_8.realAnswer).add tr6).scale (-729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 33 (3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_0_0_8.realContains tr6_contains) (-729) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr7 : RBox := {lo := -472929364761718766176575957, hi := 472929364761718766176575957}
lemma tr7_contains : tr7.Contains (fullMoment true true 33 9) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 9 33 mixed_33_9) <;> norm_num [tr7,precision]
noncomputable def t7 : RBox := {lo := -17063905251812994917836487104, hi := -903022115339153669948582961}
lemma t7_checked : ((hm33_0_0_9.realAnswer).add tr7).scale (-2187) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 33 (3/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_0_0_9.realContains tr7_contains) (-2187) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -194962356813489477136288679, hi := 194962356813489477136288679}
lemma tr8_contains : tr8.Contains (fullMoment true true 33 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 10 33 mixed_33_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := 22469995638882034345608793806, hi := 32463339568988482202955725742}
lemma t8_checked : ((hm33_0_0_10.realAnswer).add tr8).scale (-6561) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 33 (3/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_0_0_10.realContains tr8_contains) (-6561) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -73118819746921046531747332, hi := 73118819746921046531747332}
lemma tr9_contains : tr9.Contains (fullMoment true true 33 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 11 33 mixed_33_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -1640634051058389708043328694, hi := 3981232078155894678345955158}
lemma t9_checked : ((hm33_0_0_11.realAnswer).add tr9).scale (-19683) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 33 (3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_0_0_11.realContains tr9_contains) (-19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -25153474459011621003745446, hi := 25153474459011621003745446}
lemma tr10_contains : tr10.Contains (fullMoment true true 33 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 12 33 mixed_33_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -5746812960521941347213489100, hi := -2845860786048692798555899705}
lemma t10_checked : ((hm33_0_0_12.realAnswer).add tr10).scale (-59049) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 33 (3/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_0_0_12.realContains tr10_contains) (-59049) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -7991902354459712621332914, hi := 7991902354459712621332914}
lemma tr11_contains : tr11.Contains (fullMoment true true 33 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 13 33 mixed_33_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := -795651522963982569108555018, hi := 586908561396900974677950332}
lemma t11_checked : ((hm33_0_0_13.realAnswer).add tr11).scale (-177147) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 33 (3/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_0_0_13.realContains tr11_contains) (-177147) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -46939733625600342871073523762, hi := 46939733625600342871073523762}
lemma t12_contains : t12.Contains (sourcePower false 33 (3/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (3/2) 2 12 coarse_33_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -14325273944965435803399662012, hi := 14325273944965435803399662012}
lemma t13_contains : t13.Contains (sourcePower false 33 (3/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (3/2) 2 13 coarse_33_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -4122547382498648728361320336, hi := 4122547382498648728361320336}
lemma t14_contains : t14.Contains (sourcePower false 33 (3/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (3/2) 2 14 coarse_33_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -1122487668878055295737428716, hi := 1122487668878055295737428716}
lemma t15_contains : t15.Contains (sourcePower false 33 (3/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (3/2) 2 15 coarse_33_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -290066870738915377148187494, hi := 290066870738915377148187494}
lemma t16_contains : t16.Contains (sourcePower false 33 (3/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (3/2) 2 16 coarse_33_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -71348940079428091398830425, hi := 71348940079428091398830425}
lemma t17_contains : t17.Contains (sourcePower false 33 (3/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (3/2) 2 17 coarse_33_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -16752295692802850447624612, hi := 16752295692802850447624612}
lemma t18_contains : t18.Contains (sourcePower false 33 (3/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (3/2) 2 18 coarse_33_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -3764968040736910512304789, hi := 3764968040736910512304789}
lemma t19_contains : t19.Contains (sourcePower false 33 (3/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (3/2) 2 19 coarse_33_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -812182741993809472235986, hi := 812182741993809472235986}
lemma t20_contains : t20.Contains (sourcePower false 33 (3/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (3/2) 2 20 coarse_33_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -168648330431872783378767, hi := 168648330431872783378767}
lemma t21_contains : t21.Contains (sourcePower false 33 (3/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (3/2) 2 21 coarse_33_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -33808057854417327530838, hi := 33808057854417327530838}
lemma t22_contains : t22.Contains (sourcePower false 33 (3/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (3/2) 2 22 coarse_33_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -6562935926769463852608, hi := 6562935926769463852608}
lemma t23_contains : t23.Contains (sourcePower false 33 (3/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (3/2) 2 23 coarse_33_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -1237663451307691708881, hi := 1237663451307691708881}
lemma t24_contains : t24.Contains (sourcePower false 33 (3/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (3/2) 2 24 coarse_33_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -227489596311237854163, hi := 227489596311237854163}
lemma t25_contains : t25.Contains (sourcePower false 33 (3/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (3/2) 2 25 coarse_33_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -40889139706780378980, hi := 40889139706780378980}
lemma t26_contains : t26.Contains (sourcePower false 33 (3/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (3/2) 2 26 coarse_33_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -7209743405788544081, hi := 7209743405788544081}
lemma t27_contains : t27.Contains (sourcePower false 33 (3/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (3/2) 2 27 coarse_33_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -1250666140180536284, hi := 1250666140180536284}
lemma t28_contains : t28.Contains (sourcePower false 33 (3/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (3/2) 2 28 coarse_33_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 33 (3/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (3/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 413132907156193137248008392033, hi := 413132907156337197092179967504}
lemma t0_checked : ((hm33_1_0_2.realAnswer).add hm33_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 33 (3/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_1_0_2.realContains hm33_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 138794524586707093405828046616, hi := 138794524586874000297966255048}
lemma t1_checked : ((hm33_1_0_3.realAnswer).add hm33_0_1_3.realAnswer).scale (3) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 33 (3/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_1_0_3.realContains hm33_0_1_3.realContains) (3) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -597530514445852291259996248673, hi := -597530514445705186914073796451}
lemma t2_checked : ((hm33_1_0_4.realAnswer).add hm33_0_1_4.realAnswer).scale (9) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 33 (3/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_1_0_4.realContains hm33_0_1_4.realContains) (9) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -131854892940674363293911289793, hi := -131854892940570001943936373890}
lemma t3_checked : ((hm33_1_0_5.realAnswer).add hm33_0_1_5.realAnswer).scale (27) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 33 (3/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_1_0_5.realContains hm33_0_1_5.realContains) (27) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 369753019859223744111948967984, hi := 369753019859285651406612940297}
lemma t4_checked : ((hm33_1_0_6.realAnswer).add hm33_0_1_6.realAnswer).scale (81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 33 (3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_1_0_6.realContains hm33_0_1_6.realContains) (81) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 49653134072823650563801802443, hi := 49653134072855204146176722227}
lemma t5_checked : ((hm33_1_0_7.realAnswer).add hm33_0_1_7.realAnswer).scale (243) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 33 (3/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_1_0_7.realContains hm33_0_1_7.realContains) (243) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr6 : RBox := {lo := -1033339679297547063192977693, hi := 1033339679297547063192977693}
lemma tr6_contains : tr6.Contains (fullMoment false true 33 8) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 8 33 mixed_33_8) <;> norm_num [tr6,precision]
noncomputable def t6 : RBox := {lo := -140006500497126807885815012512, hi := -116465730928115463084778248546}
lemma t6_checked : ((hm33_1_0_8.realAnswer).add tr6).scale (729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 33 (3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_1_0_8.realContains tr6_contains) (729) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr7 : RBox := {lo := -472929364761718766176575957, hi := 472929364761718766176575957}
lemma tr7_contains : tr7.Contains (fullMoment false true 33 9) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 9 33 mixed_33_9) <;> norm_num [tr7,precision]
noncomputable def t7 : RBox := {lo := -18417328550782952408091838523, hi := -2256445414310481566409059616}
lemma t7_checked : ((hm33_1_0_9.realAnswer).add tr7).scale (2187) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 33 (3/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_1_0_9.realContains tr7_contains) (2187) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -194962356813489477136288679, hi := 194962356813489477136288679}
lemma tr8_contains : tr8.Contains (fullMoment false true 33 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 10 33 mixed_33_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := 23678355810949965020139617069, hi := 33671699741055920388257081044}
lemma t8_checked : ((hm33_1_0_10.realAnswer).add tr8).scale (6561) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 33 (3/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_1_0_10.realContains tr8_contains) (6561) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -73118819746921046531747332, hi := 73118819746921046531747332}
lemma tr9_contains : tr9.Contains (fullMoment false true 33 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 11 33 mixed_33_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -1376352370323839032551494007, hi := 4245513758890284091970065007}
lemma t9_checked : ((hm33_1_0_11.realAnswer).add tr9).scale (19683) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 33 (3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_1_0_11.realContains tr9_contains) (19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -25153474459011621003745446, hi := 25153474459011621003745446}
lemma tr10_contains : tr10.Contains (fullMoment false true 33 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 12 33 mixed_33_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -5939388614488620029288148716, hi := -3038436440015419993243968702}
lemma t10_checked : ((hm33_1_0_12.realAnswer).add tr10).scale (59049) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 33 (3/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_1_0_12.realContains tr10_contains) (59049) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -7991902354459712621332914, hi := 7991902354459712621332914}
lemma tr11_contains : tr11.Contains (fullMoment false true 33 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 13 33 mixed_33_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := -833374057530900407152623719, hi := 549186026829969634717089547}
lemma t11_checked : ((hm33_1_0_13.realAnswer).add tr11).scale (177147) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 33 (3/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_1_0_13.realContains tr11_contains) (177147) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -46939733625600342871073523762, hi := 46939733625600342871073523762}
lemma t12_contains : t12.Contains (sourcePower true 33 (3/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (3/2) 2 12 coarse_33_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -14325273944965435803399662012, hi := 14325273944965435803399662012}
lemma t13_contains : t13.Contains (sourcePower true 33 (3/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (3/2) 2 13 coarse_33_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -4122547382498648728361320336, hi := 4122547382498648728361320336}
lemma t14_contains : t14.Contains (sourcePower true 33 (3/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (3/2) 2 14 coarse_33_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -1122487668878055295737428716, hi := 1122487668878055295737428716}
lemma t15_contains : t15.Contains (sourcePower true 33 (3/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (3/2) 2 15 coarse_33_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -290066870738915377148187494, hi := 290066870738915377148187494}
lemma t16_contains : t16.Contains (sourcePower true 33 (3/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (3/2) 2 16 coarse_33_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -71348940079428091398830425, hi := 71348940079428091398830425}
lemma t17_contains : t17.Contains (sourcePower true 33 (3/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (3/2) 2 17 coarse_33_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -16752295692802850447624612, hi := 16752295692802850447624612}
lemma t18_contains : t18.Contains (sourcePower true 33 (3/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (3/2) 2 18 coarse_33_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -3764968040736910512304789, hi := 3764968040736910512304789}
lemma t19_contains : t19.Contains (sourcePower true 33 (3/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (3/2) 2 19 coarse_33_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -812182741993809472235986, hi := 812182741993809472235986}
lemma t20_contains : t20.Contains (sourcePower true 33 (3/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (3/2) 2 20 coarse_33_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -168648330431872783378767, hi := 168648330431872783378767}
lemma t21_contains : t21.Contains (sourcePower true 33 (3/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (3/2) 2 21 coarse_33_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -33808057854417327530838, hi := 33808057854417327530838}
lemma t22_contains : t22.Contains (sourcePower true 33 (3/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (3/2) 2 22 coarse_33_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -6562935926769463852608, hi := 6562935926769463852608}
lemma t23_contains : t23.Contains (sourcePower true 33 (3/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (3/2) 2 23 coarse_33_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -1237663451307691708881, hi := 1237663451307691708881}
lemma t24_contains : t24.Contains (sourcePower true 33 (3/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (3/2) 2 24 coarse_33_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -227489596311237854163, hi := 227489596311237854163}
lemma t25_contains : t25.Contains (sourcePower true 33 (3/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (3/2) 2 25 coarse_33_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -40889139706780378980, hi := 40889139706780378980}
lemma t26_contains : t26.Contains (sourcePower true 33 (3/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (3/2) 2 26 coarse_33_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -7209743405788544081, hi := 7209743405788544081}
lemma t27_contains : t27.Contains (sourcePower true 33 (3/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (3/2) 2 27 coarse_33_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -1250666140180536284, hi := 1250666140180536284}
lemma t28_contains : t28.Contains (sourcePower true 33 (3/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (3/2) 2 28 coarse_33_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 33 (3/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (3/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 395227717385759961591205982004, hi := 395227717385939799419758436240}
lemma t0_checked : ((hm33_0_0_2.realAnswer).add hm33_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 33 (-1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_0_0_2.realContains hm33_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -86624801278985896238284999909, hi := -86624801278847297388384779226}
lemma t1_checked : ((hm33_0_0_3.realAnswer).add hm33_1_1_3.realAnswer).scale (1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 33 (-1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_0_0_3.realContains hm33_1_1_3.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -254468788797978615648099638379, hi := -254468788797897254197295906113}
lemma t2_checked : ((hm33_0_0_4.realAnswer).add hm33_1_1_4.realAnswer).scale (-1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 33 (-1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_0_0_4.realContains hm33_1_1_4.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 36153373142981060430673558072, hi := 36153373143019526036308068609}
lemma t3_checked : ((hm33_0_0_5.realAnswer).add hm33_1_1_5.realAnswer).scale (1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 33 (-1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_0_0_5.realContains hm33_1_1_5.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 70042280152597657730803640604, hi := 70042280152612867459222818798}
lemma t4_checked : ((hm33_0_0_6.realAnswer).add hm33_1_1_6.realAnswer).scale (-1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 33 (-1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_0_0_6.realContains hm33_1_1_6.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -5918819443187650362180731892, hi := -5918819443182482225702592430}
lemma t5_checked : ((hm33_0_0_7.realAnswer).add hm33_1_1_7.realAnswer).scale (1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 33 (-1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_0_0_7.realContains hm33_1_1_7.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr6 : RBox := {lo := -1033339679297547063192977693, hi := 1033339679297547063192977693}
lemma tr6_contains : tr6.Contains (fullMoment true true 33 8) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 8 33 mixed_33_8) <;> norm_num [tr6,precision]
noncomputable def t6 : RBox := {lo := -11823053891901486507852288055, hi := -9756374533304852466716240666}
lemma t6_checked : ((hm33_0_0_8.realAnswer).add tr6).scale (-1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 33 (-1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_0_0_8.realContains tr6_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr7 : RBox := {lo := -472929364761718766176575957, hi := 472929364761718766176575957}
lemma tr7_contains : tr7.Contains (fullMoment true true 33 9) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 9 33 mixed_33_9) <;> norm_num [tr7,precision]
noncomputable def t7 : RBox := {lo := 52851774468866790010708102, hi := 998710503992713008451335322}
lemma t7_checked : ((hm33_0_0_9.realAnswer).add tr7).scale (1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 33 (-1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_0_0_9.realContains tr7_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -194962356813489477136288679, hi := 194962356813489477136288679}
lemma tr8_contains : tr8.Contains (fullMoment true true 33 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 10 33 mixed_33_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := 876744228555677608973609391, hi := 1266668942182754373412081358}
lemma t8_checked : ((hm33_0_0_10.realAnswer).add tr8).scale (-1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 33 (-1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_0_0_10.realContains tr8_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -73118819746921046531747332, hi := 73118819746921046531747332}
lemma tr9_contains : tr9.Contains (fullMoment true true 33 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 11 33 mixed_33_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -103560982777819340309563026, hi := 42676656716044075116505832}
lemma t9_checked : ((hm33_0_0_11.realAnswer).add tr9).scale (1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 33 (-1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_0_0_11.realContains tr9_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -25153474459011621003745446, hi := 25153474459011621003745446}
lemma tr10_contains : tr10.Contains (fullMoment true true 33 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 12 33 mixed_33_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -99658528875585834468773609, hi := -49351579957558323184494933}
lemma t10_checked : ((hm33_0_0_12.realAnswer).add tr10).scale (-1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 33 (-1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_0_0_12.realContains tr10_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -7991902354459712621332914, hi := 7991902354459712621332914}
lemma tr11_contains : tr11.Contains (fullMoment true true 33 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 13 33 mixed_33_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := -6785261583548426990806744, hi := 9198543125371788974887075}
lemma t11_checked : ((hm33_0_0_13.realAnswer).add tr11).scale (1) 1=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 33 (-1/1) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_0_0_13.realContains tr11_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -361780797737583295981900443, hi := 361780797737583295981900443}
lemma t12_contains : t12.Contains (sourcePower false 33 (-1/1) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (-1/1) 2 12 coarse_33_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -73606567901960173754910411, hi := 73606567901960173754910411}
lemma t13_contains : t13.Contains (sourcePower false 33 (-1/1) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (-1/1) 2 13 coarse_33_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -14121734076649432761423265, hi := 14121734076649432761423265}
lemma t14_contains : t14.Contains (sourcePower false 33 (-1/1) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (-1/1) 2 14 coarse_33_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -2563378237366519688971715, hi := 2563378237366519688971715}
lemma t15_contains : t15.Contains (sourcePower false 33 (-1/1) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (-1/1) 2 15 coarse_33_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -441609070310966499789464, hi := 441609070310966499789464}
lemma t16_contains : t16.Contains (sourcePower false 33 (-1/1) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (-1/1) 2 16 coarse_33_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -72416265063029220396969, hi := 72416265063029220396969}
lemma t17_contains : t17.Contains (sourcePower false 33 (-1/1) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (-1/1) 2 17 coarse_33_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -11335264723425896113982, hi := 11335264723425896113982}
lemma t18_contains : t18.Contains (sourcePower false 33 (-1/1) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (-1/1) 2 18 coarse_33_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -1698350689743612861834, hi := 1698350689743612861834}
lemma t19_contains : t19.Contains (sourcePower false 33 (-1/1) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (-1/1) 2 19 coarse_33_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -244246627530126076516, hi := 244246627530126076516}
lemma t20_contains : t20.Contains (sourcePower false 33 (-1/1) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (-1/1) 2 20 coarse_33_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -33811590927964850998, hi := 33811590927964850998}
lemma t21_contains : t21.Contains (sourcePower false 33 (-1/1) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (-1/1) 2 21 coarse_33_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -4518689746548450098, hi := 4518689746548450098}
lemma t22_contains : t22.Contains (sourcePower false 33 (-1/1) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (-1/1) 2 22 coarse_33_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -584789015037979950, hi := 584789015037979950}
lemma t23_contains : t23.Contains (sourcePower false 33 (-1/1) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (-1/1) 2 23 coarse_33_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -73521159708065903, hi := 73521159708065903}
lemma t24_contains : t24.Contains (sourcePower false 33 (-1/1) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (-1/1) 2 24 coarse_33_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -9009072121423814, hi := 9009072121423814}
lemma t25_contains : t25.Contains (sourcePower false 33 (-1/1) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (-1/1) 2 25 coarse_33_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -1079531297473408, hi := 1079531297473408}
lemma t26_contains : t26.Contains (sourcePower false 33 (-1/1) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (-1/1) 2 26 coarse_33_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -126898302892730, hi := 126898302892730}
lemma t27_contains : t27.Contains (sourcePower false 33 (-1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (-1/1) 2 27 coarse_33_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -14675271295313, hi := 14675271295313}
lemma t28_contains : t28.Contains (sourcePower false 33 (-1/1) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 33 (-1/1) 2 28 coarse_33_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 33 (-1/1) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 33 (-1/1) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 413132907156193137248008392033, hi := 413132907156337197092179967504}
lemma t0_checked : ((hm33_1_0_2.realAnswer).add hm33_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 33 (-1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_1_0_2.realContains hm33_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -92529683057916000198644170032, hi := -92529683057804728937218697744}
lemma t1_checked : ((hm33_1_0_3.realAnswer).add hm33_0_1_3.realAnswer).scale (-1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 33 (-1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_1_0_3.realContains hm33_0_1_3.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -265569117531489907226664999410, hi := -265569117531424527517366131756}
lemma t2_checked : ((hm33_1_0_4.realAnswer).add hm33_0_1_4.realAnswer).scale (1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 33 (-1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_1_0_4.realContains hm33_0_1_4.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 39068116426835556131536703375, hi := 39068116426866478013010752531}
lemma t3_checked : ((hm33_1_0_5.realAnswer).add hm33_0_1_5.realAnswer).scale (-1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 33 (-1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_1_0_5.realContains hm33_0_1_5.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 73037633552439258096187450466, hi := 73037633552451486697602556108}
lemma t4_checked : ((hm33_1_0_6.realAnswer).add hm33_0_1_6.realAnswer).scale (1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 33 (-1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_1_0_6.realContains hm33_0_1_6.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -6538684322351302603611749429, hi := -6538684322347147399348385507}
lemma t5_checked : ((hm33_1_0_7.realAnswer).add hm33_0_1_7.realAnswer).scale (-1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 33 (-1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_1_0_7.realContains hm33_0_1_7.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr6 : RBox := {lo := -1033339679297547063192977693, hi := 1033339679297547063192977693}
lemma tr6_contains : tr6.Contains (fullMoment false true 33 8) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 8 33 mixed_33_8) <;> norm_num [tr6,precision]
noncomputable def t6 : RBox := {lo := -12291380016208663518096242525, hi := -10224700657612331464232932657}
lemma t6_checked : ((hm33_1_0_8.realAnswer).add tr6).scale (1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 33 (-1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_1_0_8.realContains tr6_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr7 : RBox := {lo := -472929364761718766176575957, hi := 472929364761718766176575957}
lemma tr7_contains : tr7.Contains (fullMoment false true 33 9) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 9 33 mixed_33_9) <;> norm_num [tr7,precision]
noncomputable def t7 : RBox := {lo := 132064477838016296525084422, hi := 1077923207361782308292526443}
lemma t7_checked : ((hm33_1_0_9.realAnswer).add tr7).scale (-1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 33 (-1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_1_0_9.realContains tr7_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -194962356813489477136288679, hi := 194962356813489477136288679}
lemma tr8_contains : tr8.Contains (fullMoment false true 33 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 10 33 mixed_33_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := 923892560219965103666474923, hi := 1313817273847022651942358291}
lemma t8_checked : ((hm33_1_0_10.realAnswer).add tr8).scale (1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 33 (-1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_1_0_10.realContains tr8_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -73118819746921046531747332, hi := 73118819746921046531747332}
lemma tr9_contains : tr9.Contains (fullMoment false true 33 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 11 33 mixed_33_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -110435555786812246867280053, hi := 35802083707046973767533655}
lemma t9_checked : ((hm33_1_0_11.realAnswer).add tr9).scale (-1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 33 (-1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_1_0_11.realContains tr9_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -25153474459011621003745446, hi := 25153474459011621003745446}
lemma tr10_contains : tr10.Contains (fullMoment false true 33 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 12 33 mixed_33_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -102998085339910022354164580, hi := -52691136421883352352822638}
lemma t10_checked : ((hm33_1_0_12.realAnswer).add tr10).scale (1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 33 (-1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_1_0_12.realContains tr10_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -7991902354459712621332914, hi := 7991902354459712621332914}
lemma tr11_contains : tr11.Contains (fullMoment false true 33 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 13 33 mixed_33_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := -6349150609086113859679246, hi := 9634654099833946010085259}
lemma t11_checked : ((hm33_1_0_13.realAnswer).add tr11).scale (-1) 1=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 33 (-1/1) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm33_1_0_13.realContains tr11_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -361780797737583295981900443, hi := 361780797737583295981900443}
lemma t12_contains : t12.Contains (sourcePower true 33 (-1/1) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (-1/1) 2 12 coarse_33_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -73606567901960173754910411, hi := 73606567901960173754910411}
lemma t13_contains : t13.Contains (sourcePower true 33 (-1/1) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (-1/1) 2 13 coarse_33_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -14121734076649432761423265, hi := 14121734076649432761423265}
lemma t14_contains : t14.Contains (sourcePower true 33 (-1/1) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (-1/1) 2 14 coarse_33_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -2563378237366519688971715, hi := 2563378237366519688971715}
lemma t15_contains : t15.Contains (sourcePower true 33 (-1/1) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (-1/1) 2 15 coarse_33_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -441609070310966499789464, hi := 441609070310966499789464}
lemma t16_contains : t16.Contains (sourcePower true 33 (-1/1) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (-1/1) 2 16 coarse_33_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -72416265063029220396969, hi := 72416265063029220396969}
lemma t17_contains : t17.Contains (sourcePower true 33 (-1/1) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (-1/1) 2 17 coarse_33_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -11335264723425896113982, hi := 11335264723425896113982}
lemma t18_contains : t18.Contains (sourcePower true 33 (-1/1) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (-1/1) 2 18 coarse_33_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -1698350689743612861834, hi := 1698350689743612861834}
lemma t19_contains : t19.Contains (sourcePower true 33 (-1/1) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (-1/1) 2 19 coarse_33_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -244246627530126076516, hi := 244246627530126076516}
lemma t20_contains : t20.Contains (sourcePower true 33 (-1/1) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (-1/1) 2 20 coarse_33_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -33811590927964850998, hi := 33811590927964850998}
lemma t21_contains : t21.Contains (sourcePower true 33 (-1/1) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (-1/1) 2 21 coarse_33_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -4518689746548450098, hi := 4518689746548450098}
lemma t22_contains : t22.Contains (sourcePower true 33 (-1/1) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (-1/1) 2 22 coarse_33_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -584789015037979950, hi := 584789015037979950}
lemma t23_contains : t23.Contains (sourcePower true 33 (-1/1) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (-1/1) 2 23 coarse_33_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -73521159708065903, hi := 73521159708065903}
lemma t24_contains : t24.Contains (sourcePower true 33 (-1/1) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (-1/1) 2 24 coarse_33_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -9009072121423814, hi := 9009072121423814}
lemma t25_contains : t25.Contains (sourcePower true 33 (-1/1) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (-1/1) 2 25 coarse_33_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -1079531297473408, hi := 1079531297473408}
lemma t26_contains : t26.Contains (sourcePower true 33 (-1/1) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (-1/1) 2 26 coarse_33_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -126898302892730, hi := 126898302892730}
lemma t27_contains : t27.Contains (sourcePower true 33 (-1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (-1/1) 2 27 coarse_33_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -14675271295313, hi := 14675271295313}
lemma t28_contains : t28.Contains (sourcePower true 33 (-1/1) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 33 (-1/1) 2 28 coarse_33_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 33 (-1/1) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 33 (-1/1) 2) k.val := by
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
end SharpPlanar.Bernstein33

end OAI
