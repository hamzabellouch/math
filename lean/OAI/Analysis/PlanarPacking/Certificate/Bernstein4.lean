import OAI.Analysis.PlanarPacking.Certificate.LowBlock4_0
import OAI.Analysis.PlanarPacking.Certificate.LowBlock4_1
import OAI.Analysis.PlanarPacking.Certificate.LowBlock4_2
import OAI.Analysis.PlanarPacking.Certificate.LowBlock4_10
import OAI.Analysis.PlanarPacking.Certificate.LowBlock4_11
import OAI.Analysis.PlanarPacking.Certificate.LowBlock4_12
import OAI.Analysis.PlanarPacking.Certificate.CoarseBound4

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein4
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 80884657456589348145581269305, hi := 80884657456766786584480747264}
lemma t0_checked : ((hm4_0_0_2.realAnswer).add hm4_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 4 (3/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_2.realContains hm4_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 139791813805479798323135149852, hi := 139791813805696487588269988516}
lemma t1_checked : ((hm4_0_0_3.realAnswer).add hm4_1_1_3.realAnswer).scale (-3) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 4 (3/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_3.realContains hm4_1_1_3.realContains) (-3) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -96730123187839454795632234941, hi := -96730123187630680120214921277}
lemma t2_checked : ((hm4_0_0_4.realAnswer).add hm4_1_1_4.realAnswer).scale (-9) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 4 (3/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_4.realContains hm4_1_1_4.realContains) (-9) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -76838708357975737248590615823, hi := -76838708357804074682373010337}
lemma t3_checked : ((hm4_0_0_5.realAnswer).add hm4_1_1_5.realAnswer).scale (-27) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 4 (3/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_5.realContains hm4_1_1_5.realContains) (-27) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 192093014099630178287472623275, hi := 192093014099758333454559124584}
lemma t4_checked : ((hm4_0_0_6.realAnswer).add hm4_1_1_6.realAnswer).scale (-81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 4 (3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_6.realContains hm4_1_1_6.realContains) (-81) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -75935647850081962873397052894, hi := -75935647849991502023692710835}
lemma t5_checked : ((hm4_0_0_7.realAnswer).add hm4_1_1_7.realAnswer).scale (-243) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 4 (3/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_7.realContains hm4_1_1_7.realContains) (-243) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -154901791904529157584222715891, hi := -154901791904467883308057443095}
lemma t6_checked : ((hm4_0_0_8.realAnswer).add hm4_1_1_8.realAnswer).scale (-729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 4 (3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_8.realContains hm4_1_1_8.realContains) (-729) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 85711559156684269301292983627, hi := 85711559156723978482406965676}
lemma t7_checked : ((hm4_0_0_9.realAnswer).add hm4_1_1_9.realAnswer).scale (-2187) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 4 (3/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_9.realContains hm4_1_1_9.realContains) (-2187) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 66050726204208501856712150694, hi := 66050726204232916053367003078}
lemma t8_checked : ((hm4_0_0_10.realAnswer).add hm4_1_1_10.realAnswer).scale (-6561) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 4 (3/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_10.realContains hm4_1_1_10.realContains) (-6561) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := -39632702510643693101740406477, hi := -39632702510629558378891943700}
lemma t9_checked : ((hm4_0_0_11.realAnswer).add hm4_1_1_11.realAnswer).scale (-19683) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 4 (3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_11.realContains hm4_1_1_11.realContains) (-19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -17348403510348261431316165212, hi := -17348403510340593538146314596}
lemma t10_checked : ((hm4_0_0_12.realAnswer).add hm4_1_1_12.realAnswer).scale (-59049) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 4 (3/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_12.realContains hm4_1_1_12.realContains) (-59049) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := 11664924372964301880758280875, hi := 11664924372968191766583187301}
lemma t11_checked : ((hm4_0_0_13.realAnswer).add hm4_1_1_13.realAnswer).scale (-177147) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 4 (3/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_13.realContains hm4_1_1_13.realContains) (-177147) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := 2883461159386868971786162885, hi := 2883461159388714397192254109}
lemma t12_checked : ((hm4_0_0_14.realAnswer).add hm4_1_1_14.realAnswer).scale (-531441) 4096=t12 := by decide +kernel
lemma t12_contains : t12.Contains (sourcePower false 4 (3/2) 2 12) := by
  rw [← t12_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_14.realContains hm4_1_1_14.realContains) (-531441) 4096 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t13 : RBox := {lo := -2457858900531999868684092220, hi := -2457858900531179562673909517}
lemma t13_checked : ((hm4_0_0_15.realAnswer).add hm4_1_1_15.realAnswer).scale (-1594323) 8192=t13 := by decide +kernel
lemma t13_contains : t13.Contains (sourcePower false 4 (3/2) 2 13) := by
  rw [← t13_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_15.realContains hm4_1_1_15.realContains) (-1594323) 8192 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t14 : RBox := {lo := -264339825433392761687391741, hi := -264339825433049819853358042}
lemma t14_checked : ((hm4_0_0_16.realAnswer).add hm4_1_1_16.realAnswer).scale (-4782969) 16384=t14 := by decide +kernel
lemma t14_contains : t14.Contains (sourcePower false 4 (3/2) 2 14) := by
  rw [← t14_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_16.realContains hm4_1_1_16.realContains) (-4782969) 16384 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t15 : RBox := {lo := 389543758987429555518430093, hi := 389543758987564891016704021}
lemma t15_checked : ((hm4_0_0_17.realAnswer).add hm4_1_1_17.realAnswer).scale (-14348907) 32768=t15 := by decide +kernel
lemma t15_contains : t15.Contains (sourcePower false 4 (3/2) 2 15) := by
  rw [← t15_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_17.realContains hm4_1_1_17.realContains) (-14348907) 32768 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t16 : RBox := {lo := -4700502752403218149917290, hi := -4700502752352570853054839}
lemma t16_checked : ((hm4_0_0_18.realAnswer).add hm4_1_1_18.realAnswer).scale (-43046721) 65536=t16 := by decide +kernel
lemma t16_contains : t16.Contains (sourcePower false 4 (3/2) 2 16) := by
  rw [← t16_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_18.realContains hm4_1_1_18.realContains) (-43046721) 65536 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t17 : RBox := {lo := -46835610325913807725919159, hi := -46835610325895604597978284}
lemma t17_checked : ((hm4_0_0_19.realAnswer).add hm4_1_1_19.realAnswer).scale (-129140163) 131072=t17 := by decide +kernel
lemma t17_contains : t17.Contains (sourcePower false 4 (3/2) 2 17) := by
  rw [← t17_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_19.realContains hm4_1_1_19.realContains) (-129140163) 131072 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t18 : RBox := {lo := -26390367558920437394309086425, hi := 26390367558920437394309086425}
lemma t18_contains : t18.Contains (sourcePower false 4 (3/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 4 (3/2) 2 18 coarse_4_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -10630176914062335878967891547, hi := 10630176914062335878967891547}
lemma t19_contains : t19.Contains (sourcePower false 4 (3/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 4 (3/2) 2 19 coarse_4_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -4170725355037302657130575501, hi := 4170725355037302657130575501}
lemma t20_contains : t20.Contains (sourcePower false 4 (3/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 4 (3/2) 2 20 coarse_4_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -1597009396858088585591364134, hi := 1597009396858088585591364134}
lemma t21_contains : t21.Contains (sourcePower false 4 (3/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 4 (3/2) 2 21 coarse_4_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -597753179407336111151532935, hi := 597753179407336111151532935}
lemma t22_contains : t22.Contains (sourcePower false 4 (3/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 4 (3/2) 2 22 coarse_4_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -218976203799358635786654501, hi := 218976203799358635786654501}
lemma t23_contains : t23.Contains (sourcePower false 4 (3/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 4 (3/2) 2 23 coarse_4_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -78583460860525641873577874, hi := 78583460860525641873577874}
lemma t24_contains : t24.Contains (sourcePower false 4 (3/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 4 (3/2) 2 24 coarse_4_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -27643541892856090644505557, hi := 27643541892856090644505557}
lemma t25_contains : t25.Contains (sourcePower false 4 (3/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 4 (3/2) 2 25 coarse_4_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -9535506295045417796923251, hi := 9535506295045417796923251}
lemma t26_contains : t26.Contains (sourcePower false 4 (3/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 4 (3/2) 2 26 coarse_4_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -3225929251695361699015075, hi := 3225929251695361699015075}
lemma t27_contains : t27.Contains (sourcePower false 4 (3/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 4 (3/2) 2 27 coarse_4_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -1070388235927703327726843, hi := 1070388235927703327726843}
lemma t28_contains : t28.Contains (sourcePower false 4 (3/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 4 (3/2) 2 28 coarse_4_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 4 (3/2) 2 r.val) := by
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
lemma bound0 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound1 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound2 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound3 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound4 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound5 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound6 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound7 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound8 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound9 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound10 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound11 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound12 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound13 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound14 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound15 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound16 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound17 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound18 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound19 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound20 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound21 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound22 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound23 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound24 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound25 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound26 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound27 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound28 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound (k : Fin 29) : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (3/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 72075694851031639684590459061, hi := 72075694851181594356524528502}
lemma t0_checked : ((hm4_1_0_2.realAnswer).add hm4_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 4 (3/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_2.realContains hm4_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 131738893599512214554906166970, hi := 131738893599699422297688703937}
lemma t1_checked : ((hm4_1_0_3.realAnswer).add hm4_0_1_3.realAnswer).scale (3) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 4 (3/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_3.realContains hm4_0_1_3.realContains) (3) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -73047029906560067248096696190, hi := -73047029906373434933740155612}
lemma t2_checked : ((hm4_1_0_4.realAnswer).add hm4_0_1_4.realAnswer).scale (9) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 4 (3/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_4.realContains hm4_0_1_4.realContains) (9) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -71895139079214397236399512025, hi := -71895139079053338473133000036}
lemma t3_checked : ((hm4_1_0_5.realAnswer).add hm4_0_1_5.realAnswer).scale (27) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 4 (3/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_5.realContains hm4_0_1_5.realContains) (27) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 166384699078015473285066920876, hi := 166384699078143053822686673287}
lemma t4_checked : ((hm4_1_0_6.realAnswer).add hm4_0_1_6.realAnswer).scale (81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 4 (3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_6.realContains hm4_0_1_6.realContains) (81) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -66200652916064566940345961954, hi := -66200652915968935637889645275}
lemma t5_checked : ((hm4_1_0_7.realAnswer).add hm4_0_1_7.realAnswer).scale (243) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 4 (3/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_7.realContains hm4_0_1_7.realContains) (243) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -149606308194523224131311468005, hi := -149606308194455105627866921045}
lemma t6_checked : ((hm4_1_0_8.realAnswer).add hm4_0_1_8.realAnswer).scale (729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 4 (3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_8.realContains hm4_0_1_8.realContains) (729) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 81216271104656410704724829831, hi := 81216271104702178116952657953}
lemma t7_checked : ((hm4_1_0_9.realAnswer).add hm4_0_1_9.realAnswer).scale (2187) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 4 (3/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_9.realContains hm4_0_1_9.realContains) (2187) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 66836946559144755560511457224, hi := 66836946559173556844488036347}
lemma t8_checked : ((hm4_1_0_10.realAnswer).add hm4_0_1_10.realAnswer).scale (6561) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 4 (3/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_10.realContains hm4_0_1_10.realContains) (6561) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := -39189942941445416069518200784, hi := -39189942941428506754236754516}
lemma t9_checked : ((hm4_1_0_11.realAnswer).add hm4_0_1_11.realAnswer).scale (19683) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 4 (3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_11.realContains hm4_0_1_11.realContains) (19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -17785860130578284484297874047, hi := -17785860130569037475476938317}
lemma t10_checked : ((hm4_1_0_12.realAnswer).add hm4_0_1_12.realAnswer).scale (59049) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 4 (3/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_12.realContains hm4_0_1_12.realContains) (59049) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := 11752380565555018796193827282, hi := 11752380565559730893105680066}
lemma t11_checked : ((hm4_1_0_13.realAnswer).add hm4_0_1_13.realAnswer).scale (177147) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 4 (3/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_13.realContains hm4_0_1_13.realContains) (177147) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := 2977533766560135599220349578, hi := 2977533766562376655770730103}
lemma t12_checked : ((hm4_1_0_14.realAnswer).add hm4_0_1_14.realAnswer).scale (531441) 4096=t12 := by decide +kernel
lemma t12_contains : t12.Contains (sourcePower true 4 (3/2) 2 12) := by
  rw [← t12_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_14.realContains hm4_0_1_14.realContains) (531441) 4096 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t13 : RBox := {lo := -2502411808338570390213452831, hi := -2502411808337572869153773733}
lemma t13_checked : ((hm4_1_0_15.realAnswer).add hm4_0_1_15.realAnswer).scale (1594323) 8192=t13 := by decide +kernel
lemma t13_contains : t13.Contains (sourcePower true 4 (3/2) 2 13) := by
  rw [← t13_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_15.realContains hm4_0_1_15.realContains) (1594323) 8192 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t14 : RBox := {lo := -276094401229282325792702664, hi := -276094401228864994485053695}
lemma t14_checked : ((hm4_1_0_16.realAnswer).add hm4_0_1_16.realAnswer).scale (4782969) 16384=t14 := by decide +kernel
lemma t14_contains : t14.Contains (sourcePower true 4 (3/2) 2 14) := by
  rw [← t14_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_16.realContains hm4_0_1_16.realContains) (4782969) 16384 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t15 : RBox := {lo := 400000374370895666518958182, hi := 400000374371060403097449198}
lemma t15_checked : ((hm4_1_0_17.realAnswer).add hm4_0_1_17.realAnswer).scale (14348907) 32768=t15 := by decide +kernel
lemma t15_contains : t15.Contains (sourcePower true 4 (3/2) 2 15) := by
  rw [← t15_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_17.realContains hm4_0_1_17.realContains) (14348907) 32768 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t16 : RBox := {lo := -4519450006996434933695199, hi := -4519450006934811458951484}
lemma t16_checked : ((hm4_1_0_18.realAnswer).add hm4_0_1_18.realAnswer).scale (43046721) 65536=t16 := by decide +kernel
lemma t16_contains : t16.Contains (sourcePower true 4 (3/2) 2 16) := by
  rw [← t16_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_18.realContains hm4_0_1_18.realContains) (43046721) 65536 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t17 : RBox := {lo := -48405561176769681371654401, hi := -48405561176747595112130946}
lemma t17_checked : ((hm4_1_0_19.realAnswer).add hm4_0_1_19.realAnswer).scale (129140163) 131072=t17 := by decide +kernel
lemma t17_contains : t17.Contains (sourcePower true 4 (3/2) 2 17) := by
  rw [← t17_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_19.realContains hm4_0_1_19.realContains) (129140163) 131072 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t18 : RBox := {lo := -26390367558920437394309086425, hi := 26390367558920437394309086425}
lemma t18_contains : t18.Contains (sourcePower true 4 (3/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 4 (3/2) 2 18 coarse_4_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -10630176914062335878967891547, hi := 10630176914062335878967891547}
lemma t19_contains : t19.Contains (sourcePower true 4 (3/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 4 (3/2) 2 19 coarse_4_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -4170725355037302657130575501, hi := 4170725355037302657130575501}
lemma t20_contains : t20.Contains (sourcePower true 4 (3/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 4 (3/2) 2 20 coarse_4_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -1597009396858088585591364134, hi := 1597009396858088585591364134}
lemma t21_contains : t21.Contains (sourcePower true 4 (3/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 4 (3/2) 2 21 coarse_4_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -597753179407336111151532935, hi := 597753179407336111151532935}
lemma t22_contains : t22.Contains (sourcePower true 4 (3/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 4 (3/2) 2 22 coarse_4_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -218976203799358635786654501, hi := 218976203799358635786654501}
lemma t23_contains : t23.Contains (sourcePower true 4 (3/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 4 (3/2) 2 23 coarse_4_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -78583460860525641873577874, hi := 78583460860525641873577874}
lemma t24_contains : t24.Contains (sourcePower true 4 (3/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 4 (3/2) 2 24 coarse_4_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -27643541892856090644505557, hi := 27643541892856090644505557}
lemma t25_contains : t25.Contains (sourcePower true 4 (3/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 4 (3/2) 2 25 coarse_4_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -9535506295045417796923251, hi := 9535506295045417796923251}
lemma t26_contains : t26.Contains (sourcePower true 4 (3/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 4 (3/2) 2 26 coarse_4_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -3225929251695361699015075, hi := 3225929251695361699015075}
lemma t27_contains : t27.Contains (sourcePower true 4 (3/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 4 (3/2) 2 27 coarse_4_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -1070388235927703327726843, hi := 1070388235927703327726843}
lemma t28_contains : t28.Contains (sourcePower true 4 (3/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 4 (3/2) 2 28 coarse_4_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 4 (3/2) 2 r.val) := by
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
lemma bound0 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound1 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound2 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound3 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound4 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound5 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound6 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound7 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound8 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound9 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound10 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound11 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound12 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound13 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound14 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound15 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound16 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound17 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound18 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound19 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound20 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound21 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound22 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound23 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound24 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound25 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound26 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound27 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound28 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound (k : Fin 29) : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 80884657456589348145581269305, hi := 80884657456766786584480747264}
lemma t0_checked : ((hm4_0_0_2.realAnswer).add hm4_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 4 (-1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_2.realContains hm4_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -46597271268565495862756662839, hi := -46597271268493266107711716617}
lemma t1_checked : ((hm4_0_0_3.realAnswer).add hm4_1_1_3.realAnswer).scale (1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 4 (-1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_3.realContains hm4_1_1_3.realContains) (1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -10747791465315494977292470549, hi := -10747791465292297791134991253}
lemma t2_checked : ((hm4_0_0_4.realAnswer).add hm4_1_1_4.realAnswer).scale (-1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 4 (-1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_4.realContains hm4_1_1_4.realContains) (-1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 2845878087326076840087889271, hi := 2845878087332434712910763549}
lemma t3_checked : ((hm4_0_0_5.realAnswer).add hm4_1_1_5.realAnswer).scale (1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 4 (-1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_5.realContains hm4_1_1_5.realContains) (1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 2371518692588026892437933620, hi := 2371518692589609054994557094}
lemma t4_checked : ((hm4_0_0_6.realAnswer).add hm4_1_1_6.realAnswer).scale (-1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 4 (-1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_6.realContains hm4_1_1_6.realContains) (-1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 312492377983504123554290991, hi := 312492377983876390425502276}
lemma t5_checked : ((hm4_0_0_7.realAnswer).add hm4_1_1_7.realAnswer).scale (1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 4 (-1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_7.realContains hm4_1_1_7.realContains) (1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -212485311254498158551745838, hi := -212485311254414106046718028}
lemma t6_checked : ((hm4_0_0_8.realAnswer).add hm4_1_1_8.realAnswer).scale (-1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 4 (-1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_8.realContains hm4_1_1_8.realContains) (-1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -39191385073947863960862811, hi := -39191385073929707042200724}
lemma t7_checked : ((hm4_0_0_9.realAnswer).add hm4_1_1_9.realAnswer).scale (1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 4 (-1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_9.realContains hm4_1_1_9.realContains) (1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 10067173632709724410411850, hi := 10067173632713445519488951}
lemma t8_checked : ((hm4_0_0_10.realAnswer).add hm4_1_1_10.realAnswer).scale (-1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 4 (-1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_10.realContains hm4_1_1_10.realContains) (-1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := 2013549891308721149158763, hi := 2013549891309439267476524}
lemma t9_checked : ((hm4_0_0_11.realAnswer).add hm4_1_1_11.realAnswer).scale (1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 4 (-1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_11.realContains hm4_1_1_11.realContains) (1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -293796736783828031487683, hi := -293796736783698175043545}
lemma t10_checked : ((hm4_0_0_12.realAnswer).add hm4_1_1_12.realAnswer).scale (-1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 4 (-1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_12.realContains hm4_1_1_12.realContains) (-1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -65848839511638310367002, hi := -65848839511616351847664}
lemma t11_checked : ((hm4_0_0_13.realAnswer).add hm4_1_1_13.realAnswer).scale (1) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 4 (-1/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_13.realContains hm4_1_1_13.realContains) (1) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := 5425740880712758277562, hi := 5425740880716230771040}
lemma t12_checked : ((hm4_0_0_14.realAnswer).add hm4_1_1_14.realAnswer).scale (-1) 4096=t12 := by decide +kernel
lemma t12_contains : t12.Contains (sourcePower false 4 (-1/2) 2 12) := by
  rw [← t12_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_14.realContains hm4_1_1_14.realContains) (-1) 4096 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t13 : RBox := {lo := 1541631714860275842896, hi := 1541631714860790359723}
lemma t13_checked : ((hm4_0_0_15.realAnswer).add hm4_1_1_15.realAnswer).scale (1) 8192=t13 := by decide +kernel
lemma t13_contains : t13.Contains (sourcePower false 4 (-1/2) 2 13) := by
  rw [← t13_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_15.realContains hm4_1_1_15.realContains) (1) 8192 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t14 : RBox := {lo := -55266890802217777638, hi := -55266890802146077018}
lemma t14_checked : ((hm4_0_0_16.realAnswer).add hm4_1_1_16.realAnswer).scale (-1) 16384=t14 := by decide +kernel
lemma t14_contains : t14.Contains (sourcePower false 4 (-1/2) 2 14) := by
  rw [← t14_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_16.realContains hm4_1_1_16.realContains) (-1) 16384 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t15 : RBox := {lo := -27147974336133399640, hi := -27147974336123967875}
lemma t15_checked : ((hm4_0_0_17.realAnswer).add hm4_1_1_17.realAnswer).scale (1) 32768=t15 := by decide +kernel
lemma t15_contains : t15.Contains (sourcePower false 4 (-1/2) 2 15) := by
  rw [← t15_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_17.realContains hm4_1_1_17.realContains) (1) 32768 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t16 : RBox := {lo := -109195372915935181, hi := -109195372914758614}
lemma t16_checked : ((hm4_0_0_18.realAnswer).add hm4_1_1_18.realAnswer).scale (-1) 65536=t16 := by decide +kernel
lemma t16_contains : t16.Contains (sourcePower false 4 (-1/2) 2 16) := by
  rw [← t16_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_18.realContains hm4_1_1_18.realContains) (-1) 65536 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t17 : RBox := {lo := 362672690183112163, hi := 362672690183253120}
lemma t17_checked : ((hm4_0_0_19.realAnswer).add hm4_1_1_19.realAnswer).scale (1) 131072=t17 := by decide +kernel
lemma t17_contains : t17.Contains (sourcePower false 4 (-1/2) 2 17) := by
  rw [← t17_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_0_0_19.realContains hm4_1_1_19.realContains) (1) 131072 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t18 : RBox := {lo := -68118151487131175952, hi := 68118151487131175952}
lemma t18_contains : t18.Contains (sourcePower false 4 (-1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 4 (-1/2) 2 18 coarse_4_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -9146114894009762331, hi := 9146114894009762331}
lemma t19_contains : t19.Contains (sourcePower false 4 (-1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 4 (-1/2) 2 19 coarse_4_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -1196152349953484451, hi := 1196152349953484451}
lemma t20_contains : t20.Contains (sourcePower false 4 (-1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 4 (-1/2) 2 20 coarse_4_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -152672607307377610, hi := 152672607307377610}
lemma t21_contains : t21.Contains (sourcePower false 4 (-1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 4 (-1/2) 2 21 coarse_4_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -19048215288304101, hi := 19048215288304101}
lemma t22_contains : t22.Contains (sourcePower false 4 (-1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 4 (-1/2) 2 22 coarse_4_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -2325991182024511, hi := 2325991182024511}
lemma t23_contains : t23.Contains (sourcePower false 4 (-1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 4 (-1/2) 2 23 coarse_4_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -278240944058669, hi := 278240944058669}
lemma t24_contains : t24.Contains (sourcePower false 4 (-1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 4 (-1/2) 2 24 coarse_4_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -32625886368317, hi := 32625886368317}
lemma t25_contains : t25.Contains (sourcePower false 4 (-1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 4 (-1/2) 2 25 coarse_4_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -3751380654625, hi := 3751380654625}
lemma t26_contains : t26.Contains (sourcePower false 4 (-1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 4 (-1/2) 2 26 coarse_4_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -423039539925, hi := 423039539925}
lemma t27_contains : t27.Contains (sourcePower false 4 (-1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 4 (-1/2) 2 27 coarse_4_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -46789262002, hi := 46789262002}
lemma t28_contains : t28.Contains (sourcePower false 4 (-1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 4 (-1/2) 2 28 coarse_4_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 4 (-1/2) 2 r.val) := by
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
lemma bound0 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound1 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound2 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound3 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound4 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound5 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound6 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound7 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound8 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound9 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound10 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound11 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound12 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound13 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound14 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound15 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound16 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound17 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound18 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound19 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound20 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound21 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound22 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound23 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound24 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound25 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound26 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound27 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound28 : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound (k : Fin 29) : (1:ℝ)/50<powerToBernstein 28 (sourcePower false 4 (-1/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 72075694851031639684590459061, hi := 72075694851181594356524528502}
lemma t0_checked : ((hm4_1_0_2.realAnswer).add hm4_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 4 (-1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_2.realContains hm4_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -43912964533233140765896234646, hi := -43912964533170738184968722323}
lemma t1_checked : ((hm4_1_0_3.realAnswer).add hm4_0_1_3.realAnswer).scale (-1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 4 (-1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_3.realContains hm4_0_1_3.realContains) (-1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -8116336656284451916455188466, hi := -8116336656263714992637795068}
lemma t2_checked : ((hm4_1_0_4.realAnswer).add hm4_0_1_4.realAnswer).scale (1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 4 (-1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_4.realContains hm4_0_1_4.realContains) (1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 2662782928853827350856777779, hi := 2662782928859792490237018964}
lemma t3_checked : ((hm4_1_0_5.realAnswer).add hm4_0_1_5.realAnswer).scale (-1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 4 (-1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_5.realContains hm4_0_1_5.realContains) (-1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 2054132087382907077593418776, hi := 2054132087384482145959094732}
lemma t4_checked : ((hm4_1_0_6.realAnswer).add hm4_0_1_6.realAnswer).scale (1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 4 (-1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_6.realContains hm4_0_1_6.realContains) (1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 272430670436086154888434754, hi := 272430670436479699342987498}
lemma t5_checked : ((hm4_1_0_7.realAnswer).add hm4_0_1_7.realAnswer).scale (-1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 4 (-1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_7.realContains hm4_0_1_7.realContains) (-1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -205221273243516082484652220, hi := -205221273243422641464838026}
lemma t6_checked : ((hm4_1_0_8.realAnswer).add hm4_0_1_8.realAnswer).scale (1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 4 (-1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_8.realContains hm4_0_1_8.realContains) (1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -37135926431048092417445203, hi := -37135926431027165388534444}
lemma t7_checked : ((hm4_1_0_9.realAnswer).add hm4_0_1_9.realAnswer).scale (-1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 4 (-1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_9.realContains hm4_0_1_9.realContains) (-1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 10187006029438310556395588, hi := 10187006029442700326853839}
lemma t8_checked : ((hm4_1_0_10.realAnswer).add hm4_0_1_10.realAnswer).scale (1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 4 (-1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_10.realContains hm4_0_1_10.realContains) (1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := 1991055374761393423473899, hi := 1991055374762252505691115}
lemma t9_checked : ((hm4_1_0_11.realAnswer).add hm4_0_1_11.realAnswer).scale (-1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 4 (-1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_11.realContains hm4_0_1_11.realContains) (-1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -301205103059802612818132, hi := -301205103059646013911784}
lemma t10_checked : ((hm4_1_0_12.realAnswer).add hm4_0_1_12.realAnswer).scale (1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 4 (-1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_12.realContains hm4_0_1_12.realContains) (1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -66342532278614545508001, hi := -66342532278587945583012}
lemma t11_checked : ((hm4_1_0_13.realAnswer).add hm4_0_1_13.realAnswer).scale (-1) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 4 (-1/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_13.realContains hm4_0_1_13.realContains) (-1) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := 5602755087695784855177, hi := 5602755087700001798452}
lemma t12_checked : ((hm4_1_0_14.realAnswer).add hm4_0_1_14.realAnswer).scale (1) 4096=t12 := by decide +kernel
lemma t12_contains : t12.Contains (sourcePower true 4 (-1/2) 2 12) := by
  rw [← t12_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_14.realContains hm4_0_1_14.realContains) (1) 4096 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t13 : RBox := {lo := 1569576433594430281162, hi := 1569576433595055951783}
lemma t13_checked : ((hm4_1_0_15.realAnswer).add hm4_0_1_15.realAnswer).scale (-1) 8192=t13 := by decide +kernel
lemma t13_contains : t13.Contains (sourcePower true 4 (-1/2) 2 13) := by
  rw [← t13_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_15.realContains hm4_0_1_15.realContains) (-1) 8192 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t14 : RBox := {lo := -57724480595479988642, hi := -57724480595392735032}
lemma t14_checked : ((hm4_1_0_16.realAnswer).add hm4_0_1_16.realAnswer).scale (1) 16384=t14 := by decide +kernel
lemma t14_contains : t14.Contains (sourcePower true 4 (-1/2) 2 14) := by
  rw [← t14_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_16.realContains hm4_0_1_16.realContains) (1) 16384 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t15 : RBox := {lo := -27876713841065413770, hi := -27876713841053932994}
lemma t15_checked : ((hm4_1_0_17.realAnswer).add hm4_0_1_17.realAnswer).scale (-1) 32768=t15 := by decide +kernel
lemma t15_contains : t15.Contains (sourcePower true 4 (-1/2) 2 15) := by
  rw [← t15_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_17.realContains hm4_0_1_17.realContains) (-1) 32768 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t16 : RBox := {lo := -104989413874205075, hi := -104989413872773525}
lemma t16_checked : ((hm4_1_0_18.realAnswer).add hm4_0_1_18.realAnswer).scale (1) 65536=t16 := by decide +kernel
lemma t16_contains : t16.Contains (sourcePower true 4 (-1/2) 2 16) := by
  rw [← t16_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_18.realContains hm4_0_1_18.realContains) (1) 65536 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t17 : RBox := {lo := 374829642864455693, hi := 374829642864626719}
lemma t17_checked : ((hm4_1_0_19.realAnswer).add hm4_0_1_19.realAnswer).scale (-1) 131072=t17 := by decide +kernel
lemma t17_contains : t17.Contains (sourcePower true 4 (-1/2) 2 17) := by
  rw [← t17_checked]
  convert RBox.contains_scale (RBox.contains_add hm4_1_0_19.realContains hm4_0_1_19.realContains) (-1) 131072 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t18 : RBox := {lo := -68118151487131175952, hi := 68118151487131175952}
lemma t18_contains : t18.Contains (sourcePower true 4 (-1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 4 (-1/2) 2 18 coarse_4_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -9146114894009762331, hi := 9146114894009762331}
lemma t19_contains : t19.Contains (sourcePower true 4 (-1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 4 (-1/2) 2 19 coarse_4_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -1196152349953484451, hi := 1196152349953484451}
lemma t20_contains : t20.Contains (sourcePower true 4 (-1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 4 (-1/2) 2 20 coarse_4_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -152672607307377610, hi := 152672607307377610}
lemma t21_contains : t21.Contains (sourcePower true 4 (-1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 4 (-1/2) 2 21 coarse_4_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -19048215288304101, hi := 19048215288304101}
lemma t22_contains : t22.Contains (sourcePower true 4 (-1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 4 (-1/2) 2 22 coarse_4_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -2325991182024511, hi := 2325991182024511}
lemma t23_contains : t23.Contains (sourcePower true 4 (-1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 4 (-1/2) 2 23 coarse_4_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -278240944058669, hi := 278240944058669}
lemma t24_contains : t24.Contains (sourcePower true 4 (-1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 4 (-1/2) 2 24 coarse_4_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -32625886368317, hi := 32625886368317}
lemma t25_contains : t25.Contains (sourcePower true 4 (-1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 4 (-1/2) 2 25 coarse_4_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -3751380654625, hi := 3751380654625}
lemma t26_contains : t26.Contains (sourcePower true 4 (-1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 4 (-1/2) 2 26 coarse_4_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -423039539925, hi := 423039539925}
lemma t27_contains : t27.Contains (sourcePower true 4 (-1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 4 (-1/2) 2 27 coarse_4_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -46789262002, hi := 46789262002}
lemma t28_contains : t28.Contains (sourcePower true 4 (-1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 4 (-1/2) 2 28 coarse_4_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 4 (-1/2) 2 r.val) := by
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
lemma bound0 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound1 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound2 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound3 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound4 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound5 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound6 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound7 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound8 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound9 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound10 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound11 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound12 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound13 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound14 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound15 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound16 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound17 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound18 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound19 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound20 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound21 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound22 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound23 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound24 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound25 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound26 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound27 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound28 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 1) (v := 50) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound (k : Fin 29) : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (-1/2) 2) k.val := by
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
end SharpPlanar.Bernstein4

end OAI
