import OAI.Analysis.PlanarPacking.Certificate.LowBlock37_0
import OAI.Analysis.PlanarPacking.Certificate.LowBlock37_1
import OAI.Analysis.PlanarPacking.Certificate.LowBlock37_10
import OAI.Analysis.PlanarPacking.Certificate.MixedBound37
import OAI.Analysis.PlanarPacking.Certificate.CoarseBound37

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein37
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 27971407153270454829625746199, hi := 27971407153471271516527398288}
lemma t0_checked : ((hm37_0_0_2.realAnswer).add hm37_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 37 (1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_0_0_2.realContains hm37_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 22975589182996943943718916002, hi := 22975589183150764515492748523}
lemma t1_checked : ((hm37_0_0_3.realAnswer).add hm37_1_1_3.realAnswer).scale (-1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 37 (1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_0_0_3.realContains hm37_1_1_3.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -35799590280912181433032348485, hi := -35799590280822112131043398197}
lemma t2_checked : ((hm37_0_0_4.realAnswer).add hm37_1_1_4.realAnswer).scale (-1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 37 (1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_0_0_4.realContains hm37_1_1_4.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -18659639448003787754966765178, hi := -18659639447961248800729364514}
lemma t3_checked : ((hm37_0_0_5.realAnswer).add hm37_1_1_5.realAnswer).scale (-1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 37 (1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_0_0_5.realContains hm37_1_1_5.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr4 : RBox := {lo := -1452687575038373477846949182, hi := 1452687575038373477846949182}
lemma tr4_contains : tr4.Contains (fullMoment true true 37 6) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 6 37 mixed_37_6) <;> norm_num [tr4,precision]
noncomputable def t4 : RBox := {lo := 18269376187487400116945154208, hi := 21174751337580962213617333480}
lemma t4_checked : ((hm37_0_0_6.realAnswer).add tr4).scale (-1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 37 (1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_0_0_6.realContains tr4_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr5 : RBox := {lo := -852272187863596681075941712, hi := 852272187863596681075941712}
lemma tr5_contains : tr5.Contains (fullMoment true true 37 7) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 7 37 mixed_37_7) <;> norm_num [tr5,precision]
noncomputable def t5 : RBox := {lo := 3160462380914480501602014604, hi := 4865006756647388104406072324}
lemma t5_checked : ((hm37_0_0_7.realAnswer).add tr5).scale (-1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 37 (1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_0_0_7.realContains tr5_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr6 : RBox := {lo := -438025165280374769114116401, hi := 438025165280374769114116401}
lemma tr6_contains : tr6.Contains (fullMoment true true 37 8) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 8 37 mixed_37_8) <;> norm_num [tr6,precision]
noncomputable def t6 : RBox := {lo := -5047888374880759082932230164, hi := -4171838044318306212602573575}
lemma t6_checked : ((hm37_0_0_8.realAnswer).add tr6).scale (-1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 37 (1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_0_0_8.realContains tr6_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr7 : RBox := {lo := -200316477263320258439541379, hi := 200316477263320258439541379}
lemma tr7_contains : tr7.Contains (fullMoment true true 37 9) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 9 37 mixed_37_9) <;> norm_num [tr7,precision]
noncomputable def t7 : RBox := {lo := -623444570877380431393531089, hi := -222811616350287557294804039}
lemma t7_checked : ((hm37_0_0_9.realAnswer).add tr7).scale (-1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 37 (1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_0_0_9.realContains tr7_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -82522924134594386764164681, hi := 82522924134594386764164681}
lemma tr8_contains : tr8.Contains (fullMoment true true 37 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 10 37 mixed_37_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := 514646549230832851099033854, hi := 679692397500129984820338539}
lemma t8_checked : ((hm37_0_0_10.realAnswer).add tr8).scale (-1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 37 (1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_0_0_10.realContains tr8_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -30930815277007553323999573, hi := 30930815277007553323999573}
lemma tr9_contains : tr9.Contains (fullMoment true true 37 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 11 37 mixed_37_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -3884823574057179209898359, hi := 57976806979981576738875190}
lemma t9_checked : ((hm37_0_0_11.realAnswer).add tr9).scale (-1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 37 (1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_0_0_11.realContains tr9_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -10634808089414144644373220, hi := 10634808089414144644373220}
lemma tr10_contains : tr10.Contains (fullMoment true true 37 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 12 37 mixed_37_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -60196468222685075591888461, hi := -38926852043852044570406526}
lemma t10_checked : ((hm37_0_0_12.realAnswer).add tr10).scale (-1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 37 (1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_0_0_12.realContains tr10_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -1666024019441666465554773939, hi := 1666024019441666465554773939}
lemma t11_contains : t11.Contains (sourcePower false 37 (1/1) 2 11) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (1/1) 2 11 coarse_37_13) <;> norm_num [t11,precision]
noncomputable def t12 : RBox := {lo := -360418283188298954644165192, hi := 360418283188298954644165192}
lemma t12_contains : t12.Contains (sourcePower false 37 (1/1) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (1/1) 2 12 coarse_37_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -73230933690684009964846178, hi := 73230933690684009964846178}
lemma t13_contains : t13.Contains (sourcePower false 37 (1/1) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (1/1) 2 13 coarse_37_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -14024613211358169787693858, hi := 14024613211358169787693858}
lemma t14_contains : t14.Contains (sourcePower false 37 (1/1) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (1/1) 2 14 coarse_37_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -2539737320118086768090961, hi := 2539737320118086768090961}
lemma t15_contains : t15.Contains (sourcePower false 37 (1/1) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (1/1) 2 15 coarse_37_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -436172697025750189852343, hi := 436172697025750189852343}
lemma t16_contains : t16.Contains (sourcePower false 37 (1/1) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (1/1) 2 16 coarse_37_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -71231655286935315009798, hi := 71231655286935315009798}
lemma t17_contains : t17.Contains (sourcePower false 37 (1/1) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (1/1) 2 17 coarse_37_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -11089989111095300851251, hi := 11089989111095300851251}
lemma t18_contains : t18.Contains (sourcePower false 37 (1/1) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (1/1) 2 18 coarse_37_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -1649975540272999228512, hi := 1649975540272999228512}
lemma t19_contains : t19.Contains (sourcePower false 37 (1/1) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (1/1) 2 19 coarse_37_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -235137951616111849218, hi := 235137951616111849218}
lemma t20_contains : t20.Contains (sourcePower false 37 (1/1) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (1/1) 2 20 coarse_37_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -32170839535591669585, hi := 32170839535591669585}
lemma t21_contains : t21.Contains (sourcePower false 37 (1/1) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (1/1) 2 21 coarse_37_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -4235420694999396572, hi := 4235420694999396572}
lemma t22_contains : t22.Contains (sourcePower false 37 (1/1) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (1/1) 2 22 coarse_37_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -537835042776084524, hi := 537835042776084524}
lemma t23_contains : t23.Contains (sourcePower false 37 (1/1) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (1/1) 2 23 coarse_37_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -66036844332233099, hi := 66036844332233099}
lemma t24_contains : t24.Contains (sourcePower false 37 (1/1) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (1/1) 2 24 coarse_37_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -7860187966536990, hi := 7860187966536990}
lemma t25_contains : t25.Contains (sourcePower false 37 (1/1) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (1/1) 2 25 coarse_37_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -909457826982059, hi := 909457826982059}
lemma t26_contains : t26.Contains (sourcePower false 37 (1/1) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (1/1) 2 26 coarse_37_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -102588381853087, hi := 102588381853087}
lemma t27_contains : t27.Contains (sourcePower false 37 (1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (1/1) 2 27 coarse_37_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -11316112539702, hi := 11316112539702}
lemma t28_contains : t28.Contains (sourcePower false 37 (1/1) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (1/1) 2 28 coarse_37_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 37 (1/1) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (1/1) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 29784628149639126598629010425, hi := 29784628149790414422864181641}
lemma t0_checked : ((hm37_1_0_2.realAnswer).add hm37_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 37 (1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_1_0_2.realContains hm37_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 24595058952054498126169733592, hi := 24595058952171246082806590974}
lemma t1_checked : ((hm37_1_0_3.realAnswer).add hm37_0_1_3.realAnswer).scale (1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 37 (1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_1_0_3.realContains hm37_0_1_3.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -38015730701079568253815778773, hi := -38015730701011001545589625637}
lemma t2_checked : ((hm37_1_0_4.realAnswer).add hm37_0_1_4.realAnswer).scale (1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 37 (1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_1_0_4.realContains hm37_0_1_4.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -20037806668360467128058372022, hi := -20037806668328044576557493437}
lemma t3_checked : ((hm37_1_0_5.realAnswer).add hm37_0_1_5.realAnswer).scale (1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 37 (1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_1_0_5.realContains hm37_0_1_5.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr4 : RBox := {lo := -1452687575038373477846949182, hi := 1452687575038373477846949182}
lemma tr4_contains : tr4.Contains (fullMoment false true 37 6) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 6 37 mixed_37_6) <;> norm_num [tr4,precision]
noncomputable def t4 : RBox := {lo := 19469678309732272350419470641, hi := 22375053459821840507272858523}
lemma t4_checked : ((hm37_1_0_6.realAnswer).add tr4).scale (1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 37 (1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_1_0_6.realContains tr4_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr5 : RBox := {lo := -852272187863596681075941712, hi := 852272187863596681075941712}
lemma tr5_contains : tr5.Contains (fullMoment false true 37 7) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 7 37 mixed_37_7) <;> norm_num [tr5,precision]
noncomputable def t5 : RBox := {lo := 3503854590694609336441173826, hi := 5208398966426159624884366566}
lemma t5_checked : ((hm37_1_0_7.realAnswer).add tr5).scale (1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 37 (1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_1_0_7.realContains tr5_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr6 : RBox := {lo := -438025165280374769114116401, hi := 438025165280374769114116401}
lemma tr6_contains : tr6.Contains (fullMoment false true 37 8) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 8 37 mixed_37_8) <;> norm_num [tr6,precision]
noncomputable def t6 : RBox := {lo := -5330675210627286263616923280, hi := -4454624880065238364984264351}
lemma t6_checked : ((hm37_1_0_8.realAnswer).add tr6).scale (1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 37 (1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_1_0_8.realContains tr6_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr7 : RBox := {lo := -200316477263320258439541379, hi := 200316477263320258439541379}
lemma tr7_contains : tr7.Contains (fullMoment false true 37 9) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 9 37 mixed_37_9) <;> norm_num [tr7,precision]
noncomputable def t7 : RBox := {lo := -670903149397222094402464126, hi := -270270194870236944429087941}
lemma t7_checked : ((hm37_1_0_9.realAnswer).add tr7).scale (1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 37 (1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_1_0_9.realContains tr7_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -82522924134594386764164681, hi := 82522924134594386764164681}
lemma tr8_contains : tr8.Contains (fullMoment false true 37 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 10 37 mixed_37_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := 551856561295574271735811561, hi := 716902409564845542505892615}
lemma t8_checked : ((hm37_1_0_10.realAnswer).add tr8).scale (1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 37 (1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_1_0_10.realContains tr8_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -30930815277007553323999573, hi := 30930815277007553323999573}
lemma tr9_contains : tr9.Contains (fullMoment false true 37 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 11 37 mixed_37_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := 488579973260598836196892, hi := 62350210527293694204117638}
lemma t9_checked : ((hm37_1_0_11.realAnswer).add tr9).scale (1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 37 (1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_1_0_11.realContains tr9_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -10634808089414144644373220, hi := 10634808089414144644373220}
lemma tr10_contains : tr10.Contains (fullMoment false true 37 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 12 37 mixed_37_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -63337012714785769031102801, hi := -42067396535953876839131941}
lemma t10_checked : ((hm37_1_0_12.realAnswer).add tr10).scale (1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 37 (1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_1_0_12.realContains tr10_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -1666024019441666465554773939, hi := 1666024019441666465554773939}
lemma t11_contains : t11.Contains (sourcePower true 37 (1/1) 2 11) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (1/1) 2 11 coarse_37_13) <;> norm_num [t11,precision]
noncomputable def t12 : RBox := {lo := -360418283188298954644165192, hi := 360418283188298954644165192}
lemma t12_contains : t12.Contains (sourcePower true 37 (1/1) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (1/1) 2 12 coarse_37_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -73230933690684009964846178, hi := 73230933690684009964846178}
lemma t13_contains : t13.Contains (sourcePower true 37 (1/1) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (1/1) 2 13 coarse_37_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -14024613211358169787693858, hi := 14024613211358169787693858}
lemma t14_contains : t14.Contains (sourcePower true 37 (1/1) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (1/1) 2 14 coarse_37_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -2539737320118086768090961, hi := 2539737320118086768090961}
lemma t15_contains : t15.Contains (sourcePower true 37 (1/1) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (1/1) 2 15 coarse_37_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -436172697025750189852343, hi := 436172697025750189852343}
lemma t16_contains : t16.Contains (sourcePower true 37 (1/1) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (1/1) 2 16 coarse_37_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -71231655286935315009798, hi := 71231655286935315009798}
lemma t17_contains : t17.Contains (sourcePower true 37 (1/1) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (1/1) 2 17 coarse_37_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -11089989111095300851251, hi := 11089989111095300851251}
lemma t18_contains : t18.Contains (sourcePower true 37 (1/1) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (1/1) 2 18 coarse_37_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -1649975540272999228512, hi := 1649975540272999228512}
lemma t19_contains : t19.Contains (sourcePower true 37 (1/1) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (1/1) 2 19 coarse_37_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -235137951616111849218, hi := 235137951616111849218}
lemma t20_contains : t20.Contains (sourcePower true 37 (1/1) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (1/1) 2 20 coarse_37_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -32170839535591669585, hi := 32170839535591669585}
lemma t21_contains : t21.Contains (sourcePower true 37 (1/1) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (1/1) 2 21 coarse_37_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -4235420694999396572, hi := 4235420694999396572}
lemma t22_contains : t22.Contains (sourcePower true 37 (1/1) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (1/1) 2 22 coarse_37_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -537835042776084524, hi := 537835042776084524}
lemma t23_contains : t23.Contains (sourcePower true 37 (1/1) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (1/1) 2 23 coarse_37_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -66036844332233099, hi := 66036844332233099}
lemma t24_contains : t24.Contains (sourcePower true 37 (1/1) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (1/1) 2 24 coarse_37_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -7860187966536990, hi := 7860187966536990}
lemma t25_contains : t25.Contains (sourcePower true 37 (1/1) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (1/1) 2 25 coarse_37_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -909457826982059, hi := 909457826982059}
lemma t26_contains : t26.Contains (sourcePower true 37 (1/1) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (1/1) 2 26 coarse_37_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -102588381853087, hi := 102588381853087}
lemma t27_contains : t27.Contains (sourcePower true 37 (1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (1/1) 2 27 coarse_37_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -11316112539702, hi := 11316112539702}
lemma t28_contains : t28.Contains (sourcePower true 37 (1/1) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (1/1) 2 28 coarse_37_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 37 (1/1) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (1/1) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 27971407153270454829625746199, hi := 27971407153471271516527398288}
lemma t0_checked : ((hm37_0_0_2.realAnswer).add hm37_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 37 (-1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_0_0_2.realContains hm37_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -11487794591575382257746374262, hi := -11487794591498471971859458001}
lemma t1_checked : ((hm37_0_0_3.realAnswer).add hm37_1_1_3.realAnswer).scale (1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 37 (-1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_0_0_3.realContains hm37_1_1_3.realContains) (1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -8949897570228045358258087122, hi := -8949897570205528032760849549}
lemma t2_checked : ((hm37_0_0_4.realAnswer).add hm37_1_1_4.realAnswer).scale (-1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 37 (-1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_0_0_4.realContains hm37_1_1_4.realContains) (-1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 2332454930995156100091170564, hi := 2332454931000473469370845648}
lemma t3_checked : ((hm37_0_0_5.realAnswer).add hm37_1_1_5.realAnswer).scale (1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 37 (-1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_0_0_5.realContains hm37_1_1_5.realContains) (1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr4 : RBox := {lo := -1452687575038373477846949182, hi := 1452687575038373477846949182}
lemma tr4_contains : tr4.Contains (fullMoment true true 37 6) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 6 37 mixed_37_6) <;> norm_num [tr4,precision]
noncomputable def t4 : RBox := {lo := 1141836011717962507309072138, hi := 1323421958598810138351083343}
lemma t4_checked : ((hm37_0_0_6.realAnswer).add tr4).scale (-1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 37 (-1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_0_0_6.realContains tr4_contains) (-1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr5 : RBox := {lo := -852272187863596681075941712, hi := 852272187863596681075941712}
lemma tr5_contains : tr5.Contains (fullMoment true true 37 7) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 7 37 mixed_37_7) <;> norm_num [tr5,precision]
noncomputable def t5 : RBox := {lo := -152031461145230878262689761, hi := -98764449403577515675062956}
lemma t5_checked : ((hm37_0_0_7.realAnswer).add tr5).scale (1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 37 (-1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_0_0_7.realContains tr5_contains) (1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr6 : RBox := {lo := -438025165280374769114116401, hi := 438025165280374769114116401}
lemma tr6_contains : tr6.Contains (fullMoment true true 37 8) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 8 37 mixed_37_8) <;> norm_num [tr6,precision]
noncomputable def t6 : RBox := {lo := -78873255857511860670816097, hi := -65184969442473534571915212}
lemma t6_checked : ((hm37_0_0_8.realAnswer).add tr6).scale (-1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 37 (-1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_0_0_8.realContains tr6_contains) (-1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr7 : RBox := {lo := -200316477263320258439541379, hi := 200316477263320258439541379}
lemma tr7_contains : tr7.Contains (fullMoment true true 37 9) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 9 37 mixed_37_9) <;> norm_num [tr7,precision]
noncomputable def t7 : RBox := {lo := 1740715752736621541365656, hi := 4870660709979534620261962}
lemma t7_checked : ((hm37_0_0_9.realAnswer).add tr7).scale (1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 37 (-1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_0_0_9.realContains tr7_contains) (1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -82522924134594386764164681, hi := 82522924134594386764164681}
lemma tr8_contains : tr8.Contains (fullMoment true true 37 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 10 37 mixed_37_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := 2010338082932940824605600, hi := 2655048427734882753204448}
lemma t8_checked : ((hm37_0_0_10.realAnswer).add tr8).scale (-1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 37 (-1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_0_0_10.realContains tr8_contains) (-1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -30930815277007553323999573, hi := 30930815277007553323999573}
lemma tr9_contains : tr9.Contains (fullMoment true true 37 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 11 37 mixed_37_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -113235951132776517068116, hi := 7587546043080428144333}
lemma t9_checked : ((hm37_0_0_11.realAnswer).add tr9).scale (1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 37 (-1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_0_0_11.realContains tr9_contains) (1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -10634808089414144644373220, hi := 10634808089414144644373220}
lemma tr10_contains : tr10.Contains (fullMoment true true 37 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 12 37 mixed_37_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -58785613498715894132704, hi := -38014503949074262275787}
lemma t10_checked : ((hm37_0_0_12.realAnswer).add tr10).scale (-1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 37 (-1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_0_0_12.realContains tr10_contains) (-1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -813488290743001203884167, hi := 813488290743001203884167}
lemma t11_contains : t11.Contains (sourcePower false 37 (-1/2) 2 11) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (-1/2) 2 11 coarse_37_13) <;> norm_num [t11,precision]
noncomputable def t12 : RBox := {lo := -87992744919018299473674, hi := 87992744919018299473674}
lemma t12_contains : t12.Contains (sourcePower false 37 (-1/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (-1/2) 2 12 coarse_37_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -8939322960288575435162, hi := 8939322960288575435162}
lemma t13_contains : t13.Contains (sourcePower false 37 (-1/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (-1/2) 2 13 coarse_37_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -855994458701060167706, hi := 855994458701060167706}
lemma t14_contains : t14.Contains (sourcePower false 37 (-1/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (-1/2) 2 14 coarse_37_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -77506632083681847171, hi := 77506632083681847171}
lemma t15_contains : t15.Contains (sourcePower false 37 (-1/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (-1/2) 2 15 coarse_37_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -6655467178737643278, hi := 6655467178737643278}
lemma t16_contains : t16.Contains (sourcePower false 37 (-1/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (-1/2) 2 16 coarse_37_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -543454401298029442, hi := 543454401298029442}
lemma t17_contains : t17.Contains (sourcePower false 37 (-1/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (-1/2) 2 17 coarse_37_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -42304951137906269, hi := 42304951137906269}
lemma t18_contains : t18.Contains (sourcePower false 37 (-1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (-1/2) 2 18 coarse_37_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -3147078590913772, hi := 3147078590913772}
lemma t19_contains : t19.Contains (sourcePower false 37 (-1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (-1/2) 2 19 coarse_37_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -224245025268662, hi := 224245025268662}
lemma t20_contains : t20.Contains (sourcePower false 37 (-1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (-1/2) 2 20 coarse_37_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -15340251701161, hi := 15340251701161}
lemma t21_contains : t21.Contains (sourcePower false 37 (-1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (-1/2) 2 21 coarse_37_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -1009802984000, hi := 1009802984000}
lemma t22_contains : t22.Contains (sourcePower false 37 (-1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (-1/2) 2 22 coarse_37_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -64114933345, hi := 64114933345}
lemma t23_contains : t23.Contains (sourcePower false 37 (-1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (-1/2) 2 23 coarse_37_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -3936102649, hi := 3936102649}
lemma t24_contains : t24.Contains (sourcePower false 37 (-1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (-1/2) 2 24 coarse_37_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -234251856, hi := 234251856}
lemma t25_contains : t25.Contains (sourcePower false 37 (-1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (-1/2) 2 25 coarse_37_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -13551978, hi := 13551978}
lemma t26_contains : t26.Contains (sourcePower false 37 (-1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (-1/2) 2 26 coarse_37_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -764344, hi := 764344}
lemma t27_contains : t27.Contains (sourcePower false 37 (-1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (-1/2) 2 27 coarse_37_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -42156, hi := 42156}
lemma t28_contains : t28.Contains (sourcePower false 37 (-1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 37 (-1/2) 2 28 coarse_37_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 37 (-1/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 29784628149639126598629010425, hi := 29784628149790414422864181641}
lemma t0_checked : ((hm37_1_0_2.realAnswer).add hm37_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 37 (-1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_1_0_2.realContains hm37_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -12297529476085623041403295487, hi := -12297529476027249063084866796}
lemma t1_checked : ((hm37_1_0_3.realAnswer).add hm37_0_1_3.realAnswer).scale (-1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 37 (-1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_1_0_3.realContains hm37_0_1_3.realContains) (-1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -9503932675269892063453944694, hi := -9503932675252750386397406409}
lemma t2_checked : ((hm37_1_0_4.realAnswer).add hm37_0_1_4.realAnswer).scale (1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 37 (-1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_1_0_4.realContains hm37_0_1_4.realContains) (1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 2504725833541005572069686679, hi := 2504725833545058391007296503}
lemma t3_checked : ((hm37_1_0_5.realAnswer).add hm37_0_1_5.realAnswer).scale (-1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 37 (-1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_1_0_5.realContains hm37_0_1_5.realContains) (-1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr4 : RBox := {lo := -1452687575038373477846949182, hi := 1452687575038373477846949182}
lemma tr4_contains : tr4.Contains (fullMoment false true 37 6) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 6 37 mixed_37_6) <;> norm_num [tr4,precision]
noncomputable def t4 : RBox := {lo := 1216854894358267021901216915, hi := 1398440841238865031704553658}
lemma t4_checked : ((hm37_1_0_6.realAnswer).add tr4).scale (1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 37 (-1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_1_0_6.realContains tr4_contains) (1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr5 : RBox := {lo := -852272187863596681075941712, hi := 852272187863596681075941712}
lemma tr5_contains : tr5.Contains (fullMoment false true 37 7) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 7 37 mixed_37_7) <;> norm_num [tr5,precision]
noncomputable def t5 : RBox := {lo := -162762467700817488277636456, hi := -109495455959206541763786682}
lemma t5_checked : ((hm37_1_0_7.realAnswer).add tr5).scale (-1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 37 (-1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_1_0_7.realContains tr5_contains) (-1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr6 : RBox := {lo := -438025165280374769114116401, hi := 438025165280374769114116401}
lemma tr6_contains : tr6.Contains (fullMoment false true 37 8) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 8 37 mixed_37_8) <;> norm_num [tr6,precision]
noncomputable def t6 : RBox := {lo := -83291800166051347869014427, hi := -69603513751019349452879130}
lemma t6_checked : ((hm37_1_0_8.realAnswer).add tr6).scale (1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 37 (-1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_1_0_8.realContains tr6_contains) (1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr7 : RBox := {lo := -200316477263320258439541379, hi := 200316477263320258439541379}
lemma tr7_contains : tr7.Contains (fullMoment false true 37 9) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 9 37 mixed_37_9) <;> norm_num [tr7,precision]
noncomputable def t7 : RBox := {lo := 2111485897423726128352249, hi := 5241430854665797612519251}
lemma t7_checked : ((hm37_1_0_9.realAnswer).add tr7).scale (-1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 37 (-1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_1_0_9.realContains tr7_contains) (-1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr8 : RBox := {lo := -82522924134594386764164681, hi := 82522924134594386764164681}
lemma tr8_contains : tr8.Contains (fullMoment false true 37 10) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 10 37 mixed_37_10) <;> norm_num [tr8,precision]
noncomputable def t8 : RBox := {lo := 2155689692560836998968013, hi := 2800400037362677900413644}
lemma t8_checked : ((hm37_1_0_10.realAnswer).add tr8).scale (1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 37 (-1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_1_0_10.realContains tr8_contains) (1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr9 : RBox := {lo := -30930815277007553323999573, hi := 30930815277007553323999573}
lemma tr9_contains : tr9.Contains (fullMoment false true 37 11) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 11 37 mixed_37_11) <;> norm_num [tr9,precision]
noncomputable def t9 : RBox := {lo := -121777754936120496492418, hi := -954257760274607101947}
lemma t9_checked : ((hm37_1_0_11.realAnswer).add tr9).scale (-1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 37 (-1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_1_0_11.realContains tr9_contains) (-1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -10634808089414144644373220, hi := 10634808089414144644373220}
lemma tr10_contains : tr10.Contains (fullMoment false true 37 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 12 37 mixed_37_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -61852551479282977569437, hi := -41081441929642457850714}
lemma t10_checked : ((hm37_1_0_12.realAnswer).add tr10).scale (1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 37 (-1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_1_0_12.realContains tr10_contains) (1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -813488290743001203884167, hi := 813488290743001203884167}
lemma t11_contains : t11.Contains (sourcePower true 37 (-1/2) 2 11) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (-1/2) 2 11 coarse_37_13) <;> norm_num [t11,precision]
noncomputable def t12 : RBox := {lo := -87992744919018299473674, hi := 87992744919018299473674}
lemma t12_contains : t12.Contains (sourcePower true 37 (-1/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (-1/2) 2 12 coarse_37_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -8939322960288575435162, hi := 8939322960288575435162}
lemma t13_contains : t13.Contains (sourcePower true 37 (-1/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (-1/2) 2 13 coarse_37_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -855994458701060167706, hi := 855994458701060167706}
lemma t14_contains : t14.Contains (sourcePower true 37 (-1/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (-1/2) 2 14 coarse_37_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -77506632083681847171, hi := 77506632083681847171}
lemma t15_contains : t15.Contains (sourcePower true 37 (-1/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (-1/2) 2 15 coarse_37_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -6655467178737643278, hi := 6655467178737643278}
lemma t16_contains : t16.Contains (sourcePower true 37 (-1/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (-1/2) 2 16 coarse_37_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -543454401298029442, hi := 543454401298029442}
lemma t17_contains : t17.Contains (sourcePower true 37 (-1/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (-1/2) 2 17 coarse_37_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -42304951137906269, hi := 42304951137906269}
lemma t18_contains : t18.Contains (sourcePower true 37 (-1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (-1/2) 2 18 coarse_37_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -3147078590913772, hi := 3147078590913772}
lemma t19_contains : t19.Contains (sourcePower true 37 (-1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (-1/2) 2 19 coarse_37_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -224245025268662, hi := 224245025268662}
lemma t20_contains : t20.Contains (sourcePower true 37 (-1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (-1/2) 2 20 coarse_37_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -15340251701161, hi := 15340251701161}
lemma t21_contains : t21.Contains (sourcePower true 37 (-1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (-1/2) 2 21 coarse_37_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -1009802984000, hi := 1009802984000}
lemma t22_contains : t22.Contains (sourcePower true 37 (-1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (-1/2) 2 22 coarse_37_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -64114933345, hi := 64114933345}
lemma t23_contains : t23.Contains (sourcePower true 37 (-1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (-1/2) 2 23 coarse_37_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -3936102649, hi := 3936102649}
lemma t24_contains : t24.Contains (sourcePower true 37 (-1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (-1/2) 2 24 coarse_37_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -234251856, hi := 234251856}
lemma t25_contains : t25.Contains (sourcePower true 37 (-1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (-1/2) 2 25 coarse_37_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -13551978, hi := 13551978}
lemma t26_contains : t26.Contains (sourcePower true 37 (-1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (-1/2) 2 26 coarse_37_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -764344, hi := 764344}
lemma t27_contains : t27.Contains (sourcePower true 37 (-1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (-1/2) 2 27 coarse_37_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -42156, hi := 42156}
lemma t28_contains : t28.Contains (sourcePower true 37 (-1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 37 (-1/2) 2 28 coarse_37_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 37 (-1/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 37 (-1/2) 2) k.val := by
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
end SharpPlanar.Bernstein37

end OAI
