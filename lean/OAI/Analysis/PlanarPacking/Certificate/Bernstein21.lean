import OAI.Analysis.PlanarPacking.Certificate.LowBlock21_0
import OAI.Analysis.PlanarPacking.Certificate.LowBlock21_1
import OAI.Analysis.PlanarPacking.Certificate.LowBlock21_10
import OAI.Analysis.PlanarPacking.Certificate.LowBlock21_11
import OAI.Analysis.PlanarPacking.Certificate.MixedBound21
import OAI.Analysis.PlanarPacking.Certificate.CoarseBound21

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein21
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 430171654644213129444216345717, hi := 430171654644385675173401219515}
lemma t0_checked : ((hm21_0_0_2.realAnswer).add hm21_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 21 (3/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_0_0_2.realContains hm21_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 144713151994636564220186198622, hi := 144713151994836547621761922941}
lemma t1_checked : ((hm21_0_0_3.realAnswer).add hm21_1_1_3.realAnswer).scale (-3) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 21 (3/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_0_0_3.realContains hm21_1_1_3.realContains) (-3) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -626788252601725972036647168129, hi := -626788252601549693503614460532}
lemma t2_checked : ((hm21_0_0_4.realAnswer).add hm21_1_1_4.realAnswer).scale (-9) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 21 (3/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_0_0_4.realContains hm21_1_1_4.realContains) (-9) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -138581553449385425235477534260, hi := -138581553449260366245549865884}
lemma t3_checked : ((hm21_0_0_5.realAnswer).add hm21_1_1_5.realAnswer).scale (-27) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 21 (3/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_0_0_5.realContains hm21_1_1_5.realContains) (-27) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 392038710732411125775427819029, hi := 392038710732485305251299013488}
lemma t4_checked : ((hm21_0_0_6.realAnswer).add hm21_1_1_6.realAnswer).scale (-81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 21 (3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_0_0_6.realContains hm21_1_1_6.realContains) (-81) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 52566218610067641686413249387, hi := 52566218610105444927006290968}
lemma t5_checked : ((hm21_0_0_7.realAnswer).add hm21_1_1_7.realAnswer).scale (-243) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 21 (3/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_0_0_7.realContains hm21_1_1_7.realContains) (-243) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -138349320301764257363240820348, hi := -138349320301747366180608240406}
lemma t6_checked : ((hm21_0_0_8.realAnswer).add hm21_1_1_8.realAnswer).scale (-729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 21 (3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_0_0_8.realContains hm21_1_1_8.realContains) (-729) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -11182786194636026175789065420, hi := -11182786194629304732810142546}
lemma t7_checked : ((hm21_0_0_9.realAnswer).add hm21_1_1_9.realAnswer).scale (-2187) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 21 (3/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_0_0_9.realContains hm21_1_1_9.realContains) (-2187) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 31615755973534949301186928047, hi := 31615755973537360933507239777}
lemma t8_checked : ((hm21_0_0_10.realAnswer).add hm21_1_1_10.realAnswer).scale (-6561) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 21 (3/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_0_0_10.realContains hm21_1_1_10.realContains) (-6561) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := 1514999433976339067254918735, hi := 1514999433977127136680470446}
lemma t9_checked : ((hm21_0_0_11.realAnswer).add hm21_1_1_11.realAnswer).scale (-19683) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 21 (3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_0_0_11.realContains hm21_1_1_11.realContains) (-19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -371133651526043528725074012, hi := 371133651526043528725074012}
lemma tr10_contains : tr10.Contains (fullMoment true true 21 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 12 21 mixed_21_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -26063889024553967598026327108, hi := 16738984000761394528842340517}
lemma t10_checked : ((hm21_0_0_12.realAnswer).add tr10).scale (-59049) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 21 (3/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_0_0_12.realContains tr10_contains) (-59049) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -118092620930630225462300918, hi := 118092620930630225462300918}
lemma tr11_contains : tr11.Contains (fullMoment true true 21 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 13 21 mixed_21_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := -10334915409011369615460661094, hi := 10094531387862087184931194888}
lemma t11_checked : ((hm21_0_0_13.realAnswer).add tr11).scale (-177147) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 21 (3/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_0_0_13.realContains tr11_contains) (-177147) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -51162317996940730898206516312, hi := 51162317996940730898206516312}
lemma t12_contains : t12.Contains (sourcePower false 21 (3/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (3/2) 2 12 coarse_21_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -16073196934339071663200440071, hi := 16073196934339071663200440071}
lemma t13_contains : t13.Contains (sourcePower false 21 (3/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (3/2) 2 13 coarse_21_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -4801042232493527104590166183, hi := 4801042232493527104590166183}
lemma t14_contains : t14.Contains (sourcePower false 21 (3/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (3/2) 2 14 coarse_21_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -1370423344206941770097461362, hi := 1370423344206941770097461362}
lemma t15_contains : t15.Contains (sourcePower false 21 (3/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (3/2) 2 15 coarse_21_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -375651332374229463579451301, hi := 375651332374229463579451301}
lemma t16_contains : t16.Contains (sourcePower false 21 (3/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (3/2) 2 16 coarse_21_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -99341861518469404294500801, hi := 99341861518469404294500801}
lemma t17_contains : t17.Contains (sourcePower false 21 (3/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (3/2) 2 17 coarse_21_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -25451841483023795969396598, hi := 25451841483023795969396598}
lemma t18_contains : t18.Contains (sourcePower false 21 (3/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (3/2) 2 18 coarse_21_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -6340229876241134019004759, hi := 6340229876241134019004759}
lemma t19_contains : t19.Contains (sourcePower false 21 (3/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (3/2) 2 19 coarse_21_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -1539969542447927337362309, hi := 1539969542447927337362309}
lemma t20_contains : t20.Contains (sourcePower false 21 (3/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (3/2) 2 20 coarse_21_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -365409763453884912068065, hi := 365409763453884912068065}
lemma t21_contains : t21.Contains (sourcePower false 21 (3/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (3/2) 2 21 coarse_21_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -84793777425826568097104, hi := 84793777425826568097104}
lemma t22_contains : t22.Contains (sourcePower false 21 (3/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (3/2) 2 22 coarse_21_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -19247738723856548849879, hi := 19247738723856548849879}
lemma t23_contains : t23.Contains (sourcePower false 21 (3/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (3/2) 2 23 coarse_21_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -4272541658258472116877, hi := 4272541658258472116877}
lemma t24_contains : t24.Contains (sourcePower false 21 (3/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (3/2) 2 24 coarse_21_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -926793089502574754670, hi := 926793089502574754670}
lemma t25_contains : t25.Contains (sourcePower false 21 (3/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (3/2) 2 25 coarse_21_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -196290930856939223080, hi := 196290930856939223080}
lemma t26_contains : t26.Contains (sourcePower false 21 (3/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (3/2) 2 26 coarse_21_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -40557817829263615547, hi := 40557817829263615547}
lemma t27_contains : t27.Contains (sourcePower false 21 (3/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (3/2) 2 27 coarse_21_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -8169491131565603124, hi := 8169491131565603124}
lemma t28_contains : t28.Contains (sourcePower false 21 (3/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (3/2) 2 28 coarse_21_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 21 (3/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 414179948148527064521911957537, hi := 414179948148668674334322134540}
lemma t0_checked : ((hm21_1_0_2.realAnswer).add hm21_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 21 (3/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_1_0_2.realContains hm21_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 146419130032788328238769469414, hi := 146419130032952454330239278980}
lemma t1_checked : ((hm21_1_0_3.realAnswer).add hm21_0_1_3.realAnswer).scale (3) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 21 (3/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_1_0_3.realContains hm21_0_1_3.realContains) (3) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -601594943171383577704221420370, hi := -601594943171238900925176563480}
lemma t2_checked : ((hm21_1_0_4.realAnswer).add hm21_0_1_4.realAnswer).scale (9) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 21 (3/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_1_0_4.realContains hm21_0_1_4.realContains) (9) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -143910907196715460737904317786, hi := -143910907196612816250310010827}
lemma t3_checked : ((hm21_1_0_5.realAnswer).add hm21_0_1_5.realAnswer).scale (27) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 21 (3/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_1_0_5.realContains hm21_0_1_5.realContains) (27) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 375909965297851310269174392328, hi := 375909965297912197540545613024}
lemma t4_checked : ((hm21_1_0_6.realAnswer).add hm21_0_1_6.realAnswer).scale (81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 21 (3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_1_0_6.realContains hm21_0_1_6.realContains) (81) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 57214968475016064557066727826, hi := 57214968475047095376848915822}
lemma t5_checked : ((hm21_1_0_7.realAnswer).add hm21_0_1_7.realAnswer).scale (243) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 21 (3/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_1_0_7.realContains hm21_0_1_7.realContains) (243) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -132804853513438302353063095082, hi := -132804853513424436541098221230}
lemma t6_checked : ((hm21_1_0_8.realAnswer).add hm21_0_1_8.realAnswer).scale (729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 21 (3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_1_0_8.realContains hm21_0_1_8.realContains) (729) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -13095624130129339578994148388, hi := -13095624130123821741441594358}
lemma t7_checked : ((hm21_1_0_9.realAnswer).add hm21_0_1_9.realAnswer).scale (2187) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 21 (3/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_1_0_9.realContains hm21_0_1_9.realContains) (2187) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 30423850556686034879047024055, hi := 30423850556688014765140824165}
lemma t8_checked : ((hm21_1_0_10.realAnswer).add hm21_0_1_10.realAnswer).scale (6561) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 21 (3/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_1_0_10.realContains hm21_0_1_10.realContains) (6561) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := 1987102568526522326247618241, hi := 1987102568527169350064202610}
lemma t9_checked : ((hm21_1_0_11.realAnswer).add hm21_0_1_11.realAnswer).scale (19683) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 21 (3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_1_0_11.realContains hm21_0_1_11.realContains) (19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -371133651526043528725074012, hi := 371133651526043528725074012}
lemma tr10_contains : tr10.Contains (fullMoment false true 21 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 12 21 mixed_21_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -25897090971808994131515506437, hi := 16905782053506325654008060165}
lemma t10_checked : ((hm21_1_0_12.realAnswer).add tr10).scale (59049) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 21 (3/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_1_0_12.realContains tr10_contains) (59049) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -118092620930630225462300918, hi := 118092620930630225462300918}
lemma tr11_contains : tr11.Contains (fullMoment false true 21 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 13 21 mixed_21_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := -10394135058019566630244128111, hi := 10035311738853878421022840857}
lemma t11_checked : ((hm21_1_0_13.realAnswer).add tr11).scale (177147) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 21 (3/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_1_0_13.realContains tr11_contains) (177147) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -51162317996940730898206516312, hi := 51162317996940730898206516312}
lemma t12_contains : t12.Contains (sourcePower true 21 (3/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (3/2) 2 12 coarse_21_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -16073196934339071663200440071, hi := 16073196934339071663200440071}
lemma t13_contains : t13.Contains (sourcePower true 21 (3/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (3/2) 2 13 coarse_21_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -4801042232493527104590166183, hi := 4801042232493527104590166183}
lemma t14_contains : t14.Contains (sourcePower true 21 (3/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (3/2) 2 14 coarse_21_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -1370423344206941770097461362, hi := 1370423344206941770097461362}
lemma t15_contains : t15.Contains (sourcePower true 21 (3/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (3/2) 2 15 coarse_21_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -375651332374229463579451301, hi := 375651332374229463579451301}
lemma t16_contains : t16.Contains (sourcePower true 21 (3/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (3/2) 2 16 coarse_21_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -99341861518469404294500801, hi := 99341861518469404294500801}
lemma t17_contains : t17.Contains (sourcePower true 21 (3/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (3/2) 2 17 coarse_21_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -25451841483023795969396598, hi := 25451841483023795969396598}
lemma t18_contains : t18.Contains (sourcePower true 21 (3/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (3/2) 2 18 coarse_21_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -6340229876241134019004759, hi := 6340229876241134019004759}
lemma t19_contains : t19.Contains (sourcePower true 21 (3/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (3/2) 2 19 coarse_21_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -1539969542447927337362309, hi := 1539969542447927337362309}
lemma t20_contains : t20.Contains (sourcePower true 21 (3/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (3/2) 2 20 coarse_21_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -365409763453884912068065, hi := 365409763453884912068065}
lemma t21_contains : t21.Contains (sourcePower true 21 (3/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (3/2) 2 21 coarse_21_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -84793777425826568097104, hi := 84793777425826568097104}
lemma t22_contains : t22.Contains (sourcePower true 21 (3/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (3/2) 2 22 coarse_21_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -19247738723856548849879, hi := 19247738723856548849879}
lemma t23_contains : t23.Contains (sourcePower true 21 (3/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (3/2) 2 23 coarse_21_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -4272541658258472116877, hi := 4272541658258472116877}
lemma t24_contains : t24.Contains (sourcePower true 21 (3/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (3/2) 2 24 coarse_21_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -926793089502574754670, hi := 926793089502574754670}
lemma t25_contains : t25.Contains (sourcePower true 21 (3/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (3/2) 2 25 coarse_21_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -196290930856939223080, hi := 196290930856939223080}
lemma t26_contains : t26.Contains (sourcePower true 21 (3/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (3/2) 2 26 coarse_21_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -40557817829263615547, hi := 40557817829263615547}
lemma t27_contains : t27.Contains (sourcePower true 21 (3/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (3/2) 2 27 coarse_21_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -8169491131565603124, hi := 8169491131565603124}
lemma t28_contains : t28.Contains (sourcePower true 21 (3/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (3/2) 2 28 coarse_21_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 21 (3/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (3/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 430171654644213129444216345717, hi := 430171654644385675173401219515}
lemma t0_checked : ((hm21_0_0_2.realAnswer).add hm21_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 21 (-1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_0_0_2.realContains hm21_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -96475434663224365081174615294, hi := -96475434663091042813457465748}
lemma t1_checked : ((hm21_0_0_3.realAnswer).add hm21_1_1_3.realAnswer).scale (1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 21 (-1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_0_0_3.realContains hm21_1_1_3.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -278572556711878209794065408057, hi := -278572556711799863779384204681}
lemma t2_checked : ((hm21_0_0_4.realAnswer).add hm21_1_1_4.realAnswer).scale (-1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 21 (-1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_0_0_4.realContains hm21_1_1_4.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 41061201022003071480162923225, hi := 41061201022040125995697047188}
lemma t3_checked : ((hm21_0_0_5.realAnswer).add hm21_1_1_5.realAnswer).scale (1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 21 (-1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_0_0_5.realContains hm21_1_1_5.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 77439745329858987807491914870, hi := 77439745329873640543466471800}
lemma t4_checked : ((hm21_0_0_6.realAnswer).add hm21_1_1_6.realAnswer).scale (-1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 21 (-1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_0_0_6.realContains hm21_1_1_6.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -6922300393100305504790951897, hi := -6922300393095327300268411442}
lemma t5_checked : ((hm21_0_0_7.realAnswer).add hm21_1_1_7.realAnswer).scale (1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 21 (-1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_0_0_7.realContains hm21_1_1_7.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -12145893689043775680723473940, hi := -12145893689042292778544482011}
lemma t6_checked : ((hm21_0_0_8.realAnswer).add hm21_1_1_8.realAnswer).scale (-1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 21 (-1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_0_0_8.realContains hm21_1_1_8.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 654502347010768635482258000, hi := 654502347011162025834933870}
lemma t7_checked : ((hm21_0_0_9.realAnswer).add hm21_1_1_9.realAnswer).scale (1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 21 (-1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_0_0_9.realContains hm21_1_1_9.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 1233597550560119954443507633, hi := 1233597550560214052580072151}
lemma t8_checked : ((hm21_0_0_10.realAnswer).add hm21_1_1_10.realAnswer).scale (-1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 21 (-1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_0_0_10.realContains hm21_1_1_10.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := -39408612010175740180887104, hi := -39408612010155240686608667}
lemma t9_checked : ((hm21_0_0_11.realAnswer).add hm21_1_1_11.realAnswer).scale (1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 21 (-1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_0_0_11.realContains hm21_1_1_11.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -371133651526043528725074012, hi := 371133651526043528725074012}
lemma tr10_contains : tr10.Contains (fullMoment true true 21 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 12 21 mixed_21_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -451987711242243946897982336, hi := 290279591809847211596039843}
lemma t10_checked : ((hm21_0_0_12.realAnswer).add tr10).scale (-1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 21 (-1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_0_0_12.realContains tr10_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -118092620930630225462300918, hi := 118092620930630225462300918}
lemma tr11_contains : tr11.Contains (fullMoment true true 21 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap true 13 21 mixed_21_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := -116703078699281131234167596, hi := 119482163161980078536263295}
lemma t11_checked : ((hm21_0_0_13.realAnswer).add tr11).scale (1) 1=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 21 (-1/1) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_0_0_13.realContains tr11_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -394325719158795113209281728, hi := 394325719158795113209281728}
lemma t12_contains : t12.Contains (sourcePower false 21 (-1/1) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (-1/1) 2 12 coarse_21_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -82587800142195574588673691, hi := 82587800142195574588673691}
lemma t13_contains : t13.Contains (sourcePower false 21 (-1/1) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (-1/1) 2 13 coarse_21_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -16445909630017244117953782, hi := 16445909630017244117953782}
lemma t14_contains : t14.Contains (sourcePower false 21 (-1/1) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (-1/1) 2 14 coarse_21_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -3129578590409225449893404, hi := 3129578590409225449893404}
lemma t15_contains : t15.Contains (sourcePower false 21 (-1/1) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (-1/1) 2 15 coarse_21_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -571906178834794457983058, hi := 571906178834794457983058}
lemma t16_contains : t16.Contains (sourcePower false 21 (-1/1) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (-1/1) 2 16 coarse_21_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -100827938965423342075918, hi := 100827938965423342075918}
lemma t17_contains : t17.Contains (sourcePower false 21 (-1/1) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (-1/1) 2 17 coarse_21_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -17221720903165216877834, hi := 17221720903165216877834}
lemma t18_contains : t18.Contains (sourcePower false 21 (-1/1) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (-1/1) 2 18 coarse_21_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -2860033250465415001628, hi := 2860033250465415001628}
lemma t19_contains : t19.Contains (sourcePower false 21 (-1/1) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (-1/1) 2 19 coarse_21_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -463112976666628679145, hi := 463112976666628679145}
lemma t20_contains : t20.Contains (sourcePower false 21 (-1/1) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (-1/1) 2 20 coarse_21_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -73259458966171742099, hi := 73259458966171742099}
lemma t21_contains : t21.Contains (sourcePower false 21 (-1/1) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (-1/1) 2 21 coarse_21_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -11333297353995478269, hi := 11333297353995478269}
lemma t22_contains : t22.Contains (sourcePower false 21 (-1/1) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (-1/1) 2 22 coarse_21_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -1715065680303394038, hi := 1715065680303394038}
lemma t23_contains : t23.Contains (sourcePower false 21 (-1/1) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (-1/1) 2 23 coarse_21_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -253802612725042730, hi := 253802612725042730}
lemma t24_contains : t24.Contains (sourcePower false 21 (-1/1) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (-1/1) 2 24 coarse_21_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -36702978599261021, hi := 36702978599261021}
lemma t25_contains : t25.Contains (sourcePower false 21 (-1/1) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (-1/1) 2 25 coarse_21_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -5182359051567824, hi := 5182359051567824}
lemma t26_contains : t26.Contains (sourcePower false 21 (-1/1) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (-1/1) 2 26 coarse_21_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -713855953241536, hi := 713855953241536}
lemma t27_contains : t27.Contains (sourcePower false 21 (-1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (-1/1) 2 27 coarse_21_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -95860513728366, hi := 95860513728366}
lemma t28_contains : t28.Contains (sourcePower false 21 (-1/1) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 21 (-1/1) 2 28 coarse_21_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 21 (-1/1) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (-1/1) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 414179948148527064521911957537, hi := 414179948148668674334322134540}
lemma t0_checked : ((hm21_1_0_2.realAnswer).add hm21_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 21 (-1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_1_0_2.realContains hm21_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -97612753355301636220159519320, hi := -97612753355192218825846312943}
lemma t1_checked : ((hm21_1_0_3.realAnswer).add hm21_0_1_3.realAnswer).scale (-1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 21 (-1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_1_0_3.realContains hm21_0_1_3.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -267375530298392701201876186831, hi := -267375530298328400411189583769}
lemma t2_checked : ((hm21_1_0_4.realAnswer).add hm21_0_1_4.realAnswer).scale (1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 21 (-1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_1_0_4.realContains hm21_0_1_4.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 42640268798996390000091855060, hi := 42640268799026803181601279344}
lemma t3_checked : ((hm21_1_0_5.realAnswer).add hm21_0_1_5.realAnswer).scale (-1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 21 (-1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_1_0_5.realContains hm21_0_1_5.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 74253820305748406966750497250, hi := 74253820305760434082083084054}
lemma t4_checked : ((hm21_1_0_6.realAnswer).add hm21_0_1_6.realAnswer).scale (1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 21 (-1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_1_0_6.realContains hm21_0_1_6.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -7534481445273691572259939532, hi := -7534481445269605209161050578}
lemma t5_checked : ((hm21_1_0_7.realAnswer).add hm21_0_1_7.realAnswer).scale (-1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 21 (-1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_1_0_7.realContains hm21_0_1_7.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -11659136659615982648279887634, hi := -11659136659614765347915344525}
lemma t6_checked : ((hm21_1_0_8.realAnswer).add hm21_0_1_8.realAnswer).scale (1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 21 (-1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_1_0_8.realContains hm21_0_1_8.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 766456281964265744355063593, hi := 766456281964588690494399174}
lemma t7_checked : ((hm21_1_0_9.realAnswer).add hm21_0_1_9.realAnswer).scale (-1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 21 (-1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_1_0_9.realContains hm21_0_1_9.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 1187091257813081074384398439, hi := 1187091257813158326455730984}
lemma t8_checked : ((hm21_1_0_10.realAnswer).add hm21_0_1_10.realAnswer).scale (1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 21 (-1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_1_0_10.realContains hm21_0_1_10.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := -51689097956912600072797426, hi := -51689097956895769498490095}
lemma t9_checked : ((hm21_1_0_11.realAnswer).add hm21_0_1_11.realAnswer).scale (-1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 21 (-1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_1_0_11.realContains hm21_0_1_11.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr10 : RBox := {lo := -371133651526043528725074012, hi := 371133651526043528725074012}
lemma tr10_contains : tr10.Contains (fullMoment false true 21 12) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 12 21 mixed_21_12) <;> norm_num [tr10,precision]
noncomputable def t10 : RBox := {lo := -449095177820664363336752165, hi := 293172125231426060893567268}
lemma t10_checked : ((hm21_1_0_12.realAnswer).add tr10).scale (1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 21 (-1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_1_0_12.realContains tr10_contains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def tr11 : RBox := {lo := -118092620930630225462300918, hi := 118092620930630225462300918}
lemma tr11_contains : tr11.Contains (fullMoment false true 21 13) := by
  apply RBox.contains_of_abs (fullMoment_transformed_cap false 13 21 mixed_21_13) <;> norm_num [tr11,precision]
noncomputable def t11 : RBox := {lo := -116018439156027158271123858, hi := 120166802705233915667439891}
lemma t11_checked : ((hm21_1_0_13.realAnswer).add tr11).scale (-1) 1=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 21 (-1/1) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm21_1_0_13.realContains tr11_contains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -394325719158795113209281728, hi := 394325719158795113209281728}
lemma t12_contains : t12.Contains (sourcePower true 21 (-1/1) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (-1/1) 2 12 coarse_21_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -82587800142195574588673691, hi := 82587800142195574588673691}
lemma t13_contains : t13.Contains (sourcePower true 21 (-1/1) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (-1/1) 2 13 coarse_21_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -16445909630017244117953782, hi := 16445909630017244117953782}
lemma t14_contains : t14.Contains (sourcePower true 21 (-1/1) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (-1/1) 2 14 coarse_21_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -3129578590409225449893404, hi := 3129578590409225449893404}
lemma t15_contains : t15.Contains (sourcePower true 21 (-1/1) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (-1/1) 2 15 coarse_21_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -571906178834794457983058, hi := 571906178834794457983058}
lemma t16_contains : t16.Contains (sourcePower true 21 (-1/1) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (-1/1) 2 16 coarse_21_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -100827938965423342075918, hi := 100827938965423342075918}
lemma t17_contains : t17.Contains (sourcePower true 21 (-1/1) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (-1/1) 2 17 coarse_21_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -17221720903165216877834, hi := 17221720903165216877834}
lemma t18_contains : t18.Contains (sourcePower true 21 (-1/1) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (-1/1) 2 18 coarse_21_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -2860033250465415001628, hi := 2860033250465415001628}
lemma t19_contains : t19.Contains (sourcePower true 21 (-1/1) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (-1/1) 2 19 coarse_21_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -463112976666628679145, hi := 463112976666628679145}
lemma t20_contains : t20.Contains (sourcePower true 21 (-1/1) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (-1/1) 2 20 coarse_21_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -73259458966171742099, hi := 73259458966171742099}
lemma t21_contains : t21.Contains (sourcePower true 21 (-1/1) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (-1/1) 2 21 coarse_21_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -11333297353995478269, hi := 11333297353995478269}
lemma t22_contains : t22.Contains (sourcePower true 21 (-1/1) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (-1/1) 2 22 coarse_21_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -1715065680303394038, hi := 1715065680303394038}
lemma t23_contains : t23.Contains (sourcePower true 21 (-1/1) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (-1/1) 2 23 coarse_21_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -253802612725042730, hi := 253802612725042730}
lemma t24_contains : t24.Contains (sourcePower true 21 (-1/1) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (-1/1) 2 24 coarse_21_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -36702978599261021, hi := 36702978599261021}
lemma t25_contains : t25.Contains (sourcePower true 21 (-1/1) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (-1/1) 2 25 coarse_21_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -5182359051567824, hi := 5182359051567824}
lemma t26_contains : t26.Contains (sourcePower true 21 (-1/1) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (-1/1) 2 26 coarse_21_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -713855953241536, hi := 713855953241536}
lemma t27_contains : t27.Contains (sourcePower true 21 (-1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (-1/1) 2 27 coarse_21_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -95860513728366, hi := 95860513728366}
lemma t28_contains : t28.Contains (sourcePower true 21 (-1/1) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 21 (-1/1) 2 28 coarse_21_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 21 (-1/1) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 21 (-1/1) 2) k.val := by
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
end SharpPlanar.Bernstein21

end OAI
