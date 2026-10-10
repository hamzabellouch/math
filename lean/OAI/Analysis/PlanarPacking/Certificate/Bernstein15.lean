import OAI.Analysis.PlanarPacking.Certificate.LowBlock15_0
import OAI.Analysis.PlanarPacking.Certificate.LowBlock15_1
import OAI.Analysis.PlanarPacking.Certificate.LowBlock15_10
import OAI.Analysis.PlanarPacking.Certificate.LowBlock15_11
import OAI.Analysis.PlanarPacking.Certificate.CoarseBound15

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein15
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 27159338010067260923830593872, hi := 27159338010239649859273041516}
lemma t0_checked : ((hm15_0_0_2.realAnswer).add hm15_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 15 (1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_0_0_2.realContains hm15_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -11320484761419235950371594400, hi := -11320484761352631784562848693}
lemma t1_checked : ((hm15_0_0_3.realAnswer).add hm15_1_1_3.realAnswer).scale (-1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 15 (1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_0_0_3.realContains hm15_1_1_3.realContains) (-1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -8502230164594066963161227126, hi := -8502230164574496715233605314}
lemma t2_checked : ((hm15_0_0_4.realAnswer).add hm15_1_1_4.realAnswer).scale (-1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 15 (1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_0_0_4.realContains hm15_1_1_4.realContains) (-1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 2261629607214195482483685067, hi := 2261629607218823517815143127}
lemma t3_checked : ((hm15_0_0_5.realAnswer).add hm15_1_1_5.realAnswer).scale (-1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 15 (1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_0_0_5.realContains hm15_1_1_5.realContains) (-1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 1152051916524554219581319778, hi := 1152051916525469280518389969}
lemma t4_checked : ((hm15_0_0_6.realAnswer).add hm15_1_1_6.realAnswer).scale (-1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 15 (1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_0_0_6.realContains hm15_1_1_6.realContains) (-1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -115425337124907146133229224, hi := -115425337124751698907305844}
lemma t5_checked : ((hm15_0_0_7.realAnswer).add hm15_1_1_7.realAnswer).scale (-1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 15 (1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_0_0_7.realContains hm15_1_1_7.realContains) (-1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -64675426596631346531142138, hi := -64675426596608193414916868}
lemma t6_checked : ((hm15_0_0_8.realAnswer).add hm15_1_1_8.realAnswer).scale (-1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 15 (1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_0_0_8.realContains hm15_1_1_8.realContains) (-1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 2693565504955469538077893, hi := 2693565504958540840601594}
lemma t7_checked : ((hm15_0_0_9.realAnswer).add hm15_1_1_9.realAnswer).scale (-1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 15 (1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_0_0_9.realContains hm15_1_1_9.realContains) (-1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 1966666077138055488418528, hi := 1966666077138422863829891}
lemma t8_checked : ((hm15_0_0_10.realAnswer).add hm15_1_1_10.realAnswer).scale (-1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 15 (1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_0_0_10.realContains hm15_1_1_10.realContains) (-1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := -27993446524694652017937, hi := -27993446524654624976840}
lemma t9_checked : ((hm15_0_0_11.realAnswer).add hm15_1_1_11.realAnswer).scale (-1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 15 (1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_0_0_11.realContains hm15_1_1_11.realContains) (-1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -37120064623356127749744, hi := -37120064623352121715786}
lemma t10_checked : ((hm15_0_0_12.realAnswer).add hm15_1_1_12.realAnswer).scale (-1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 15 (1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_0_0_12.realContains hm15_1_1_12.realContains) (-1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -1061230630839543253842157, hi := 1061230630839543253842157}
lemma t11_contains : t11.Contains (sourcePower false 15 (1/2) 2 11) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (1/2) 2 11 coarse_15_13) <;> norm_num [t11,precision]
noncomputable def t12 : RBox := {lo := -124676864188939402959787, hi := 124676864188939402959787}
lemma t12_contains : t12.Contains (sourcePower false 15 (1/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (1/2) 2 12 coarse_15_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -14011371607662972651343, hi := 14011371607662972651343}
lemma t13_contains : t13.Contains (sourcePower false 15 (1/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (1/2) 2 13 coarse_15_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -1513738773311503444352, hi := 1513738773311503444352}
lemma t14_contains : t14.Contains (sourcePower false 15 (1/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (1/2) 2 14 coarse_15_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -157824026550899286770, hi := 157824026550899286770}
lemma t15_contains : t15.Contains (sourcePower false 15 (1/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (1/2) 2 15 coarse_15_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -15922942750219540366, hi := 15922942750219540366}
lemma t16_contains : t16.Contains (sourcePower false 15 (1/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (1/2) 2 16 coarse_15_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -1557074307019053506, hi := 1557074307019053506}
lemma t17_contains : t17.Contains (sourcePower false 15 (1/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (1/2) 2 17 coarse_15_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -147690407521422312, hi := 147690407521422312}
lemma t18_contains : t18.Contains (sourcePower false 15 (1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (1/2) 2 18 coarse_15_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -13589382730293059, hi := 13589382730293059}
lemma t19_contains : t19.Contains (sourcePower false 15 (1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (1/2) 2 19 coarse_15_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -1212674233406933, hi := 1212674233406933}
lemma t20_contains : t20.Contains (sourcePower false 15 (1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (1/2) 2 20 coarse_15_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -104912039047631, hi := 104912039047631}
lemma t21_contains : t21.Contains (sourcePower false 15 (1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (1/2) 2 21 coarse_15_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -8796397165936, hi := 8796397165936}
lemma t22_contains : t22.Contains (sourcePower false 15 (1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (1/2) 2 22 coarse_15_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -714679113149, hi := 714679113149}
lemma t23_contains : t23.Contains (sourcePower false 15 (1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (1/2) 2 23 coarse_15_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -56267812699, hi := 56267812699}
lemma t24_contains : t24.Contains (sourcePower false 15 (1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (1/2) 2 24 coarse_15_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -4293965936, hi := 4293965936}
lemma t25_contains : t25.Contains (sourcePower false 15 (1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (1/2) 2 25 coarse_15_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -317759162, hi := 317759162}
lemma t26_contains : t26.Contains (sourcePower false 15 (1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (1/2) 2 26 coarse_15_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -22816166, hi := 22816166}
lemma t27_contains : t27.Contains (sourcePower false 15 (1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (1/2) 2 27 coarse_15_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -1590803, hi := 1590803}
lemma t28_contains : t28.Contains (sourcePower false 15 (1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (1/2) 2 28 coarse_15_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 15 (1/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (1/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 24406391988011399658015545144, hi := 24406391988152941714119318691}
lemma t0_checked : ((hm15_1_0_2.realAnswer).add hm15_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 15 (1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_1_0_2.realContains hm15_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -10158364509439971009191968223, hi := -10158364509385287802629848657}
lemma t1_checked : ((hm15_1_0_3.realAnswer).add hm15_0_1_3.realAnswer).scale (1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 15 (1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_1_0_3.realContains hm15_0_1_3.realContains) (1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -7619268723470759017201562337, hi := -7619268723454691155396574669}
lemma t2_checked : ((hm15_1_0_4.realAnswer).add hm15_0_1_4.realAnswer).scale (1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 15 (1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_1_0_4.realContains hm15_0_1_4.realContains) (1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 2015413053875911566127081405, hi := 2015413053879711524816992913}
lemma t3_checked : ((hm15_1_0_5.realAnswer).add hm15_0_1_5.realAnswer).scale (1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 15 (1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_1_0_5.realContains hm15_0_1_5.realContains) (1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 1028212877256464328670694083, hi := 1028212877257215704581882040}
lemma t4_checked : ((hm15_1_0_6.realAnswer).add hm15_0_1_6.realAnswer).scale (1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 15 (1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_1_0_6.realContains hm15_0_1_6.realContains) (1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -100423043534180200372301866, hi := -100423043534052550999890063}
lemma t5_checked : ((hm15_1_0_7.realAnswer).add hm15_0_1_7.realAnswer).scale (1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 15 (1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_1_0_7.realContains hm15_0_1_7.realContains) (1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -57061087266525712112476637, hi := -57061087266506697886050939}
lemma t6_checked : ((hm15_1_0_8.realAnswer).add hm15_0_1_8.realAnswer).scale (1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 15 (1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_1_0_8.realContains hm15_0_1_8.realContains) (1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 2205939157309565632757925, hi := 2205939157312088150031684}
lemma t7_checked : ((hm15_1_0_9.realAnswer).add hm15_0_1_9.realAnswer).scale (1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 15 (1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_1_0_9.realContains hm15_0_1_9.realContains) (1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 1701763119366142804354440, hi := 1701763119366444577258313}
lemma t8_checked : ((hm15_1_0_10.realAnswer).add hm15_0_1_10.realAnswer).scale (1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 15 (1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_1_0_10.realContains hm15_0_1_10.realContains) (1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := -17393617252392906557029, hi := -17393617252360020512583}
lemma t9_checked : ((hm15_1_0_11.realAnswer).add hm15_0_1_11.realAnswer).scale (1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 15 (1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_1_0_11.realContains hm15_0_1_11.realContains) (1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -31120206315854971972018, hi := -31120206315851679538801}
lemma t10_checked : ((hm15_1_0_12.realAnswer).add hm15_0_1_12.realAnswer).scale (1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 15 (1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_1_0_12.realContains hm15_0_1_12.realContains) (1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -1061230630839543253842157, hi := 1061230630839543253842157}
lemma t11_contains : t11.Contains (sourcePower true 15 (1/2) 2 11) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (1/2) 2 11 coarse_15_13) <;> norm_num [t11,precision]
noncomputable def t12 : RBox := {lo := -124676864188939402959787, hi := 124676864188939402959787}
lemma t12_contains : t12.Contains (sourcePower true 15 (1/2) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (1/2) 2 12 coarse_15_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -14011371607662972651343, hi := 14011371607662972651343}
lemma t13_contains : t13.Contains (sourcePower true 15 (1/2) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (1/2) 2 13 coarse_15_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -1513738773311503444352, hi := 1513738773311503444352}
lemma t14_contains : t14.Contains (sourcePower true 15 (1/2) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (1/2) 2 14 coarse_15_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -157824026550899286770, hi := 157824026550899286770}
lemma t15_contains : t15.Contains (sourcePower true 15 (1/2) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (1/2) 2 15 coarse_15_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -15922942750219540366, hi := 15922942750219540366}
lemma t16_contains : t16.Contains (sourcePower true 15 (1/2) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (1/2) 2 16 coarse_15_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -1557074307019053506, hi := 1557074307019053506}
lemma t17_contains : t17.Contains (sourcePower true 15 (1/2) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (1/2) 2 17 coarse_15_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -147690407521422312, hi := 147690407521422312}
lemma t18_contains : t18.Contains (sourcePower true 15 (1/2) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (1/2) 2 18 coarse_15_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -13589382730293059, hi := 13589382730293059}
lemma t19_contains : t19.Contains (sourcePower true 15 (1/2) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (1/2) 2 19 coarse_15_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -1212674233406933, hi := 1212674233406933}
lemma t20_contains : t20.Contains (sourcePower true 15 (1/2) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (1/2) 2 20 coarse_15_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -104912039047631, hi := 104912039047631}
lemma t21_contains : t21.Contains (sourcePower true 15 (1/2) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (1/2) 2 21 coarse_15_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -8796397165936, hi := 8796397165936}
lemma t22_contains : t22.Contains (sourcePower true 15 (1/2) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (1/2) 2 22 coarse_15_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -714679113149, hi := 714679113149}
lemma t23_contains : t23.Contains (sourcePower true 15 (1/2) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (1/2) 2 23 coarse_15_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -56267812699, hi := 56267812699}
lemma t24_contains : t24.Contains (sourcePower true 15 (1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (1/2) 2 24 coarse_15_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -4293965936, hi := 4293965936}
lemma t25_contains : t25.Contains (sourcePower true 15 (1/2) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (1/2) 2 25 coarse_15_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -317759162, hi := 317759162}
lemma t26_contains : t26.Contains (sourcePower true 15 (1/2) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (1/2) 2 26 coarse_15_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -22816166, hi := 22816166}
lemma t27_contains : t27.Contains (sourcePower true 15 (1/2) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (1/2) 2 27 coarse_15_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -1590803, hi := 1590803}
lemma t28_contains : t28.Contains (sourcePower true 15 (1/2) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (1/2) 2 28 coarse_15_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 15 (1/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (1/2) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 27159338010067260923830593872, hi := 27159338010239649859273041516}
lemma t0_checked : ((hm15_0_0_2.realAnswer).add hm15_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 15 (-1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_0_0_2.realContains hm15_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 22640969522705263569125697386, hi := 22640969522838471900743188799}
lemma t1_checked : ((hm15_0_0_3.realAnswer).add hm15_1_1_3.realAnswer).scale (1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 15 (-1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_0_0_3.realContains hm15_1_1_3.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -34008920658376267852644908504, hi := -34008920658297986860934421259}
lemma t2_checked : ((hm15_0_0_4.realAnswer).add hm15_1_1_4.realAnswer).scale (-1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 15 (-1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_0_0_4.realContains hm15_1_1_4.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -18093036857750588142521145009, hi := -18093036857713563859869480536}
lemma t3_checked : ((hm15_0_0_5.realAnswer).add hm15_1_1_5.realAnswer).scale (1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 15 (-1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_0_0_5.realContains hm15_1_1_5.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 18432830664392867513301116460, hi := 18432830664407508488294239502}
lemma t4_checked : ((hm15_0_0_6.realAnswer).add hm15_1_1_6.realAnswer).scale (-1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 15 (-1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_0_0_6.realContains hm15_1_1_6.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 3693610787992054365033787027, hi := 3693610787997028676263335154}
lemma t5_checked : ((hm15_0_0_7.realAnswer).add hm15_1_1_7.realAnswer).scale (1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 15 (-1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_0_0_7.realContains hm15_1_1_7.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -4139227302184406177993096771, hi := -4139227302182924378554679615}
lemma t6_checked : ((hm15_0_0_8.realAnswer).add hm15_1_1_8.realAnswer).scale (-1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 15 (-1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_0_0_8.realContains hm15_1_1_8.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -344776384634693227597004015, hi := -344776384634300100873970316}
lemma t7_checked : ((hm15_0_0_9.realAnswer).add hm15_1_1_9.realAnswer).scale (1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 15 (-1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_0_0_9.realContains hm15_1_1_9.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 503466515747342205035143317, hi := 503466515747436253140452012}
lemma t8_checked : ((hm15_0_0_10.realAnswer).add hm15_1_1_10.realAnswer).scale (-1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 15 (-1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_0_0_10.realContains hm15_1_1_10.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := 14332644620623167988142393, hi := 14332644620643661833183311}
lemma t9_checked : ((hm15_0_0_11.realAnswer).add hm15_1_1_11.realAnswer).scale (1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 15 (-1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_0_0_11.realContains hm15_1_1_11.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -38010946174316674815737136, hi := -38010946174312572636965326}
lemma t10_checked : ((hm15_0_0_12.realAnswer).add hm15_1_1_12.realAnswer).scale (-1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 15 (-1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_0_0_12.realContains hm15_1_1_12.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -2173400331959384583868736519, hi := 2173400331959384583868736519}
lemma t11_contains : t11.Contains (sourcePower false 15 (-1/1) 2 11) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (-1/1) 2 11 coarse_15_13) <;> norm_num [t11,precision]
noncomputable def t12 : RBox := {lo := -510676435717895794523285937, hi := 510676435717895794523285937}
lemma t12_contains : t12.Contains (sourcePower false 15 (-1/1) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (-1/1) 2 12 coarse_15_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -114781156209975071959800993, hi := 114781156209975071959800993}
lemma t13_contains : t13.Contains (sourcePower false 15 (-1/1) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (-1/1) 2 13 coarse_15_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -24801096061935672432257826, hi := 24801096061935672432257826}
lemma t14_contains : t14.Contains (sourcePower false 15 (-1/1) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (-1/1) 2 14 coarse_15_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -5171577702019867828849372, hi := 5171577702019867828849372}
lemma t15_contains : t15.Contains (sourcePower false 15 (-1/1) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (-1/1) 2 15 coarse_15_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -1043525976078387797403047, hi := 1043525976078387797403047}
lemma t16_contains : t16.Contains (sourcePower false 15 (-1/1) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (-1/1) 2 16 coarse_15_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -204088843569601381051700, hi := 204088843569601381051700}
lemma t17_contains : t17.Contains (sourcePower false 15 (-1/1) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (-1/1) 2 17 coarse_15_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -38716154189295730443609, hi := 38716154189295730443609}
lemma t18_contains : t18.Contains (sourcePower false 15 (-1/1) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (-1/1) 2 18 coarse_15_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -7124750292899887013175, hi := 7124750292899887013175}
lemma t19_contains : t19.Contains (sourcePower false 15 (-1/1) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (-1/1) 2 19 coarse_15_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -1271581096968907241704, hi := 1271581096968907241704}
lemma t20_contains : t20.Contains (sourcePower false 15 (-1/1) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (-1/1) 2 20 coarse_15_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -220016492512816141698, hi := 220016492512816141698}
lemma t21_contains : t21.Contains (sourcePower false 15 (-1/1) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (-1/1) 2 21 coarse_15_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -36894763818673297662, hi := 36894763818673297662}
lemma t22_contains : t22.Contains (sourcePower false 15 (-1/1) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (-1/1) 2 22 coarse_15_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -5995162925987219398, hi := 5995162925987219398}
lemma t23_contains : t23.Contains (sourcePower false 15 (-1/1) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (-1/1) 2 23 coarse_15_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -944017247492413777, hi := 944017247492413777}
lemma t24_contains : t24.Contains (sourcePower false 15 (-1/1) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (-1/1) 2 24 coarse_15_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -144081587984564201, hi := 144081587984564201}
lemma t25_contains : t25.Contains (sourcePower false 15 (-1/1) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (-1/1) 2 25 coarse_15_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -21324456348662756, hi := 21324456348662756}
lemma t26_contains : t26.Contains (sourcePower false 15 (-1/1) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (-1/1) 2 26 coarse_15_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -3062333875518606, hi := 3062333875518606}
lemma t27_contains : t27.Contains (sourcePower false 15 (-1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (-1/1) 2 27 coarse_15_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -427027912874177, hi := 427027912874177}
lemma t28_contains : t28.Contains (sourcePower false 15 (-1/1) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap false 15 (-1/1) 2 28 coarse_15_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 15 (-1/1) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 15 (-1/1) 2) k.val := by
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
noncomputable def t0 : RBox := {lo := 24406391988011399658015545144, hi := 24406391988152941714119318691}
lemma t0_checked : ((hm15_1_0_2.realAnswer).add hm15_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 15 (-1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_1_0_2.realContains hm15_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 20316729018770575605259697314, hi := 20316729018879942018383936446}
lemma t1_checked : ((hm15_1_0_3.realAnswer).add hm15_0_1_3.realAnswer).scale (-1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 15 (-1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_1_0_3.realContains hm15_0_1_3.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -30477074893883036068806249346, hi := -30477074893818764621586298679}
lemma t2_checked : ((hm15_1_0_4.realAnswer).add hm15_0_1_4.realAnswer).scale (1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 15 (-1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_1_0_4.realContains hm15_0_1_4.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -16123304431037692198535943297, hi := -16123304431007292529016651241}
lemma t3_checked : ((hm15_1_0_5.realAnswer).add hm15_0_1_5.realAnswer).scale (-1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 15 (-1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_1_0_5.realContains hm15_0_1_5.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 16451406036103429258731105339, hi := 16451406036115451273310112625}
lemma t4_checked : ((hm15_1_0_6.realAnswer).add hm15_0_1_6.realAnswer).scale (1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 15 (-1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_1_0_6.realContains hm15_0_1_6.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 3213537393089681631996482034, hi := 3213537393093766411913659683}
lemma t5_checked : ((hm15_1_0_7.realAnswer).add hm15_0_1_7.realAnswer).scale (-1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 15 (-1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_1_0_7.realContains hm15_0_1_7.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -3651909585057645575198504713, hi := -3651909585056428664707260099}
lemma t6_checked : ((hm15_1_0_8.realAnswer).add hm15_0_1_8.realAnswer).scale (1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 15 (-1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_1_0_8.realContains hm15_0_1_8.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -282360212135947283204055498, hi := -282360212135624400993014522}
lemma t7_checked : ((hm15_1_0_9.realAnswer).add hm15_0_1_9.realAnswer).scale (-1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 15 (-1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_1_0_9.realContains hm15_0_1_9.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 435651358557732557914736809, hi := 435651358557809811778127914}
lemma t8_checked : ((hm15_1_0_10.realAnswer).add hm15_0_1_10.realAnswer).scale (1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 15 (-1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_1_0_10.realContains hm15_0_1_10.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := 8905532033208330502442716, hi := 8905532033225168157198572}
lemma t9_checked : ((hm15_1_0_11.realAnswer).add hm15_0_1_11.realAnswer).scale (-1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 15 (-1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_1_0_11.realContains hm15_0_1_11.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -31867091267435491299346323, hi := -31867091267432119847732998}
lemma t10_checked : ((hm15_1_0_12.realAnswer).add hm15_0_1_12.realAnswer).scale (1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 15 (-1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm15_1_0_12.realContains hm15_0_1_12.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -2173400331959384583868736519, hi := 2173400331959384583868736519}
lemma t11_contains : t11.Contains (sourcePower true 15 (-1/1) 2 11) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (-1/1) 2 11 coarse_15_13) <;> norm_num [t11,precision]
noncomputable def t12 : RBox := {lo := -510676435717895794523285937, hi := 510676435717895794523285937}
lemma t12_contains : t12.Contains (sourcePower true 15 (-1/1) 2 12) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (-1/1) 2 12 coarse_15_14) <;> norm_num [t12,precision]
noncomputable def t13 : RBox := {lo := -114781156209975071959800993, hi := 114781156209975071959800993}
lemma t13_contains : t13.Contains (sourcePower true 15 (-1/1) 2 13) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (-1/1) 2 13 coarse_15_15) <;> norm_num [t13,precision]
noncomputable def t14 : RBox := {lo := -24801096061935672432257826, hi := 24801096061935672432257826}
lemma t14_contains : t14.Contains (sourcePower true 15 (-1/1) 2 14) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (-1/1) 2 14 coarse_15_16) <;> norm_num [t14,precision]
noncomputable def t15 : RBox := {lo := -5171577702019867828849372, hi := 5171577702019867828849372}
lemma t15_contains : t15.Contains (sourcePower true 15 (-1/1) 2 15) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (-1/1) 2 15 coarse_15_17) <;> norm_num [t15,precision]
noncomputable def t16 : RBox := {lo := -1043525976078387797403047, hi := 1043525976078387797403047}
lemma t16_contains : t16.Contains (sourcePower true 15 (-1/1) 2 16) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (-1/1) 2 16 coarse_15_18) <;> norm_num [t16,precision]
noncomputable def t17 : RBox := {lo := -204088843569601381051700, hi := 204088843569601381051700}
lemma t17_contains : t17.Contains (sourcePower true 15 (-1/1) 2 17) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (-1/1) 2 17 coarse_15_19) <;> norm_num [t17,precision]
noncomputable def t18 : RBox := {lo := -38716154189295730443609, hi := 38716154189295730443609}
lemma t18_contains : t18.Contains (sourcePower true 15 (-1/1) 2 18) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (-1/1) 2 18 coarse_15_20) <;> norm_num [t18,precision]
noncomputable def t19 : RBox := {lo := -7124750292899887013175, hi := 7124750292899887013175}
lemma t19_contains : t19.Contains (sourcePower true 15 (-1/1) 2 19) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (-1/1) 2 19 coarse_15_21) <;> norm_num [t19,precision]
noncomputable def t20 : RBox := {lo := -1271581096968907241704, hi := 1271581096968907241704}
lemma t20_contains : t20.Contains (sourcePower true 15 (-1/1) 2 20) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (-1/1) 2 20 coarse_15_22) <;> norm_num [t20,precision]
noncomputable def t21 : RBox := {lo := -220016492512816141698, hi := 220016492512816141698}
lemma t21_contains : t21.Contains (sourcePower true 15 (-1/1) 2 21) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (-1/1) 2 21 coarse_15_23) <;> norm_num [t21,precision]
noncomputable def t22 : RBox := {lo := -36894763818673297662, hi := 36894763818673297662}
lemma t22_contains : t22.Contains (sourcePower true 15 (-1/1) 2 22) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (-1/1) 2 22 coarse_15_24) <;> norm_num [t22,precision]
noncomputable def t23 : RBox := {lo := -5995162925987219398, hi := 5995162925987219398}
lemma t23_contains : t23.Contains (sourcePower true 15 (-1/1) 2 23) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (-1/1) 2 23 coarse_15_25) <;> norm_num [t23,precision]
noncomputable def t24 : RBox := {lo := -944017247492413777, hi := 944017247492413777}
lemma t24_contains : t24.Contains (sourcePower true 15 (-1/1) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (-1/1) 2 24 coarse_15_26) <;> norm_num [t24,precision]
noncomputable def t25 : RBox := {lo := -144081587984564201, hi := 144081587984564201}
lemma t25_contains : t25.Contains (sourcePower true 15 (-1/1) 2 25) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (-1/1) 2 25 coarse_15_27) <;> norm_num [t25,precision]
noncomputable def t26 : RBox := {lo := -21324456348662756, hi := 21324456348662756}
lemma t26_contains : t26.Contains (sourcePower true 15 (-1/1) 2 26) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (-1/1) 2 26 coarse_15_28) <;> norm_num [t26,precision]
noncomputable def t27 : RBox := {lo := -3062333875518606, hi := 3062333875518606}
lemma t27_contains : t27.Contains (sourcePower true 15 (-1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (-1/1) 2 27 coarse_15_29) <;> norm_num [t27,precision]
noncomputable def t28 : RBox := {lo := -427027912874177, hi := 427027912874177}
lemma t28_contains : t28.Contains (sourcePower true 15 (-1/1) 2 28) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 15 (-1/1) 2 28 coarse_15_30) <;> norm_num [t28,precision]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 15 (-1/1) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 15 (-1/1) 2) k.val := by
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
end SharpPlanar.Bernstein15

end OAI
