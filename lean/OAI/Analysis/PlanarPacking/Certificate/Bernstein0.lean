import OAI.Analysis.PlanarPacking.Certificate.HighMoments0_0
import OAI.Analysis.PlanarPacking.Certificate.HighMoments0_4
import OAI.Analysis.PlanarPacking.BernsteinBoxes
import OAI.Analysis.PlanarPacking.Certificate.HighMoments0_1
import OAI.Analysis.PlanarPacking.Certificate.HighMoments0_2
import OAI.Analysis.PlanarPacking.Certificate.HighMoments0_3
import OAI.Analysis.PlanarPacking.Certificate.HighMoments0_5
import OAI.Analysis.PlanarPacking.Certificate.HighMoments0_6
import OAI.Analysis.PlanarPacking.Certificate.HighMoments0_7

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein0
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N1_right
noncomputable def t0 : RBox := {lo := 3010659550390303898621260289067, hi := 3010659550390480643209021776036}
lemma t0_checked : ((hm0_1_0_0.realAnswer).add hm0_0_1_0.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 0 (1/2) 0 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_0.realContains hm0_0_1_0.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -1157514538053939177724331753156, hi := -1157514538053536044087787283906}
lemma t1_checked : ((hm0_1_0_1.realAnswer).add hm0_0_1_1.realAnswer).scale (1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 0 (1/2) 0 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_1.realContains hm0_0_1_1.realContains) (1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -4083980829144199815552047121103, hi := -4083980829143671848176401706360}
lemma t2_checked : ((hm0_1_0_2.realAnswer).add hm0_0_1_2.realAnswer).scale (1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 0 (1/2) 0 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_2.realContains hm0_0_1_2.realContains) (1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 5721821381827118436337229302358, hi := 5721821381827687689264449589910}
lemma t3_checked : ((hm0_1_0_3.realAnswer).add hm0_0_1_3.realAnswer).scale (1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 0 (1/2) 0 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_3.realContains hm0_0_1_3.realContains) (1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := -5382937070567010163413286437938, hi := -5382937070566575703506296564245}
lemma t4_checked : ((hm0_1_0_4.realAnswer).add hm0_0_1_4.realAnswer).scale (1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 0 (1/2) 0 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_4.realContains hm0_0_1_4.realContains) (1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 5253869407757627792877906430708, hi := 5253869407757964053467863760797}
lemma t5_checked : ((hm0_1_0_5.realAnswer).add hm0_0_1_5.realAnswer).scale (1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 0 (1/2) 0 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_5.realContains hm0_0_1_5.realContains) (1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := -4661177298176000350739551351826, hi := -4661177298175791351040369632539}
lemma t6_checked : ((hm0_1_0_6.realAnswer).add hm0_0_1_6.realAnswer).scale (1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 0 (1/2) 0 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_6.realContains hm0_0_1_6.realContains) (1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 3374880889767393803869957738866, hi := 3374880889767507686009309906298}
lemma t7_checked : ((hm0_1_0_7.realAnswer).add hm0_0_1_7.realAnswer).scale (1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 0 (1/2) 0 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_7.realContains hm0_0_1_7.realContains) (1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := -2010835960397130498414037786335, hi := -2010835960397074580873968573056}
lemma t8_checked : ((hm0_1_0_8.realAnswer).add hm0_0_1_8.realAnswer).scale (1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 0 (1/2) 0 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_8.realContains hm0_0_1_8.realContains) (1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := 1018772257458285554425588694868, hi := 1018772257458309724068594789857}
lemma t9_checked : ((hm0_1_0_9.realAnswer).add hm0_0_1_9.realAnswer).scale (1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 0 (1/2) 0 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_9.realContains hm0_0_1_9.realContains) (1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -448722651349900756596575570102, hi := -448722651349891193108893116955}
lemma t10_checked : ((hm0_1_0_10.realAnswer).add hm0_0_1_10.realAnswer).scale (1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 0 (1/2) 0 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_10.realContains hm0_0_1_10.realContains) (1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := 173606185176861026422696113900, hi := 173606185176864469860234569222}
lemma t11_checked : ((hm0_1_0_11.realAnswer).add hm0_0_1_11.realAnswer).scale (1) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 0 (1/2) 0 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_11.realContains hm0_0_1_11.realContains) (1) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -59507280908054413476215557022, hi := -59507280908053273606054575733}
lemma t12_checked : ((hm0_1_0_12.realAnswer).add hm0_0_1_12.realAnswer).scale (1) 4096=t12 := by decide +kernel
lemma t12_contains : t12.Contains (sourcePower true 0 (1/2) 0 12) := by
  rw [← t12_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_12.realContains hm0_0_1_12.realContains) (1) 4096 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t13 : RBox := {lo := 18383711669706433117720700424, hi := 18383711669706782326150549042}
lemma t13_checked : ((hm0_1_0_13.realAnswer).add hm0_0_1_13.realAnswer).scale (1) 8192=t13 := by decide +kernel
lemma t13_contains : t13.Contains (sourcePower true 0 (1/2) 0 13) := by
  rw [← t13_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_13.realContains hm0_0_1_13.realContains) (1) 8192 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t14 : RBox := {lo := -5280308198453700154466861404, hi := -5280308198453600612036277149}
lemma t14_checked : ((hm0_1_0_14.realAnswer).add hm0_0_1_14.realAnswer).scale (1) 16384=t14 := by decide +kernel
lemma t14_contains : t14.Contains (sourcePower true 0 (1/2) 0 14) := by
  rw [← t14_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_14.realContains hm0_0_1_14.realContains) (1) 16384 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t15 : RBox := {lo := 1468750860697749988104331417, hi := 1468750860697776464442125617}
lemma t15_checked : ((hm0_1_0_15.realAnswer).add hm0_0_1_15.realAnswer).scale (1) 32768=t15 := by decide +kernel
lemma t15_contains : t15.Contains (sourcePower true 0 (1/2) 0 15) := by
  rw [← t15_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_15.realContains hm0_0_1_15.realContains) (1) 32768 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t16 : RBox := {lo := -408586155659153146991480533, hi := -408586155659146522856268285}
lemma t16_checked : ((hm0_1_0_16.realAnswer).add hm0_0_1_16.realAnswer).scale (1) 65536=t16 := by decide +kernel
lemma t16_contains : t16.Contains (sourcePower true 0 (1/2) 0 16) := by
  rw [← t16_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_16.realContains hm0_0_1_16.realContains) (1) 65536 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t17 : RBox := {lo := 114108058606255134053354090, hi := 114108058606256695231919493}
lemma t17_checked : ((hm0_1_0_17.realAnswer).add hm0_0_1_17.realAnswer).scale (1) 131072=t17 := by decide +kernel
lemma t17_contains : t17.Contains (sourcePower true 0 (1/2) 0 17) := by
  rw [← t17_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_17.realContains hm0_0_1_17.realContains) (1) 131072 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t18 : RBox := {lo := -31289156184766260600739793, hi := -31289156184765912884567838}
lemma t18_checked : ((hm0_1_0_18.realAnswer).add hm0_0_1_18.realAnswer).scale (1) 262144=t18 := by decide +kernel
lemma t18_contains : t18.Contains (sourcePower true 0 (1/2) 0 18) := by
  rw [← t18_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_18.realContains hm0_0_1_18.realContains) (1) 262144 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t19 : RBox := {lo := 8193300540967235684014113, hi := 8193300540967309215535189}
lemma t19_checked : ((hm0_1_0_19.realAnswer).add hm0_0_1_19.realAnswer).scale (1) 524288=t19 := by decide +kernel
lemma t19_contains : t19.Contains (sourcePower true 0 (1/2) 0 19) := by
  rw [← t19_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_19.realContains hm0_0_1_19.realContains) (1) 524288 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t20 : RBox := {lo := -2010567823212377569297526, hi := -2010567823212362778860796}
lemma t20_checked : ((hm0_1_0_20.realAnswer).add hm0_0_1_20.realAnswer).scale (1) 1048576=t20 := by decide +kernel
lemma t20_contains : t20.Contains (sourcePower true 0 (1/2) 0 20) := by
  rw [← t20_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_20.realContains hm0_0_1_20.realContains) (1) 1048576 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t21 : RBox := {lo := 458686901207641578218607, hi := 458686901207644417814637}
lemma t21_checked : ((hm0_1_0_21.realAnswer).add hm0_0_1_21.realAnswer).scale (1) 2097152=t21 := by decide +kernel
lemma t21_contains : t21.Contains (sourcePower true 0 (1/2) 0 21) := by
  rw [← t21_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_21.realContains hm0_0_1_21.realContains) (1) 2097152 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t22 : RBox := {lo := -97262997565299989711617, hi := -97262997565299469091222}
lemma t22_checked : ((hm0_1_0_22.realAnswer).add hm0_0_1_22.realAnswer).scale (1) 4194304=t22 := by decide +kernel
lemma t22_contains : t22.Contains (sourcePower true 0 (1/2) 0 22) := by
  rw [← t22_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_22.realContains hm0_0_1_22.realContains) (1) 4194304 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t23 : RBox := {lo := 19253022017069823168490, hi := 19253022017069914774625}
lemma t23_checked : ((hm0_1_0_23.realAnswer).add hm0_0_1_23.realAnswer).scale (1) 8388608=t23 := by decide +kernel
lemma t23_contains : t23.Contains (sourcePower true 0 (1/2) 0 23) := by
  rw [← t23_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_23.realContains hm0_0_1_23.realContains) (1) 8388608 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t24 : RBox := {lo := -3582895898254668588208, hi := -3582895898254653101891}
lemma t24_checked : ((hm0_1_0_24.realAnswer).add hm0_0_1_24.realAnswer).scale (1) 16777216=t24 := by decide +kernel
lemma t24_contains : t24.Contains (sourcePower true 0 (1/2) 0 24) := by
  rw [← t24_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_24.realContains hm0_0_1_24.realContains) (1) 16777216 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t25 : RBox := {lo := 632382829782203366350, hi := 632382829782205884770}
lemma t25_checked : ((hm0_1_0_25.realAnswer).add hm0_0_1_25.realAnswer).scale (1) 33554432=t25 := by decide +kernel
lemma t25_contains : t25.Contains (sourcePower true 0 (1/2) 0 25) := by
  rw [← t25_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_25.realContains hm0_0_1_25.realContains) (1) 33554432 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t26 : RBox := {lo := -106912686730081946069, hi := -106912686730081550688}
lemma t26_checked : ((hm0_1_0_26.realAnswer).add hm0_0_1_26.realAnswer).scale (1) 67108864=t26 := by decide +kernel
lemma t26_contains : t26.Contains (sourcePower true 0 (1/2) 0 26) := by
  rw [← t26_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_26.realContains hm0_0_1_26.realContains) (1) 67108864 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t27 : RBox := {lo := 17487194279363975319, hi := 17487194279364035379}
lemma t27_checked : ((hm0_1_0_27.realAnswer).add hm0_0_1_27.realAnswer).scale (1) 134217728=t27 := by decide +kernel
lemma t27_contains : t27.Contains (sourcePower true 0 (1/2) 0 27) := by
  rw [← t27_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_27.realContains hm0_0_1_27.realContains) (1) 134217728 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t28 : RBox := {lo := -2791162666881053465, hi := -2791162666881044618}
lemma t28_checked : ((hm0_1_0_28.realAnswer).add hm0_0_1_28.realAnswer).scale (1) 268435456=t28 := by decide +kernel
lemma t28_contains : t28.Contains (sourcePower true 0 (1/2) 0 28) := by
  rw [← t28_checked]
  convert RBox.contains_scale (RBox.contains_add hm0_1_0_28.realContains hm0_0_1_28.realContains) (1) 268435456 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 0 (1/2) 0 r.val) := by
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
lemma bound0 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 0 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound1 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 1 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound2 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 2 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound3 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 3 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound4 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 4 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound5 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 5 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound6 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 6 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound7 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 7 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound8 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 8 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound9 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 9 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound10 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 10 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound11 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 11 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound12 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 12 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound13 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 13 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound14 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 14 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound15 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 15 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound16 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 16 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound17 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 17 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound18 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 18 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound19 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 19 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound20 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 20 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound21 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 21 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound22 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 22 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound23 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 23 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound24 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 24 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound25 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 25 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound26 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 26 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound27 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 27 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound28 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 28 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 37) (v := 50) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound (k : Fin 29) : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) k.val := by
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
end SharpPlanar.Bernstein0

end OAI
