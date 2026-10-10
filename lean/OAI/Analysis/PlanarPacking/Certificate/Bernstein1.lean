import OAI.Analysis.PlanarPacking.BernsteinBoxes
import OAI.Analysis.PlanarPacking.Certificate.HighMoments1_0
import OAI.Analysis.PlanarPacking.Certificate.HighMoments1_1
import OAI.Analysis.PlanarPacking.Certificate.HighMoments1_2
import OAI.Analysis.PlanarPacking.Certificate.HighMoments1_3
import OAI.Analysis.PlanarPacking.Certificate.HighMoments1_4
import OAI.Analysis.PlanarPacking.Certificate.HighMoments1_5
import OAI.Analysis.PlanarPacking.Certificate.HighMoments1_6
import OAI.Analysis.PlanarPacking.Certificate.HighMoments1_7

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein1
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 1763035019179741583475524811551, hi := 1763035019180016298943129538706}
lemma t0_checked : ((hm1_0_0_1.realAnswer).add hm1_1_1_1.realAnswer).scale (-1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower false 1 (1/1) 1 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_1.realContains hm1_1_1_1.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -1589948320085958454589340602391, hi := -1589948320085516608921108133404}
lemma t1_checked : ((hm1_0_0_2.realAnswer).add hm1_1_1_2.realAnswer).scale (-1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower false 1 (1/1) 1 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_2.realContains hm1_1_1_2.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := -516651337560567654075495423230, hi := -516651337560039257667266488754}
lemma t2_checked : ((hm1_0_0_3.realAnswer).add hm1_1_1_3.realAnswer).scale (-1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower false 1 (1/1) 1 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_3.realContains hm1_1_1_3.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 801784442360821482964379328962, hi := 801784442361316154786389263566}
lemma t3_checked : ((hm1_0_0_4.realAnswer).add hm1_1_1_4.realAnswer).scale (-1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower false 1 (1/1) 1 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_4.realContains hm1_1_1_4.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := 154911090581499165263164190010, hi := 154911090581888673933835026952}
lemma t4_checked : ((hm1_0_0_5.realAnswer).add hm1_1_1_5.realAnswer).scale (-1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 1 (1/1) 1 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_5.realContains hm1_1_1_5.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -621940417853192215857733651016, hi := -621940417852914747141806167349}
lemma t5_checked : ((hm1_0_0_6.realAnswer).add hm1_1_1_6.realAnswer).scale (-1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower false 1 (1/1) 1 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_6.realContains hm1_1_1_6.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := 413994558940119903448888763146, hi := 413994558940310059129363612600}
lemma t6_checked : ((hm1_0_0_7.realAnswer).add hm1_1_1_7.realAnswer).scale (-1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 1 (1/1) 1 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_7.realContains hm1_1_1_7.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 19074696079656669206920597865, hi := 19074696079776231501906104084}
lemma t7_checked : ((hm1_0_0_8.realAnswer).add hm1_1_1_8.realAnswer).scale (-1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower false 1 (1/1) 1 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_8.realContains hm1_1_1_8.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := -209797788981833789732473398312, hi := -209797788981766874195519719747}
lemma t8_checked : ((hm1_0_0_9.realAnswer).add hm1_1_1_9.realAnswer).scale (-1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower false 1 (1/1) 1 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_9.realContains hm1_1_1_9.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := 112480352673426549289171735150, hi := 112480352673462599384311698547}
lemma t9_checked : ((hm1_0_0_10.realAnswer).add hm1_1_1_10.realAnswer).scale (-1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower false 1 (1/1) 1 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_10.realContains hm1_1_1_10.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := 17790286685661893946485983686, hi := 17790286685680409469069298980}
lemma t10_checked : ((hm1_0_0_11.realAnswer).add hm1_1_1_11.realAnswer).scale (-1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower false 1 (1/1) 1 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_11.realContains hm1_1_1_11.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -51140060085380105627978919119, hi := -51140060085370396211299625973}
lemma t11_checked : ((hm1_0_0_12.realAnswer).add hm1_1_1_12.realAnswer).scale (-1) 1=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower false 1 (1/1) 1 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_12.realContains hm1_1_1_12.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := 30152114990247550907852423187, hi := 30152114990252585641102423293}
lemma t12_checked : ((hm1_0_0_13.realAnswer).add hm1_1_1_13.realAnswer).scale (-1) 1=t12 := by decide +kernel
lemma t12_contains : t12.Contains (sourcePower false 1 (1/1) 1 12) := by
  rw [← t12_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_13.realContains hm1_1_1_13.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t13 : RBox := {lo := -11046979774555862378193581022, hi := -11046979774553308340642151448}
lemma t13_checked : ((hm1_0_0_14.realAnswer).add hm1_1_1_14.realAnswer).scale (-1) 1=t13 := by decide +kernel
lemma t13_contains : t13.Contains (sourcePower false 1 (1/1) 1 13) := by
  rw [← t13_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_14.realContains hm1_1_1_14.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t14 : RBox := {lo := 5162769573346517541969431140, hi := 5162769573347768927435120444}
lemma t14_checked : ((hm1_0_0_15.realAnswer).add hm1_1_1_15.realAnswer).scale (-1) 1=t14 := by decide +kernel
lemma t14_contains : t14.Contains (sourcePower false 1 (1/1) 1 14) := by
  rw [← t14_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_15.realContains hm1_1_1_15.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t15 : RBox := {lo := -4403592368600343358290555103, hi := -4403592368599751747625958426}
lemma t15_checked : ((hm1_0_0_16.realAnswer).add hm1_1_1_16.realAnswer).scale (-1) 1=t15 := by decide +kernel
lemma t15_contains : t15.Contains (sourcePower false 1 (1/1) 1 15) := by
  rw [← t15_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_16.realContains hm1_1_1_16.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t16 : RBox := {lo := 3488754170411527892798534312, hi := 3488754170411794564206431519}
lemma t16_checked : ((hm1_0_0_17.realAnswer).add hm1_1_1_17.realAnswer).scale (-1) 1=t16 := by decide +kernel
lemma t16_contains : t16.Contains (sourcePower false 1 (1/1) 1 16) := by
  rw [← t16_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_17.realContains hm1_1_1_17.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t17 : RBox := {lo := -2061999144534369104910251530, hi := -2061999144534253902924316023}
lemma t17_checked : ((hm1_0_0_18.realAnswer).add hm1_1_1_18.realAnswer).scale (-1) 1=t17 := by decide +kernel
lemma t17_contains : t17.Contains (sourcePower false 1 (1/1) 1 17) := by
  rw [← t17_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_18.realContains hm1_1_1_18.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t18 : RBox := {lo := 924499542799954635228891164, hi := 924499542800002002996525523}
lemma t18_checked : ((hm1_0_0_19.realAnswer).add hm1_1_1_19.realAnswer).scale (-1) 1=t18 := by decide +kernel
lemma t18_contains : t18.Contains (sourcePower false 1 (1/1) 1 18) := by
  rw [← t18_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_19.realContains hm1_1_1_19.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t19 : RBox := {lo := -324455201683265947638790714, hi := -324455201683247345135613693}
lemma t19_checked : ((hm1_0_0_20.realAnswer).add hm1_1_1_20.realAnswer).scale (-1) 1=t19 := by decide +kernel
lemma t19_contains : t19.Contains (sourcePower false 1 (1/1) 1 19) := by
  rw [← t19_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_20.realContains hm1_1_1_20.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t20 : RBox := {lo := 91545119069663452170116028, hi := 91545119069670434926977076}
lemma t20_checked : ((hm1_0_0_21.realAnswer).add hm1_1_1_21.realAnswer).scale (-1) 1=t20 := by decide +kernel
lemma t20_contains : t20.Contains (sourcePower false 1 (1/1) 1 20) := by
  rw [← t20_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_21.realContains hm1_1_1_21.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t21 : RBox := {lo := -22045524796855351856240072, hi := -22045524796852843918995093}
lemma t21_checked : ((hm1_0_0_22.realAnswer).add hm1_1_1_22.realAnswer).scale (-1) 1=t21 := by decide +kernel
lemma t21_contains : t21.Contains (sourcePower false 1 (1/1) 1 21) := by
  rw [← t21_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_22.realContains hm1_1_1_22.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t22 : RBox := {lo := 5609036036619128155670574, hi := 5609036036619991439920331}
lemma t22_checked : ((hm1_0_0_23.realAnswer).add hm1_1_1_23.realAnswer).scale (-1) 1=t22 := by decide +kernel
lemma t22_contains : t22.Contains (sourcePower false 1 (1/1) 1 22) := by
  rw [← t22_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_23.realContains hm1_1_1_23.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t23 : RBox := {lo := -2109415754424522019037564, hi := -2109415754424236315411121}
lemma t23_checked : ((hm1_0_0_24.realAnswer).add hm1_1_1_24.realAnswer).scale (-1) 1=t23 := by decide +kernel
lemma t23_contains : t23.Contains (sourcePower false 1 (1/1) 1 23) := by
  rw [← t23_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_24.realContains hm1_1_1_24.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t24 : RBox := {lo := 1058619222603894933722271, hi := 1058619222603986036418624}
lemma t24_checked : ((hm1_0_0_25.realAnswer).add hm1_1_1_25.realAnswer).scale (-1) 1=t24 := by decide +kernel
lemma t24_contains : t24.Contains (sourcePower false 1 (1/1) 1 24) := by
  rw [← t24_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_25.realContains hm1_1_1_25.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t25 : RBox := {lo := -521543548658586339883345, hi := -521543548658558139400882}
lemma t25_checked : ((hm1_0_0_26.realAnswer).add hm1_1_1_26.realAnswer).scale (-1) 1=t25 := by decide +kernel
lemma t25_contains : t25.Contains (sourcePower false 1 (1/1) 1 25) := by
  rw [← t25_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_26.realContains hm1_1_1_26.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t26 : RBox := {lo := 227865089432252726638814, hi := 227865089432261341607778}
lemma t26_checked : ((hm1_0_0_27.realAnswer).add hm1_1_1_27.realAnswer).scale (-1) 1=t26 := by decide +kernel
lemma t26_contains : t26.Contains (sourcePower false 1 (1/1) 1 26) := by
  rw [← t26_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_27.realContains hm1_1_1_27.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t27 : RBox := {lo := -88178579406599415888153, hi := -88178579406596665859095}
lemma t27_checked : ((hm1_0_0_28.realAnswer).add hm1_1_1_28.realAnswer).scale (-1) 1=t27 := by decide +kernel
lemma t27_contains : t27.Contains (sourcePower false 1 (1/1) 1 27) := by
  rw [← t27_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_28.realContains hm1_1_1_28.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t28 : RBox := {lo := 30745284988016099645406, hi := 30745284988017150506141}
lemma t28_checked : ((hm1_0_0_29.realAnswer).add hm1_1_1_29.realAnswer).scale (-1) 1=t28 := by decide +kernel
lemma t28_contains : t28.Contains (sourcePower false 1 (1/1) 1 28) := by
  rw [← t28_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_0_0_29.realContains hm1_1_1_29.realContains) (-1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 1 (1/1) 1 r.val) := by
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
lemma bound0 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 0 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound1 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 1 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound2 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 2 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound3 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 3 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound4 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 4 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound5 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 5 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound6 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 6 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound7 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 7 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound8 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 8 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound9 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 9 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound10 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 10 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound11 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 11 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound12 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 12 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound13 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 13 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound14 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 14 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound15 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 15 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound16 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 16 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound17 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 17 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound18 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 18 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound19 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 19 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound20 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 20 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound21 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 21 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound22 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 22 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound23 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 23 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound24 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 24 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound25 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 25 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound26 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 26 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound27 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 27 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound28 : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) 28 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/50<powerToBernstein 28 (sourcePower false 1 (1/1) 1) k.val := by
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
noncomputable def t0 : RBox := {lo := 1748076608800213996526705081841, hi := 1748076608800676585401726848184}
lemma t0_checked : ((hm1_1_0_2.realAnswer).add hm1_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 1 (1/1) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_2.realContains hm1_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := -2566936845787339703052147652281, hi := -2566936845786754539193231840479}
lemma t1_checked : ((hm1_1_0_3.realAnswer).add hm1_0_1_3.realAnswer).scale (1) 1=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 1 (1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_3.realContains hm1_0_1_3.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := 788015125822514376363896825203, hi := 788015125823082517645739465582}
lemma t2_checked : ((hm1_1_0_4.realAnswer).add hm1_0_1_4.realAnswer).scale (1) 1=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 1 (1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_4.realContains hm1_0_1_4.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := 801473329179703242055848542511, hi := 801473329180161348230600379273}
lemma t3_checked : ((hm1_1_0_5.realAnswer).add hm1_0_1_5.realAnswer).scale (1) 1=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 1 (1/1) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_5.realContains hm1_0_1_5.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := -989619402545820147705823690132, hi := -989619402545488651469392575143}
lemma t4_checked : ((hm1_1_0_6.realAnswer).add hm1_0_1_6.realAnswer).scale (1) 1=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 1 (1/1) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_6.realContains hm1_0_1_6.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := 511302174796620577486891691928, hi := 511302174796849928637520657558}
lemma t5_checked : ((hm1_1_0_7.realAnswer).add hm1_0_1_7.realAnswer).scale (1) 1=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 1 (1/1) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_7.realContains hm1_0_1_7.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := 12583790543309548381913794509, hi := 12583790543454410324477615593}
lemma t6_checked : ((hm1_1_0_8.realAnswer).add hm1_0_1_8.realAnswer).scale (1) 1=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 1 (1/1) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_8.realContains hm1_0_1_8.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := -215395302916849649773894154097, hi := -215395302916768433511783198780}
lemma t7_checked : ((hm1_1_0_9.realAnswer).add hm1_0_1_9.realAnswer).scale (1) 1=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 1 (1/1) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_9.realContains hm1_0_1_9.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 113396156120500350094090807216, hi := 113396156120544112539067936038}
lemma t8_checked : ((hm1_1_0_10.realAnswer).add hm1_0_1_10.realAnswer).scale (1) 1=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 1 (1/1) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_10.realContains hm1_0_1_10.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := 20032974768048632949798581891, hi := 20032974768071102912263638250}
lemma t9_checked : ((hm1_1_0_11.realAnswer).add hm1_0_1_11.realAnswer).scale (1) 1=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 1 (1/1) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_11.realContains hm1_0_1_11.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -53038356483437408213364385242, hi := -53038356483425632327696911781}
lemma t10_checked : ((hm1_1_0_12.realAnswer).add hm1_0_1_12.realAnswer).scale (1) 1=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 1 (1/1) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_12.realContains hm1_0_1_12.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := 30716895649799357063629917613, hi := 30716895649805459499645368830}
lemma t11_checked : ((hm1_1_0_13.realAnswer).add hm1_0_1_13.realAnswer).scale (1) 1=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 1 (1/1) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_13.realContains hm1_0_1_13.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -10938471405241648612681814823, hi := -10938471405238554263991531056}
lemma t12_checked : ((hm1_1_0_14.realAnswer).add hm1_0_1_14.realAnswer).scale (1) 1=t12 := by decide +kernel
lemma t12_contains : t12.Contains (sourcePower true 1 (1/1) 2 12) := by
  rw [← t12_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_14.realContains hm1_0_1_14.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t13 : RBox := {lo := 5042761956922174978190354586, hi := 5042761956923690588993795146}
lemma t13_checked : ((hm1_1_0_15.realAnswer).add hm1_0_1_15.realAnswer).scale (1) 1=t13 := by decide +kernel
lemma t13_contains : t13.Contains (sourcePower true 1 (1/1) 2 13) := by
  rw [← t13_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_15.realContains hm1_0_1_15.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t14 : RBox := {lo := -4434420475855080999677896484, hi := -4434420475854364524811789121}
lemma t14_checked : ((hm1_1_0_16.realAnswer).add hm1_0_1_16.realAnswer).scale (1) 1=t14 := by decide +kernel
lemma t14_contains : t14.Contains (sourcePower true 1 (1/1) 2 14) := by
  rw [← t14_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_16.realContains hm1_0_1_16.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t15 : RBox := {lo := 3581722126421433399160583268, hi := 3581722126421756363452697623}
lemma t15_checked : ((hm1_1_0_17.realAnswer).add hm1_0_1_17.realAnswer).scale (1) 1=t15 := by decide +kernel
lemma t15_contains : t15.Contains (sourcePower true 1 (1/1) 2 15) := by
  rw [← t15_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_17.realContains hm1_0_1_17.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t16 : RBox := {lo := -2135390667226566009319078920, hi := -2135390667226426459202021410}
lemma t16_checked : ((hm1_1_0_18.realAnswer).add hm1_0_1_18.realAnswer).scale (1) 1=t16 := by decide +kernel
lemma t16_contains : t16.Contains (sourcePower true 1 (1/1) 2 16) := by
  rw [← t16_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_18.realContains hm1_0_1_18.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t17 : RBox := {lo := 961417521058673443420458188, hi := 961417521058730840977265561}
lemma t17_checked : ((hm1_1_0_19.realAnswer).add hm1_0_1_19.realAnswer).scale (1) 1=t17 := by decide +kernel
lemma t17_contains : t17.Contains (sourcePower true 1 (1/1) 2 17) := by
  rw [← t17_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_19.realContains hm1_0_1_19.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t18 : RBox := {lo := -338082901303105091570767255, hi := -338082901303082538300085402}
lemma t18_checked : ((hm1_1_0_20.realAnswer).add hm1_0_1_20.realAnswer).scale (1) 1=t18 := by decide +kernel
lemma t18_contains : t18.Contains (sourcePower true 1 (1/1) 2 18) := by
  rw [← t18_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_20.realContains hm1_0_1_20.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t19 : RBox := {lo := 95488672852492451082865915, hi := 95488672852500922821227300}
lemma t19_checked : ((hm1_1_0_21.realAnswer).add hm1_0_1_21.realAnswer).scale (1) 1=t19 := by decide +kernel
lemma t19_contains : t19.Contains (sourcePower true 1 (1/1) 2 19) := by
  rw [← t19_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_21.realContains hm1_0_1_21.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t20 : RBox := {lo := -23066020529813207384913554, hi := -23066020529810161612111032}
lemma t20_checked : ((hm1_1_0_22.realAnswer).add hm1_0_1_22.realAnswer).scale (1) 1=t20 := by decide +kernel
lemma t20_contains : t20.Contains (sourcePower true 1 (1/1) 2 20) := by
  rw [← t20_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_22.realContains hm1_0_1_22.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t21 : RBox := {lo := 5944787904485716633364017, hi := 5944787904486766455540668}
lemma t21_checked : ((hm1_1_0_23.realAnswer).add hm1_0_1_23.realAnswer).scale (1) 1=t21 := by decide +kernel
lemma t21_contains : t21.Contains (sourcePower true 1 (1/1) 2 21) := by
  rw [← t21_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_23.realContains hm1_0_1_23.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t22 : RBox := {lo := -2277348885376867519397703, hi := -2277348885376519471605148}
lemma t22_checked : ((hm1_1_0_24.realAnswer).add hm1_0_1_24.realAnswer).scale (1) 1=t22 := by decide +kernel
lemma t22_contains : t22.Contains (sourcePower true 1 (1/1) 2 22) := by
  rw [← t22_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_24.realContains hm1_0_1_24.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t23 : RBox := {lo := 1149887104482546949859620, hi := 1149887104482658163684470}
lemma t23_checked : ((hm1_1_0_25.realAnswer).add hm1_0_1_25.realAnswer).scale (1) 1=t23 := by decide +kernel
lemma t23_contains : t23.Contains (sourcePower true 1 (1/1) 2 23) := by
  rw [← t23_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_25.realContains hm1_0_1_25.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t24 : RBox := {lo := -565156860402344662984212, hi := -565156860402310176104551}
lemma t24_checked : ((hm1_1_0_26.realAnswer).add hm1_0_1_26.realAnswer).scale (1) 1=t24 := by decide +kernel
lemma t24_contains : t24.Contains (sourcePower true 1 (1/1) 2 24) := by
  rw [← t24_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_26.realContains hm1_0_1_26.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t25 : RBox := {lo := 245650501084249431557409, hi := 245650501084259953858200}
lemma t25_checked : ((hm1_1_0_27.realAnswer).add hm1_0_1_27.realAnswer).scale (1) 1=t25 := by decide +kernel
lemma t25_contains : t25.Contains (sourcePower true 1 (1/1) 2 25) := by
  rw [← t25_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_27.realContains hm1_0_1_27.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t26 : RBox := {lo := -94467326662983615864608, hi := -94467326662980300844301}
lemma t26_checked : ((hm1_1_0_28.realAnswer).add hm1_0_1_28.realAnswer).scale (1) 1=t26 := by decide +kernel
lemma t26_contains : t26.Contains (sourcePower true 1 (1/1) 2 26) := by
  rw [← t26_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_28.realContains hm1_0_1_28.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t27 : RBox := {lo := 32713979065011183591439, hi := 32713979065012398252319}
lemma t27_checked : ((hm1_1_0_29.realAnswer).add hm1_0_1_29.realAnswer).scale (1) 1=t27 := by decide +kernel
lemma t27_contains : t27.Contains (sourcePower true 1 (1/1) 2 27) := by
  rw [← t27_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_29.realContains hm1_0_1_29.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t28 : RBox := {lo := -10364206612527697121435, hi := -10364206612527075581675}
lemma t28_checked : ((hm1_1_0_30.realAnswer).add hm1_0_1_30.realAnswer).scale (1) 1=t28 := by decide +kernel
lemma t28_contains : t28.Contains (sourcePower true 1 (1/1) 2 28) := by
  rw [← t28_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_30.realContains hm1_0_1_30.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 1 (1/1) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 0 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound1 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 1 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound2 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 2 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound3 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 3 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound4 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 4 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound5 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 5 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound6 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 6 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound7 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 7 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound8 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 8 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound9 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 9 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound10 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 10 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound11 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 11 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound12 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 12 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound13 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 13 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound14 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 14 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound15 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 15 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound16 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 16 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound17 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 17 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound18 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 18 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound19 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 19 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound20 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 20 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound21 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 21 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound22 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 22 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound23 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 23 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound24 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 24 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound25 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 25 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound26 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 26 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound27 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 27 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound28 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) 28 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (1/1) 2) k.val := by
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
namespace N1_left
noncomputable def t0 : RBox := {lo := 1748076608800213996526705081841, hi := 1748076608800676585401726848184}
lemma t0_checked : ((hm1_1_0_2.realAnswer).add hm1_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
lemma t0_contains : t0.Contains (sourcePower true 1 (-1/2) 2 0) := by
  rw [← t0_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_2.realContains hm1_0_1_2.realContains) (1) 1 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t1 : RBox := {lo := 1283468422893377269596615920239, hi := 1283468422893669851526073826141}
lemma t1_checked : ((hm1_1_0_3.realAnswer).add hm1_0_1_3.realAnswer).scale (-1) 2=t1 := by decide +kernel
lemma t1_contains : t1.Contains (sourcePower true 1 (-1/2) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_3.realContains hm1_0_1_3.realContains) (-1) 2 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t2 : RBox := {lo := 197003781455628594090974206300, hi := 197003781455770629411434866396}
lemma t2_checked : ((hm1_1_0_4.realAnswer).add hm1_0_1_4.realAnswer).scale (1) 4=t2 := by decide +kernel
lemma t2_contains : t2.Contains (sourcePower true 1 (-1/2) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_4.realContains hm1_0_1_4.realContains) (1) 4 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t3 : RBox := {lo := -100184166147520168528825047410, hi := -100184166147462905256981067813}
lemma t3_checked : ((hm1_1_0_5.realAnswer).add hm1_0_1_5.realAnswer).scale (-1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 1 (-1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_5.realContains hm1_0_1_5.realContains) (-1) 8 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t4 : RBox := {lo := -61851212659113759231613980634, hi := -61851212659093040716837035946}
lemma t4_checked : ((hm1_1_0_6.realAnswer).add hm1_0_1_6.realAnswer).scale (1) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower true 1 (-1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_6.realContains hm1_0_1_6.realContains) (1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t5 : RBox := {lo := -15978192962401560269922520549, hi := -15978192962394393046465365372}
lemma t5_checked : ((hm1_1_0_7.realAnswer).add hm1_0_1_7.realAnswer).scale (-1) 32=t5 := by decide +kernel
lemma t5_contains : t5.Contains (sourcePower true 1 (-1/2) 2 5) := by
  rw [← t5_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_7.realContains hm1_0_1_7.realContains) (-1) 32 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t6 : RBox := {lo := 196621727239211693467403039, hi := 196621727241475161319962744}
lemma t6_checked : ((hm1_1_0_8.realAnswer).add hm1_0_1_8.realAnswer).scale (1) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower true 1 (-1/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_8.realContains hm1_0_1_8.realContains) (1) 64 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t7 : RBox := {lo := 1682775804037253386810806240, hi := 1682775804037887888858548079}
lemma t7_checked : ((hm1_1_0_9.realAnswer).add hm1_0_1_9.realAnswer).scale (-1) 128=t7 := by decide +kernel
lemma t7_contains : t7.Contains (sourcePower true 1 (-1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_9.realContains hm1_0_1_9.realContains) (-1) 128 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t8 : RBox := {lo := 442953734845704492555042215, hi := 442953734845875439605734126}
lemma t8_checked : ((hm1_1_0_10.realAnswer).add hm1_0_1_10.realAnswer).scale (1) 256=t8 := by decide +kernel
lemma t8_contains : t8.Contains (sourcePower true 1 (-1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_10.realContains hm1_0_1_10.realContains) (1) 256 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t9 : RBox := {lo := -39126903843888872875514919, hi := -39126903843844986230075355}
lemma t9_checked : ((hm1_1_0_11.realAnswer).add hm1_0_1_11.realAnswer).scale (-1) 512=t9 := by decide +kernel
lemma t9_contains : t9.Contains (sourcePower true 1 (-1/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_11.realContains hm1_0_1_11.realContains) (-1) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t10 : RBox := {lo := -51795270003356843958363658, hi := -51795270003345344070016515}
lemma t10_checked : ((hm1_1_0_12.realAnswer).add hm1_0_1_12.realAnswer).scale (1) 1024=t10 := by decide +kernel
lemma t10_contains : t10.Contains (sourcePower true 1 (-1/2) 2 10) := by
  rw [← t10_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_12.realContains hm1_0_1_12.realContains) (1) 1024 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t11 : RBox := {lo := -14998484204006572021311216, hi := -14998484204003592316225545}
lemma t11_checked : ((hm1_1_0_13.realAnswer).add hm1_0_1_13.realAnswer).scale (-1) 2048=t11 := by decide +kernel
lemma t11_contains : t11.Contains (sourcePower true 1 (-1/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_13.realContains hm1_0_1_13.realContains) (-1) 2048 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t12 : RBox := {lo := -2670525245420324368330522, hi := -2670525245419568912107307}
lemma t12_checked : ((hm1_1_0_14.realAnswer).add hm1_0_1_14.realAnswer).scale (1) 4096=t12 := by decide +kernel
lemma t12_contains : t12.Contains (sourcePower true 1 (-1/2) 2 12) := by
  rw [← t12_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_14.realContains hm1_0_1_14.realContains) (1) 4096 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t13 : RBox := {lo := -615571527944786448851782, hi := -615571527944601437767377}
lemma t13_checked : ((hm1_1_0_15.realAnswer).add hm1_0_1_15.realAnswer).scale (-1) 8192=t13 := by decide +kernel
lemma t13_contains : t13.Contains (sourcePower true 1 (-1/2) 2 13) := by
  rw [← t13_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_15.realContains hm1_0_1_15.realContains) (-1) 8192 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t14 : RBox := {lo := -270655546622014221171747, hi := -270655546621970491016344}
lemma t14_checked : ((hm1_1_0_16.realAnswer).add hm1_0_1_16.realAnswer).scale (1) 16384=t14 := by decide +kernel
lemma t14_contains : t14.Contains (sourcePower true 1 (-1/2) 2 14) := by
  rw [← t14_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_16.realContains hm1_0_1_16.realContains) (1) 16384 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t15 : RBox := {lo := -109305484815117076521384, hi := -109305484815107220433367}
lemma t15_checked : ((hm1_1_0_17.realAnswer).add hm1_0_1_17.realAnswer).scale (-1) 32768=t15 := by decide +kernel
lemma t15_contains : t15.Contains (sourcePower true 1 (-1/2) 2 15) := by
  rw [← t15_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_17.realContains hm1_0_1_17.realContains) (-1) 32768 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t16 : RBox := {lo := -32583475757241302632433, hi := -32583475757239173266632}
lemma t16_checked : ((hm1_1_0_18.realAnswer).add hm1_0_1_18.realAnswer).scale (1) 65536=t16 := by decide +kernel
lemma t16_contains : t16.Contains (sourcePower true 1 (-1/2) 2 16) := by
  rw [← t16_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_18.realContains hm1_0_1_18.realContains) (1) 65536 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t17 : RBox := {lo := -7335033577413412788218, hi := -7335033577412974879611}
lemma t17_checked : ((hm1_1_0_19.realAnswer).add hm1_0_1_19.realAnswer).scale (-1) 131072=t17 := by decide +kernel
lemma t17_contains : t17.Contains (sourcePower true 1 (-1/2) 2 17) := by
  rw [← t17_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_19.realContains hm1_0_1_19.realContains) (-1) 131072 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t18 : RBox := {lo := -1289683919155521742138, hi := -1289683919155435708237}
lemma t18_checked : ((hm1_1_0_20.realAnswer).add hm1_0_1_20.realAnswer).scale (1) 262144=t18 := by decide +kernel
lemma t18_contains : t18.Contains (sourcePower true 1 (-1/2) 2 18) := by
  rw [← t18_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_20.realContains hm1_0_1_20.realContains) (1) 262144 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t19 : RBox := {lo := -182130189614297719615, hi := -182130189614281561055}
lemma t19_checked : ((hm1_1_0_21.realAnswer).add hm1_0_1_21.realAnswer).scale (-1) 524288=t19 := by decide +kernel
lemma t19_contains : t19.Contains (sourcePower true 1 (-1/2) 2 19) := by
  rw [← t19_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_21.realContains hm1_0_1_21.realContains) (-1) 524288 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t20 : RBox := {lo := -21997471360982139001, hi := -21997471360979234325}
lemma t20_checked : ((hm1_1_0_22.realAnswer).add hm1_0_1_22.realAnswer).scale (1) 1048576=t20 := by decide +kernel
lemma t20_contains : t20.Contains (sourcePower true 1 (-1/2) 2 20) := by
  rw [← t20_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_22.realContains hm1_0_1_22.realContains) (1) 1048576 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t21 : RBox := {lo := -2834695770495780209, hi := -2834695770495279614}
lemma t21_checked : ((hm1_1_0_23.realAnswer).add hm1_0_1_23.realAnswer).scale (-1) 2097152=t21 := by decide +kernel
lemma t21_contains : t21.Contains (sourcePower true 1 (-1/2) 2 21) := by
  rw [← t21_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_23.realContains hm1_0_1_23.realContains) (-1) 2097152 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t22 : RBox := {lo := -542962285370079880, hi := -542962285369996898}
lemma t22_checked : ((hm1_1_0_24.realAnswer).add hm1_0_1_24.realAnswer).scale (1) 4194304=t22 := by decide +kernel
lemma t22_contains : t22.Contains (sourcePower true 1 (-1/2) 2 22) := by
  rw [← t22_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_24.realContains hm1_0_1_24.realContains) (1) 4194304 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t23 : RBox := {lo := -137077224788982650, hi := -137077224788969391}
lemma t23_checked : ((hm1_1_0_25.realAnswer).add hm1_0_1_25.realAnswer).scale (-1) 8388608=t23 := by decide +kernel
lemma t23_contains : t23.Contains (sourcePower true 1 (-1/2) 2 23) := by
  rw [← t23_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_25.realContains hm1_0_1_25.realContains) (-1) 8388608 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t24 : RBox := {lo := -33685973906656782, hi := -33685973906654726}
lemma t24_checked : ((hm1_1_0_26.realAnswer).add hm1_0_1_26.realAnswer).scale (1) 16777216=t24 := by decide +kernel
lemma t24_contains : t24.Contains (sourcePower true 1 (-1/2) 2 24) := by
  rw [← t24_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_26.realContains hm1_0_1_26.realContains) (1) 16777216 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t25 : RBox := {lo := -7320955428012013, hi := -7320955428011698}
lemma t25_checked : ((hm1_1_0_27.realAnswer).add hm1_0_1_27.realAnswer).scale (-1) 33554432=t25 := by decide +kernel
lemma t25_contains : t25.Contains (sourcePower true 1 (-1/2) 2 25) := by
  rw [← t25_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_27.realContains hm1_0_1_27.realContains) (-1) 33554432 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t26 : RBox := {lo := -1407672862156982, hi := -1407672862156932}
lemma t26_checked : ((hm1_1_0_28.realAnswer).add hm1_0_1_28.realAnswer).scale (1) 67108864=t26 := by decide +kernel
lemma t26_contains : t26.Contains (sourcePower true 1 (-1/2) 2 26) := by
  rw [← t26_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_28.realContains hm1_0_1_28.realContains) (1) 67108864 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t27 : RBox := {lo := -243738137669954, hi := -243738137669944}
lemma t27_checked : ((hm1_1_0_29.realAnswer).add hm1_0_1_29.realAnswer).scale (-1) 134217728=t27 := by decide +kernel
lemma t27_contains : t27.Contains (sourcePower true 1 (-1/2) 2 27) := by
  rw [← t27_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_29.realContains hm1_0_1_29.realContains) (-1) 134217728 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def t28 : RBox := {lo := -38609678344905, hi := -38609678344901}
lemma t28_checked : ((hm1_1_0_30.realAnswer).add hm1_0_1_30.realAnswer).scale (1) 268435456=t28 := by decide +kernel
lemma t28_contains : t28.Contains (sourcePower true 1 (-1/2) 2 28) := by
  rw [← t28_checked]
  convert RBox.contains_scale (RBox.contains_add hm1_1_0_30.realContains hm1_0_1_30.realContains) (1) 268435456 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 1 (-1/2) 2 r.val) := by
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
lemma bound0 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 0 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound1 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 1 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound2 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 2 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound3 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 3 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound4 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 4 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound5 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 5 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound6 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 6 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound7 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 7 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound8 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 8 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound9 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 9 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound10 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 10 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound11 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 11 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound12 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 12 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound13 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 13 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound14 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 14 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound15 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 15 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound16 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 16 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound17 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 17 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound18 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 18 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound19 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 19 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound20 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 20 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound21 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 21 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound22 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 22 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound23 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 23 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound24 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 24 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound25 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 25 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound26 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 26 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound27 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 27 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound28 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 28 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt (u := 9) (v := 50) (bernsteinBox_contains ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) k.val := by
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
end SharpPlanar.Bernstein1

end OAI
