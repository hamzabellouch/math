import OAI.Geometry.Convex.GeneralMahler.Middle.Verified

namespace OAI
namespace GeneralMahler.SCal.Mid.Tab
open Grid Cert Cert.IV
lemma ctrue_34_0_2 : By (tile Cn true 34) 0 2 := by
  apply byRun (tile Cn true 34) 0 2 2
  · rfl
  decide +kernel
lemma ctrue_34_2_5 : By (tile Cn true 34) 2 5 := by
  apply byRun (tile Cn true 34) 2 3 5
  · rfl
  decide +kernel
lemma ctrue_34_0_5 : By (tile Cn true 34) 0 5 := byJoin ctrue_34_0_2 ctrue_34_2_5
lemma ctrue_34_5_8 : By (tile Cn true 34) 5 8 := by
  apply byRun (tile Cn true 34) 5 3 8
  · rfl
  decide +kernel
lemma ctrue_34_8_11 : By (tile Cn true 34) 8 11 := by
  apply byRun (tile Cn true 34) 8 3 11
  · rfl
  decide +kernel
lemma ctrue_34_5_11 : By (tile Cn true 34) 5 11 := byJoin ctrue_34_5_8 ctrue_34_8_11
lemma ctrue_34_0_11 : By (tile Cn true 34) 0 11 := byJoin ctrue_34_0_5 ctrue_34_5_11
lemma ctrue_34_11_13 : By (tile Cn true 34) 11 13 := by
  apply byRun (tile Cn true 34) 11 2 13
  · rfl
  decide +kernel
lemma ctrue_34_13_16 : By (tile Cn true 34) 13 16 := by
  apply byRun (tile Cn true 34) 13 3 16
  · rfl
  decide +kernel
lemma ctrue_34_11_16 : By (tile Cn true 34) 11 16 := byJoin ctrue_34_11_13 ctrue_34_13_16
lemma ctrue_34_16_19 : By (tile Cn true 34) 16 19 := by
  apply byRun (tile Cn true 34) 16 3 19
  · rfl
  decide +kernel
lemma ctrue_34_19_22 : By (tile Cn true 34) 19 22 := by
  apply byRun (tile Cn true 34) 19 3 22
  · rfl
  decide +kernel
lemma ctrue_34_16_22 : By (tile Cn true 34) 16 22 := byJoin ctrue_34_16_19 ctrue_34_19_22
lemma ctrue_34_11_22 : By (tile Cn true 34) 11 22 := byJoin ctrue_34_11_16 ctrue_34_16_22
lemma ctrue_34_0_22 : By (tile Cn true 34) 0 22 := byJoin ctrue_34_0_11 ctrue_34_11_22
lemma ctrue_34_22_24 : By (tile Cn true 34) 22 24 := by
  apply byRun (tile Cn true 34) 22 2 24
  · rfl
  decide +kernel
lemma ctrue_34_24_27 : By (tile Cn true 34) 24 27 := by
  apply byRun (tile Cn true 34) 24 3 27
  · rfl
  decide +kernel
lemma ctrue_34_22_27 : By (tile Cn true 34) 22 27 := byJoin ctrue_34_22_24 ctrue_34_24_27
lemma ctrue_34_27_30 : By (tile Cn true 34) 27 30 := by
  apply byRun (tile Cn true 34) 27 3 30
  · rfl
  decide +kernel
lemma ctrue_34_30_33 : By (tile Cn true 34) 30 33 := by
  apply byRun (tile Cn true 34) 30 3 33
  · rfl
  decide +kernel
lemma ctrue_34_27_33 : By (tile Cn true 34) 27 33 := byJoin ctrue_34_27_30 ctrue_34_30_33
lemma ctrue_34_22_33 : By (tile Cn true 34) 22 33 := byJoin ctrue_34_22_27 ctrue_34_27_33
lemma ctrue_34_33_36 : By (tile Cn true 34) 33 36 := by
  apply byRun (tile Cn true 34) 33 3 36
  · rfl
  decide +kernel
lemma ctrue_34_36_39 : By (tile Cn true 34) 36 39 := by
  apply byRun (tile Cn true 34) 36 3 39
  · rfl
  decide +kernel
lemma ctrue_34_33_39 : By (tile Cn true 34) 33 39 := byJoin ctrue_34_33_36 ctrue_34_36_39
lemma ctrue_34_39_42 : By (tile Cn true 34) 39 42 := by
  apply byRun (tile Cn true 34) 39 3 42
  · rfl
  decide +kernel
lemma ctrue_34_42_45 : By (tile Cn true 34) 42 45 := by
  apply byRun (tile Cn true 34) 42 3 45
  · rfl
  decide +kernel
lemma ctrue_34_39_45 : By (tile Cn true 34) 39 45 := byJoin ctrue_34_39_42 ctrue_34_42_45
lemma ctrue_34_33_45 : By (tile Cn true 34) 33 45 := byJoin ctrue_34_33_39 ctrue_34_39_45
lemma ctrue_34_22_45 : By (tile Cn true 34) 22 45 := byJoin ctrue_34_22_33 ctrue_34_33_45
lemma ctrue_34_0_45 : By (tile Cn true 34) 0 45 := byJoin ctrue_34_0_22 ctrue_34_22_45
lemma ctrue_34_45_47 : By (tile Cn true 34) 45 47 := by
  apply byRun (tile Cn true 34) 45 2 47
  · rfl
  decide +kernel
lemma ctrue_34_47_50 : By (tile Cn true 34) 47 50 := by
  apply byRun (tile Cn true 34) 47 3 50
  · rfl
  decide +kernel
lemma ctrue_34_45_50 : By (tile Cn true 34) 45 50 := byJoin ctrue_34_45_47 ctrue_34_47_50
lemma ctrue_34_50_53 : By (tile Cn true 34) 50 53 := by
  apply byRun (tile Cn true 34) 50 3 53
  · rfl
  decide +kernel
lemma ctrue_34_53_56 : By (tile Cn true 34) 53 56 := by
  apply byRun (tile Cn true 34) 53 3 56
  · rfl
  decide +kernel
lemma ctrue_34_50_56 : By (tile Cn true 34) 50 56 := byJoin ctrue_34_50_53 ctrue_34_53_56
lemma ctrue_34_45_56 : By (tile Cn true 34) 45 56 := byJoin ctrue_34_45_50 ctrue_34_50_56
lemma ctrue_34_56_58 : By (tile Cn true 34) 56 58 := by
  apply byRun (tile Cn true 34) 56 2 58
  · rfl
  decide +kernel
lemma ctrue_34_58_61 : By (tile Cn true 34) 58 61 := by
  apply byRun (tile Cn true 34) 58 3 61
  · rfl
  decide +kernel
lemma ctrue_34_56_61 : By (tile Cn true 34) 56 61 := byJoin ctrue_34_56_58 ctrue_34_58_61
lemma ctrue_34_61_64 : By (tile Cn true 34) 61 64 := by
  apply byRun (tile Cn true 34) 61 3 64
  · rfl
  decide +kernel
lemma ctrue_34_64_67 : By (tile Cn true 34) 64 67 := by
  apply byRun (tile Cn true 34) 64 3 67
  · rfl
  decide +kernel
lemma ctrue_34_61_67 : By (tile Cn true 34) 61 67 := byJoin ctrue_34_61_64 ctrue_34_64_67
lemma ctrue_34_56_67 : By (tile Cn true 34) 56 67 := byJoin ctrue_34_56_61 ctrue_34_61_67
lemma ctrue_34_45_67 : By (tile Cn true 34) 45 67 := byJoin ctrue_34_45_56 ctrue_34_56_67
lemma ctrue_34_67_69 : By (tile Cn true 34) 67 69 := by
  apply byRun (tile Cn true 34) 67 2 69
  · rfl
  decide +kernel
lemma ctrue_34_69_72 : By (tile Cn true 34) 69 72 := by
  apply byRun (tile Cn true 34) 69 3 72
  · rfl
  decide +kernel
lemma ctrue_34_67_72 : By (tile Cn true 34) 67 72 := byJoin ctrue_34_67_69 ctrue_34_69_72
lemma ctrue_34_72_75 : By (tile Cn true 34) 72 75 := by
  apply byRun (tile Cn true 34) 72 3 75
  · rfl
  decide +kernel
lemma ctrue_34_75_78 : By (tile Cn true 34) 75 78 := by
  apply byRun (tile Cn true 34) 75 3 78
  · rfl
  decide +kernel
lemma ctrue_34_72_78 : By (tile Cn true 34) 72 78 := byJoin ctrue_34_72_75 ctrue_34_75_78
lemma ctrue_34_67_78 : By (tile Cn true 34) 67 78 := byJoin ctrue_34_67_72 ctrue_34_72_78
lemma ctrue_34_78_81 : By (tile Cn true 34) 78 81 := by
  apply byRun (tile Cn true 34) 78 3 81
  · rfl
  decide +kernel
lemma ctrue_34_81_84 : By (tile Cn true 34) 81 84 := by
  apply byRun (tile Cn true 34) 81 3 84
  · rfl
  decide +kernel
lemma ctrue_34_78_84 : By (tile Cn true 34) 78 84 := byJoin ctrue_34_78_81 ctrue_34_81_84
lemma ctrue_34_84_87 : By (tile Cn true 34) 84 87 := by
  apply byRun (tile Cn true 34) 84 3 87
  · rfl
  decide +kernel
lemma ctrue_34_87_90 : By (tile Cn true 34) 87 90 := by
  apply byRun (tile Cn true 34) 87 3 90
  · rfl
  decide +kernel
lemma ctrue_34_84_90 : By (tile Cn true 34) 84 90 := byJoin ctrue_34_84_87 ctrue_34_87_90
lemma ctrue_34_78_90 : By (tile Cn true 34) 78 90 := byJoin ctrue_34_78_84 ctrue_34_84_90
lemma ctrue_34_67_90 : By (tile Cn true 34) 67 90 := byJoin ctrue_34_67_78 ctrue_34_78_90
lemma ctrue_34_45_90 : By (tile Cn true 34) 45 90 := byJoin ctrue_34_45_67 ctrue_34_67_90
lemma ctrue_34_0_90 : By (tile Cn true 34) 0 90 := byJoin ctrue_34_0_45 ctrue_34_45_90
end GeneralMahler.SCal.Mid.Tab

end OAI
