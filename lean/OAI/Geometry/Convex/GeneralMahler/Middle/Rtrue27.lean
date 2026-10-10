import OAI.Geometry.Convex.GeneralMahler.Middle.Verified

namespace OAI
namespace GeneralMahler.SCal.Mid.Tab
open Grid Cert Cert.IV
lemma ctrue_27_0_2 : By (tile Cn true 27) 0 2 := by
  apply byRun (tile Cn true 27) 0 2 2
  · rfl
  decide +kernel
lemma ctrue_27_2_5 : By (tile Cn true 27) 2 5 := by
  apply byRun (tile Cn true 27) 2 3 5
  · rfl
  decide +kernel
lemma ctrue_27_0_5 : By (tile Cn true 27) 0 5 := byJoin ctrue_27_0_2 ctrue_27_2_5
lemma ctrue_27_5_8 : By (tile Cn true 27) 5 8 := by
  apply byRun (tile Cn true 27) 5 3 8
  · rfl
  decide +kernel
lemma ctrue_27_8_11 : By (tile Cn true 27) 8 11 := by
  apply byRun (tile Cn true 27) 8 3 11
  · rfl
  decide +kernel
lemma ctrue_27_5_11 : By (tile Cn true 27) 5 11 := byJoin ctrue_27_5_8 ctrue_27_8_11
lemma ctrue_27_0_11 : By (tile Cn true 27) 0 11 := byJoin ctrue_27_0_5 ctrue_27_5_11
lemma ctrue_27_11_13 : By (tile Cn true 27) 11 13 := by
  apply byRun (tile Cn true 27) 11 2 13
  · rfl
  decide +kernel
lemma ctrue_27_13_16 : By (tile Cn true 27) 13 16 := by
  apply byRun (tile Cn true 27) 13 3 16
  · rfl
  decide +kernel
lemma ctrue_27_11_16 : By (tile Cn true 27) 11 16 := byJoin ctrue_27_11_13 ctrue_27_13_16
lemma ctrue_27_16_19 : By (tile Cn true 27) 16 19 := by
  apply byRun (tile Cn true 27) 16 3 19
  · rfl
  decide +kernel
lemma ctrue_27_19_22 : By (tile Cn true 27) 19 22 := by
  apply byRun (tile Cn true 27) 19 3 22
  · rfl
  decide +kernel
lemma ctrue_27_16_22 : By (tile Cn true 27) 16 22 := byJoin ctrue_27_16_19 ctrue_27_19_22
lemma ctrue_27_11_22 : By (tile Cn true 27) 11 22 := byJoin ctrue_27_11_16 ctrue_27_16_22
lemma ctrue_27_0_22 : By (tile Cn true 27) 0 22 := byJoin ctrue_27_0_11 ctrue_27_11_22
lemma ctrue_27_22_24 : By (tile Cn true 27) 22 24 := by
  apply byRun (tile Cn true 27) 22 2 24
  · rfl
  decide +kernel
lemma ctrue_27_24_27 : By (tile Cn true 27) 24 27 := by
  apply byRun (tile Cn true 27) 24 3 27
  · rfl
  decide +kernel
lemma ctrue_27_22_27 : By (tile Cn true 27) 22 27 := byJoin ctrue_27_22_24 ctrue_27_24_27
lemma ctrue_27_27_30 : By (tile Cn true 27) 27 30 := by
  apply byRun (tile Cn true 27) 27 3 30
  · rfl
  decide +kernel
lemma ctrue_27_30_33 : By (tile Cn true 27) 30 33 := by
  apply byRun (tile Cn true 27) 30 3 33
  · rfl
  decide +kernel
lemma ctrue_27_27_33 : By (tile Cn true 27) 27 33 := byJoin ctrue_27_27_30 ctrue_27_30_33
lemma ctrue_27_22_33 : By (tile Cn true 27) 22 33 := byJoin ctrue_27_22_27 ctrue_27_27_33
lemma ctrue_27_33_36 : By (tile Cn true 27) 33 36 := by
  apply byRun (tile Cn true 27) 33 3 36
  · rfl
  decide +kernel
lemma ctrue_27_36_39 : By (tile Cn true 27) 36 39 := by
  apply byRun (tile Cn true 27) 36 3 39
  · rfl
  decide +kernel
lemma ctrue_27_33_39 : By (tile Cn true 27) 33 39 := byJoin ctrue_27_33_36 ctrue_27_36_39
lemma ctrue_27_39_42 : By (tile Cn true 27) 39 42 := by
  apply byRun (tile Cn true 27) 39 3 42
  · rfl
  decide +kernel
lemma ctrue_27_42_45 : By (tile Cn true 27) 42 45 := by
  apply byRun (tile Cn true 27) 42 3 45
  · rfl
  decide +kernel
lemma ctrue_27_39_45 : By (tile Cn true 27) 39 45 := byJoin ctrue_27_39_42 ctrue_27_42_45
lemma ctrue_27_33_45 : By (tile Cn true 27) 33 45 := byJoin ctrue_27_33_39 ctrue_27_39_45
lemma ctrue_27_22_45 : By (tile Cn true 27) 22 45 := byJoin ctrue_27_22_33 ctrue_27_33_45
lemma ctrue_27_0_45 : By (tile Cn true 27) 0 45 := byJoin ctrue_27_0_22 ctrue_27_22_45
lemma ctrue_27_45_47 : By (tile Cn true 27) 45 47 := by
  apply byRun (tile Cn true 27) 45 2 47
  · rfl
  decide +kernel
lemma ctrue_27_47_50 : By (tile Cn true 27) 47 50 := by
  apply byRun (tile Cn true 27) 47 3 50
  · rfl
  decide +kernel
lemma ctrue_27_45_50 : By (tile Cn true 27) 45 50 := byJoin ctrue_27_45_47 ctrue_27_47_50
lemma ctrue_27_50_53 : By (tile Cn true 27) 50 53 := by
  apply byRun (tile Cn true 27) 50 3 53
  · rfl
  decide +kernel
lemma ctrue_27_53_56 : By (tile Cn true 27) 53 56 := by
  apply byRun (tile Cn true 27) 53 3 56
  · rfl
  decide +kernel
lemma ctrue_27_50_56 : By (tile Cn true 27) 50 56 := byJoin ctrue_27_50_53 ctrue_27_53_56
lemma ctrue_27_45_56 : By (tile Cn true 27) 45 56 := byJoin ctrue_27_45_50 ctrue_27_50_56
lemma ctrue_27_56_58 : By (tile Cn true 27) 56 58 := by
  apply byRun (tile Cn true 27) 56 2 58
  · rfl
  decide +kernel
lemma ctrue_27_58_61 : By (tile Cn true 27) 58 61 := by
  apply byRun (tile Cn true 27) 58 3 61
  · rfl
  decide +kernel
lemma ctrue_27_56_61 : By (tile Cn true 27) 56 61 := byJoin ctrue_27_56_58 ctrue_27_58_61
lemma ctrue_27_61_64 : By (tile Cn true 27) 61 64 := by
  apply byRun (tile Cn true 27) 61 3 64
  · rfl
  decide +kernel
lemma ctrue_27_64_67 : By (tile Cn true 27) 64 67 := by
  apply byRun (tile Cn true 27) 64 3 67
  · rfl
  decide +kernel
lemma ctrue_27_61_67 : By (tile Cn true 27) 61 67 := byJoin ctrue_27_61_64 ctrue_27_64_67
lemma ctrue_27_56_67 : By (tile Cn true 27) 56 67 := byJoin ctrue_27_56_61 ctrue_27_61_67
lemma ctrue_27_45_67 : By (tile Cn true 27) 45 67 := byJoin ctrue_27_45_56 ctrue_27_56_67
lemma ctrue_27_67_69 : By (tile Cn true 27) 67 69 := by
  apply byRun (tile Cn true 27) 67 2 69
  · rfl
  decide +kernel
lemma ctrue_27_69_72 : By (tile Cn true 27) 69 72 := by
  apply byRun (tile Cn true 27) 69 3 72
  · rfl
  decide +kernel
lemma ctrue_27_67_72 : By (tile Cn true 27) 67 72 := byJoin ctrue_27_67_69 ctrue_27_69_72
lemma ctrue_27_72_75 : By (tile Cn true 27) 72 75 := by
  apply byRun (tile Cn true 27) 72 3 75
  · rfl
  decide +kernel
lemma ctrue_27_75_78 : By (tile Cn true 27) 75 78 := by
  apply byRun (tile Cn true 27) 75 3 78
  · rfl
  decide +kernel
lemma ctrue_27_72_78 : By (tile Cn true 27) 72 78 := byJoin ctrue_27_72_75 ctrue_27_75_78
lemma ctrue_27_67_78 : By (tile Cn true 27) 67 78 := byJoin ctrue_27_67_72 ctrue_27_72_78
lemma ctrue_27_78_81 : By (tile Cn true 27) 78 81 := by
  apply byRun (tile Cn true 27) 78 3 81
  · rfl
  decide +kernel
lemma ctrue_27_81_84 : By (tile Cn true 27) 81 84 := by
  apply byRun (tile Cn true 27) 81 3 84
  · rfl
  decide +kernel
lemma ctrue_27_78_84 : By (tile Cn true 27) 78 84 := byJoin ctrue_27_78_81 ctrue_27_81_84
lemma ctrue_27_84_87 : By (tile Cn true 27) 84 87 := by
  apply byRun (tile Cn true 27) 84 3 87
  · rfl
  decide +kernel
lemma ctrue_27_87_90 : By (tile Cn true 27) 87 90 := by
  apply byRun (tile Cn true 27) 87 3 90
  · rfl
  decide +kernel
lemma ctrue_27_84_90 : By (tile Cn true 27) 84 90 := byJoin ctrue_27_84_87 ctrue_27_87_90
lemma ctrue_27_78_90 : By (tile Cn true 27) 78 90 := byJoin ctrue_27_78_84 ctrue_27_84_90
lemma ctrue_27_67_90 : By (tile Cn true 27) 67 90 := byJoin ctrue_27_67_78 ctrue_27_78_90
lemma ctrue_27_45_90 : By (tile Cn true 27) 45 90 := byJoin ctrue_27_45_67 ctrue_27_67_90
lemma ctrue_27_0_90 : By (tile Cn true 27) 0 90 := byJoin ctrue_27_0_45 ctrue_27_45_90
end GeneralMahler.SCal.Mid.Tab

end OAI
