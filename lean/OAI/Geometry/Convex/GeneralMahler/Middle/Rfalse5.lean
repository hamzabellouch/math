import OAI.Geometry.Convex.GeneralMahler.Middle.Verified

namespace OAI
namespace GeneralMahler.SCal.Mid.Tab
open Grid Cert Cert.IV
lemma cfalse_5_0_2 : By (tile Cn false 5) 0 2 := by
  apply byRun (tile Cn false 5) 0 2 2
  · rfl
  decide +kernel
lemma cfalse_5_2_5 : By (tile Cn false 5) 2 5 := by
  apply byRun (tile Cn false 5) 2 3 5
  · rfl
  decide +kernel
lemma cfalse_5_0_5 : By (tile Cn false 5) 0 5 := byJoin cfalse_5_0_2 cfalse_5_2_5
lemma cfalse_5_5_8 : By (tile Cn false 5) 5 8 := by
  apply byRun (tile Cn false 5) 5 3 8
  · rfl
  decide +kernel
lemma cfalse_5_8_11 : By (tile Cn false 5) 8 11 := by
  apply byRun (tile Cn false 5) 8 3 11
  · rfl
  decide +kernel
lemma cfalse_5_5_11 : By (tile Cn false 5) 5 11 := byJoin cfalse_5_5_8 cfalse_5_8_11
lemma cfalse_5_0_11 : By (tile Cn false 5) 0 11 := byJoin cfalse_5_0_5 cfalse_5_5_11
lemma cfalse_5_11_13 : By (tile Cn false 5) 11 13 := by
  apply byRun (tile Cn false 5) 11 2 13
  · rfl
  decide +kernel
lemma cfalse_5_13_16 : By (tile Cn false 5) 13 16 := by
  apply byRun (tile Cn false 5) 13 3 16
  · rfl
  decide +kernel
lemma cfalse_5_11_16 : By (tile Cn false 5) 11 16 := byJoin cfalse_5_11_13 cfalse_5_13_16
lemma cfalse_5_16_19 : By (tile Cn false 5) 16 19 := by
  apply byRun (tile Cn false 5) 16 3 19
  · rfl
  decide +kernel
lemma cfalse_5_19_22 : By (tile Cn false 5) 19 22 := by
  apply byRun (tile Cn false 5) 19 3 22
  · rfl
  decide +kernel
lemma cfalse_5_16_22 : By (tile Cn false 5) 16 22 := byJoin cfalse_5_16_19 cfalse_5_19_22
lemma cfalse_5_11_22 : By (tile Cn false 5) 11 22 := byJoin cfalse_5_11_16 cfalse_5_16_22
lemma cfalse_5_0_22 : By (tile Cn false 5) 0 22 := byJoin cfalse_5_0_11 cfalse_5_11_22
lemma cfalse_5_22_24 : By (tile Cn false 5) 22 24 := by
  apply byRun (tile Cn false 5) 22 2 24
  · rfl
  decide +kernel
lemma cfalse_5_24_27 : By (tile Cn false 5) 24 27 := by
  apply byRun (tile Cn false 5) 24 3 27
  · rfl
  decide +kernel
lemma cfalse_5_22_27 : By (tile Cn false 5) 22 27 := byJoin cfalse_5_22_24 cfalse_5_24_27
lemma cfalse_5_27_30 : By (tile Cn false 5) 27 30 := by
  apply byRun (tile Cn false 5) 27 3 30
  · rfl
  decide +kernel
lemma cfalse_5_30_33 : By (tile Cn false 5) 30 33 := by
  apply byRun (tile Cn false 5) 30 3 33
  · rfl
  decide +kernel
lemma cfalse_5_27_33 : By (tile Cn false 5) 27 33 := byJoin cfalse_5_27_30 cfalse_5_30_33
lemma cfalse_5_22_33 : By (tile Cn false 5) 22 33 := byJoin cfalse_5_22_27 cfalse_5_27_33
lemma cfalse_5_33_36 : By (tile Cn false 5) 33 36 := by
  apply byRun (tile Cn false 5) 33 3 36
  · rfl
  decide +kernel
lemma cfalse_5_36_39 : By (tile Cn false 5) 36 39 := by
  apply byRun (tile Cn false 5) 36 3 39
  · rfl
  decide +kernel
lemma cfalse_5_33_39 : By (tile Cn false 5) 33 39 := byJoin cfalse_5_33_36 cfalse_5_36_39
lemma cfalse_5_39_42 : By (tile Cn false 5) 39 42 := by
  apply byRun (tile Cn false 5) 39 3 42
  · rfl
  decide +kernel
lemma cfalse_5_42_45 : By (tile Cn false 5) 42 45 := by
  apply byRun (tile Cn false 5) 42 3 45
  · rfl
  decide +kernel
lemma cfalse_5_39_45 : By (tile Cn false 5) 39 45 := byJoin cfalse_5_39_42 cfalse_5_42_45
lemma cfalse_5_33_45 : By (tile Cn false 5) 33 45 := byJoin cfalse_5_33_39 cfalse_5_39_45
lemma cfalse_5_22_45 : By (tile Cn false 5) 22 45 := byJoin cfalse_5_22_33 cfalse_5_33_45
lemma cfalse_5_0_45 : By (tile Cn false 5) 0 45 := byJoin cfalse_5_0_22 cfalse_5_22_45
lemma cfalse_5_45_47 : By (tile Cn false 5) 45 47 := by
  apply byRun (tile Cn false 5) 45 2 47
  · rfl
  decide +kernel
lemma cfalse_5_47_50 : By (tile Cn false 5) 47 50 := by
  apply byRun (tile Cn false 5) 47 3 50
  · rfl
  decide +kernel
lemma cfalse_5_45_50 : By (tile Cn false 5) 45 50 := byJoin cfalse_5_45_47 cfalse_5_47_50
lemma cfalse_5_50_53 : By (tile Cn false 5) 50 53 := by
  apply byRun (tile Cn false 5) 50 3 53
  · rfl
  decide +kernel
lemma cfalse_5_53_56 : By (tile Cn false 5) 53 56 := by
  apply byRun (tile Cn false 5) 53 3 56
  · rfl
  decide +kernel
lemma cfalse_5_50_56 : By (tile Cn false 5) 50 56 := byJoin cfalse_5_50_53 cfalse_5_53_56
lemma cfalse_5_45_56 : By (tile Cn false 5) 45 56 := byJoin cfalse_5_45_50 cfalse_5_50_56
lemma cfalse_5_56_58 : By (tile Cn false 5) 56 58 := by
  apply byRun (tile Cn false 5) 56 2 58
  · rfl
  decide +kernel
lemma cfalse_5_58_61 : By (tile Cn false 5) 58 61 := by
  apply byRun (tile Cn false 5) 58 3 61
  · rfl
  decide +kernel
lemma cfalse_5_56_61 : By (tile Cn false 5) 56 61 := byJoin cfalse_5_56_58 cfalse_5_58_61
lemma cfalse_5_61_64 : By (tile Cn false 5) 61 64 := by
  apply byRun (tile Cn false 5) 61 3 64
  · rfl
  decide +kernel
lemma cfalse_5_64_67 : By (tile Cn false 5) 64 67 := by
  apply byRun (tile Cn false 5) 64 3 67
  · rfl
  decide +kernel
lemma cfalse_5_61_67 : By (tile Cn false 5) 61 67 := byJoin cfalse_5_61_64 cfalse_5_64_67
lemma cfalse_5_56_67 : By (tile Cn false 5) 56 67 := byJoin cfalse_5_56_61 cfalse_5_61_67
lemma cfalse_5_45_67 : By (tile Cn false 5) 45 67 := byJoin cfalse_5_45_56 cfalse_5_56_67
lemma cfalse_5_67_69 : By (tile Cn false 5) 67 69 := by
  apply byRun (tile Cn false 5) 67 2 69
  · rfl
  decide +kernel
lemma cfalse_5_69_72 : By (tile Cn false 5) 69 72 := by
  apply byRun (tile Cn false 5) 69 3 72
  · rfl
  decide +kernel
lemma cfalse_5_67_72 : By (tile Cn false 5) 67 72 := byJoin cfalse_5_67_69 cfalse_5_69_72
lemma cfalse_5_72_75 : By (tile Cn false 5) 72 75 := by
  apply byRun (tile Cn false 5) 72 3 75
  · rfl
  decide +kernel
lemma cfalse_5_75_78 : By (tile Cn false 5) 75 78 := by
  apply byRun (tile Cn false 5) 75 3 78
  · rfl
  decide +kernel
lemma cfalse_5_72_78 : By (tile Cn false 5) 72 78 := byJoin cfalse_5_72_75 cfalse_5_75_78
lemma cfalse_5_67_78 : By (tile Cn false 5) 67 78 := byJoin cfalse_5_67_72 cfalse_5_72_78
lemma cfalse_5_78_81 : By (tile Cn false 5) 78 81 := by
  apply byRun (tile Cn false 5) 78 3 81
  · rfl
  decide +kernel
lemma cfalse_5_81_84 : By (tile Cn false 5) 81 84 := by
  apply byRun (tile Cn false 5) 81 3 84
  · rfl
  decide +kernel
lemma cfalse_5_78_84 : By (tile Cn false 5) 78 84 := byJoin cfalse_5_78_81 cfalse_5_81_84
lemma cfalse_5_84_87 : By (tile Cn false 5) 84 87 := by
  apply byRun (tile Cn false 5) 84 3 87
  · rfl
  decide +kernel
lemma cfalse_5_87_90 : By (tile Cn false 5) 87 90 := by
  apply byRun (tile Cn false 5) 87 3 90
  · rfl
  decide +kernel
lemma cfalse_5_84_90 : By (tile Cn false 5) 84 90 := byJoin cfalse_5_84_87 cfalse_5_87_90
lemma cfalse_5_78_90 : By (tile Cn false 5) 78 90 := byJoin cfalse_5_78_84 cfalse_5_84_90
lemma cfalse_5_67_90 : By (tile Cn false 5) 67 90 := byJoin cfalse_5_67_78 cfalse_5_78_90
lemma cfalse_5_45_90 : By (tile Cn false 5) 45 90 := byJoin cfalse_5_45_67 cfalse_5_67_90
lemma cfalse_5_0_90 : By (tile Cn false 5) 0 90 := byJoin cfalse_5_0_45 cfalse_5_45_90
end GeneralMahler.SCal.Mid.Tab

end OAI
