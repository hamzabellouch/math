import Mathlib
import OAI.Analysis.LaughlinFock.Sparse1315
import OAI.Analysis.LaughlinFock.Sparse1316

namespace OAI

/-! Sparse1317. -/
namespace LaughlinFock
def collectedFourData_13_7 : List (List CollectedFourTerm) := [
  collectedFourData_13_7_0,
  collectedFourData_13_7_1,
  collectedFourData_13_7_2,
  collectedFourData_13_7_3,
  collectedFourData_13_7_4,
  collectedFourData_13_7_5,
  collectedFourData_13_7_6,
  collectedFourData_13_7_7,
  collectedFourData_13_7_8,
  collectedFourData_13_7_9,
  collectedFourData_13_7_10,
  collectedFourData_13_7_11,
  collectedFourData_13_7_12,
  collectedFourData_13_7_13,
  collectedFourData_13_7_14,
  collectedFourData_13_7_15,
  collectedFourData_13_7_16,
  collectedFourData_13_7_17,
  collectedFourData_13_7_18,
  collectedFourData_13_7_19,
  collectedFourData_13_7_20,
  collectedFourData_13_7_21,
  collectedFourData_13_7_22,
  collectedFourData_13_7_23,
  collectedFourData_13_7_24,
  collectedFourData_13_7_25,
  collectedFourData_13_7_26,
  collectedFourData_13_7_27,
  collectedFourData_13_7_28,
  collectedFourData_13_7_29,
  collectedFourData_13_7_30,
  collectedFourData_13_7_31,
  collectedFourData_13_7_32,
  collectedFourData_13_7_33,
  collectedFourData_13_7_34,
  collectedFourData_13_7_35,
  collectedFourData_13_7_36,
  collectedFourData_13_7_37,
  collectedFourData_13_7_38,
  collectedFourData_13_7_39,
  collectedFourData_13_7_40,
  collectedFourData_13_7_41,
  collectedFourData_13_7_42,
  collectedFourData_13_7_43
]

theorem collectedFourChecked_13_7 : collectNumericRowParts 13 7 = collectedFourData_13_7 := by
  decide +kernel

def collectedFourData_13 : Fin 8 → List (List CollectedFourTerm) :=
  ![collectedFourData_13_0, collectedFourData_13_1, collectedFourData_13_2, collectedFourData_13_3, collectedFourData_13_4, collectedFourData_13_5, collectedFourData_13_6, collectedFourData_13_7]

theorem collectedFourChecked_13 (t : Fin 8) :
    collectNumericRowParts 13 t = collectedFourData_13 t := by
  fin_cases t
  · exact collectedFourChecked_13_0
  · exact collectedFourChecked_13_1
  · exact collectedFourChecked_13_2
  · exact collectedFourChecked_13_3
  · exact collectedFourChecked_13_4
  · exact collectedFourChecked_13_5
  · exact collectedFourChecked_13_6
  · exact collectedFourChecked_13_7

end LaughlinFock

end OAI
