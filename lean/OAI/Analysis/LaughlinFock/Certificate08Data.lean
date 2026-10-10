import Mathlib
import OAI.Analysis.LaughlinFock.LDL
import OAI.Analysis.LaughlinFock.Sparse0833

namespace OAI

/-! Certificate08 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

def fourYData_8 : Matrix (CopyLabel 8) (CopyLabel 8) ℚ :=
  copyMatrixData 8 [
    [(-63725659480009131775992546879/536870912000000000000000000), (-1915756407095537127488603541/268435456000000000000000000), (5848046872621070751629176509/536870912000000000000000000), (-15409311511841483890426595631/2147483648000000000000000000)],
    [(-1915756407095537127488603541/268435456000000000000000000), (-20669734241111819247651968649/7516192768000000000000000000), (9455940384238314087831042759/3758096384000000000000000000), (-12382701644617792221325809759/4294967296000000000000000000)],
    [(5848046872621070751629176509/536870912000000000000000000), (9455940384238314087831042759/3758096384000000000000000000), (-2472410179928723052502001181/1073741824000000000000000000), (1770955193734196297743289949/536870912000000000000000000)],
    [(-15409311511841483890426595631/2147483648000000000000000000), (-12382701644617792221325809759/4294967296000000000000000000), (1770955193734196297743289949/536870912000000000000000000), (-178020445962132587387054522433/17179869184000000000000000000)]
  ]

def fourZData_8 : Matrix (CopyLabel 8) (CopyLabel 8) ℚ :=
  copyMatrixData 8 [
    [0, 0, 0, 0],
    [0, 90, -45, (315/8)],
    [0, -45, (45/2), (-315/16)],
    [0, (315/8), (-315/16), (2205/128)]
  ]

def fourLData_8 : Matrix (CopyLabel 8) (CopyLabel 8) ℚ :=
  copyMatrixData 8 [
    [1, 0, 0, 0],
    [0, 1, 0, 0],
    [0, (-1/2), 1, 0],
    [0, (7/16), 0, 1]
  ]

def fourPivotData_8 : CopyLabel 8 → ℚ :=
  copyDiagonalData 8 [0, (6175145290577572637607316298463/120259084288000000000000000000), 0, 0]

theorem fourOccupations_8 : highestFourOccupations 8 = {{0,1,2,6}, {0,1,3,5}, {0,2,3,4}} := by
  decide +kernel

theorem fourYNumber_8_1_1 :
    (collectedFourPartsTrace 8 1 1 collectedFourData_8 : ℚ) / fourCommonDenominator = (-63725659480009131775992546879/536870912000000000000000000) := by
  decide +kernel

theorem fourYNumber_8_3_1 :
    (collectedFourPartsTrace 8 3 1 collectedFourData_8 : ℚ) / fourCommonDenominator = (-1915756407095537127488603541/268435456000000000000000000) := by
  decide +kernel

theorem fourYNumber_8_3_3 :
    (collectedFourPartsTrace 8 3 3 collectedFourData_8 : ℚ) / fourCommonDenominator = (-20669734241111819247651968649/7516192768000000000000000000) := by
  decide +kernel

theorem fourYNumber_8_5_1 :
    (collectedFourPartsTrace 8 5 1 collectedFourData_8 : ℚ) / fourCommonDenominator = (5848046872621070751629176509/536870912000000000000000000) := by
  decide +kernel

theorem fourYNumber_8_5_3 :
    (collectedFourPartsTrace 8 5 3 collectedFourData_8 : ℚ) / fourCommonDenominator = (9455940384238314087831042759/3758096384000000000000000000) := by
  decide +kernel

theorem fourYNumber_8_5_5 :
    (collectedFourPartsTrace 8 5 5 collectedFourData_8 : ℚ) / fourCommonDenominator = (-2472410179928723052502001181/1073741824000000000000000000) := by
  decide +kernel

theorem fourYNumber_8_7_1 :
    (collectedFourPartsTrace 8 7 1 collectedFourData_8 : ℚ) / fourCommonDenominator = (-15409311511841483890426595631/2147483648000000000000000000) := by
  decide +kernel

theorem fourYNumber_8_7_3 :
    (collectedFourPartsTrace 8 7 3 collectedFourData_8 : ℚ) / fourCommonDenominator = (-12382701644617792221325809759/4294967296000000000000000000) := by
  decide +kernel

theorem fourYNumber_8_7_5 :
    (collectedFourPartsTrace 8 7 5 collectedFourData_8 : ℚ) / fourCommonDenominator = (1770955193734196297743289949/536870912000000000000000000) := by
  decide +kernel

theorem fourYNumber_8_7_7 :
    (collectedFourPartsTrace 8 7 7 collectedFourData_8 : ℚ) / fourCommonDenominator = (-178020445962132587387054522433/17179869184000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
