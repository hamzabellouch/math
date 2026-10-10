import Mathlib
import OAI.Analysis.LaughlinFock.FasterTrace
import OAI.Analysis.LaughlinFock.LDL

namespace OAI

/-! Certificate05 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

def fourYData_5 : Matrix (CopyLabel 5) (CopyLabel 5) ℚ :=
  copyMatrixData 5 [
    [(-2024172058688009719584426783/60129542144000000000000000000), (61749543313564923991586775801/601295421440000000000000000000), (-371682523763530720573033623/12025908428800000000000000000)],
    [(61749543313564923991586775801/601295421440000000000000000000), (-81625478502088057676049676411/1202590842880000000000000000000), (6370708288009007294968493697/120259084288000000000000000000)],
    [(-371682523763530720573033623/12025908428800000000000000000), (6370708288009007294968493697/120259084288000000000000000000), (-400615328776296560234415701/3006477107200000000000000000)]
  ]

def fourZData_5 : Matrix (CopyLabel 5) (CopyLabel 5) ℚ :=
  copyMatrixData 5 [
    [24, -6, (15/2)],
    [-6, (3/2), (-15/8)],
    [(15/2), (-15/8), (75/32)]
  ]

def fourLData_5 : Matrix (CopyLabel 5) (CopyLabel 5) ℚ :=
  copyMatrixData 5 [
    [1, 0, 0],
    [(-1/4), 1, 0],
    [(5/16), 0, 1]
  ]

def fourPivotData_5 : CopyLabel 5 → ℚ :=
  copyDiagonalData 5 [(1888290710477919674814730887537/18790481920000000000000000000), 0, 0]

theorem fourOccupations_5 : highestFourOccupations 5 = {{0,1,2,3}} := by
  decide +kernel

theorem fourYNumber_5_1_1 :
    (shortNumericRowsFourTrace 5 1 1 : ℚ) / fourCommonDenominator = (-2024172058688009719584426783/60129542144000000000000000000) := by
  decide +kernel

theorem fourYNumber_5_3_1 :
    (shortNumericRowsFourTrace 5 3 1 : ℚ) / fourCommonDenominator = (61749543313564923991586775801/601295421440000000000000000000) := by
  decide +kernel

theorem fourYNumber_5_3_3 :
    (shortNumericRowsFourTrace 5 3 3 : ℚ) / fourCommonDenominator = (-81625478502088057676049676411/1202590842880000000000000000000) := by
  decide +kernel

theorem fourYNumber_5_5_1 :
    (shortNumericRowsFourTrace 5 5 1 : ℚ) / fourCommonDenominator = (-371682523763530720573033623/12025908428800000000000000000) := by
  decide +kernel

theorem fourYNumber_5_5_3 :
    (shortNumericRowsFourTrace 5 5 3 : ℚ) / fourCommonDenominator = (6370708288009007294968493697/120259084288000000000000000000) := by
  decide +kernel

theorem fourYNumber_5_5_5 :
    (shortNumericRowsFourTrace 5 5 5 : ℚ) / fourCommonDenominator = (-400615328776296560234415701/3006477107200000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
