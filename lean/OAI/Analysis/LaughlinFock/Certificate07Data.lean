import Mathlib
import OAI.Analysis.LaughlinFock.FasterTrace
import OAI.Analysis.LaughlinFock.LDL

namespace OAI

/-! Certificate07 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

def fourYData_7 : Matrix (CopyLabel 7) (CopyLabel 7) ℚ :=
  copyMatrixData 7 [
    [(-166434639714168948577730130927/3758096384000000000000000000), (45995705370248318526416296167/7516192768000000000000000000), (-106335364725988709134966359/53687091200000000000000000), (-51594657218957307370313483247/4294967296000000000000000000)],
    [(45995705370248318526416296167/7516192768000000000000000000), (-87211931042683137626019530763/75161927680000000000000000000), (1568403660783923680978370343/3006477107200000000000000000), (3815628101661385334514451191/1717986918400000000000000000)],
    [(-106335364725988709134966359/53687091200000000000000000), (1568403660783923680978370343/3006477107200000000000000000), (-11751684800182621092199856481/30064771072000000000000000000), (-10949361788140579505956340379/8589934592000000000000000000)],
    [(-51594657218957307370313483247/4294967296000000000000000000), (3815628101661385334514451191/1717986918400000000000000000), (-10949361788140579505956340379/8589934592000000000000000000), (-148920474389511901767358542711/34359738368000000000000000000)]
  ]

def fourZData_7 : Matrix (CopyLabel 7) (CopyLabel 7) ℚ :=
  copyMatrixData 7 [
    [720, 0, -45, (315/2)],
    [0, 0, 0, 0],
    [-45, 0, (45/16), (-315/32)],
    [(315/2), 0, (-315/32), (2205/64)]
  ]

def fourLData_7 : Matrix (CopyLabel 7) (CopyLabel 7) ℚ :=
  copyMatrixData 7 [
    [1, 0, 0, 0],
    [0, 1, 0, 0],
    [(-1/16), 0, 1, 0],
    [(7/32), 0, 0, 1]
  ]

def fourPivotData_7 : CopyLabel 7 → ℚ :=
  copyDiagonalData 7 [(48465284516682192798125037847983/15032385536000000000000000000), 0, 0, 0]

theorem fourOccupations_7 : highestFourOccupations 7 = {{0,1,2,5}, {0,1,3,4}} := by
  decide +kernel

theorem fourYNumber_7_1_1 :
    (shortNumericRowsFourTrace 7 1 1 : ℚ) / fourCommonDenominator = (-166434639714168948577730130927/3758096384000000000000000000) := by
  decide +kernel

theorem fourYNumber_7_3_1 :
    (shortNumericRowsFourTrace 7 3 1 : ℚ) / fourCommonDenominator = (45995705370248318526416296167/7516192768000000000000000000) := by
  decide +kernel

theorem fourYNumber_7_3_3 :
    (shortNumericRowsFourTrace 7 3 3 : ℚ) / fourCommonDenominator = (-87211931042683137626019530763/75161927680000000000000000000) := by
  decide +kernel

theorem fourYNumber_7_5_1 :
    (shortNumericRowsFourTrace 7 5 1 : ℚ) / fourCommonDenominator = (-106335364725988709134966359/53687091200000000000000000) := by
  decide +kernel

theorem fourYNumber_7_5_3 :
    (shortNumericRowsFourTrace 7 5 3 : ℚ) / fourCommonDenominator = (1568403660783923680978370343/3006477107200000000000000000) := by
  decide +kernel

theorem fourYNumber_7_5_5 :
    (shortNumericRowsFourTrace 7 5 5 : ℚ) / fourCommonDenominator = (-11751684800182621092199856481/30064771072000000000000000000) := by
  decide +kernel

theorem fourYNumber_7_7_1 :
    (shortNumericRowsFourTrace 7 7 1 : ℚ) / fourCommonDenominator = (-51594657218957307370313483247/4294967296000000000000000000) := by
  decide +kernel

theorem fourYNumber_7_7_3 :
    (shortNumericRowsFourTrace 7 7 3 : ℚ) / fourCommonDenominator = (3815628101661385334514451191/1717986918400000000000000000) := by
  decide +kernel

theorem fourYNumber_7_7_5 :
    (shortNumericRowsFourTrace 7 7 5 : ℚ) / fourCommonDenominator = (-10949361788140579505956340379/8589934592000000000000000000) := by
  decide +kernel

theorem fourYNumber_7_7_7 :
    (shortNumericRowsFourTrace 7 7 7 : ℚ) / fourCommonDenominator = (-148920474389511901767358542711/34359738368000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
