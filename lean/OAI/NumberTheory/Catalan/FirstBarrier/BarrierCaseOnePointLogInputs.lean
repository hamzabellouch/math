import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

namespace OAI

noncomputable section
namespace InternalCatalan.Case1PointData

def FixedLogNormalization (s : ℝ) (m : ℤ) (y : ℚ) : Prop :=
  s = (2 : ℝ) ^ m * (y : ℝ) ∧
    (y : ℝ) ∈ Set.Icc (1 : ℝ) 2 ∧ |(m : ℝ)| ≤ 100

def X0 : ℚ := (-1983459957 / 2000000000)

def X0PrintedUpper : ℚ := (-1389245765787 / 500000000000)

theorem X0_normalizations :
    FixedLogNormalization |(X0 : ℝ)| (-1) (1983459957 / 1000000000) ∧
    FixedLogNormalization (1 - (X0 : ℝ)) (0) (3983459957 / 2000000000) ∧
    FixedLogNormalization (1 + (X0 : ℝ) ^ 2) (0) (7934113401022441849 / 4000000000000000000) := by
  norm_num [FixedLogNormalization, X0, Set.mem_Icc]

def X1 : ℚ := (-2259572153 / 10000000000)

def X1PrintedUpper : ℚ := (-331166682987 / 250000000000)

theorem X1_normalizations :
    FixedLogNormalization |(X1 : ℝ)| (-3) (2259572153 / 1250000000) ∧
    FixedLogNormalization (1 - (X1 : ℝ)) (0) (12259572153 / 10000000000) ∧
    FixedLogNormalization (1 + (X1 : ℝ) ^ 2) (0) (105105666314613055409 / 100000000000000000000) := by
  norm_num [FixedLogNormalization, X1, Set.mem_Icc]

def X2 : ℚ := (1271904013 / 5000000000)

def X2PrintedUpper : ℚ := (-662327903523 / 500000000000)

theorem X2_normalizations :
    FixedLogNormalization |(X2 : ℝ)| (-2) (1271904013 / 1250000000) ∧
    FixedLogNormalization (1 - (X2 : ℝ)) (-1) (3728095987 / 2500000000) ∧
    FixedLogNormalization (1 + (X2 : ℝ) ^ 2) (0) (26617739818285504169 / 25000000000000000000) := by
  norm_num [FixedLogNormalization, X2, Set.mem_Icc]

def X3 : ℚ := (4437270259 / 10000000000)

def X3PrintedUpper : ℚ := (-1352236629957 / 1000000000000)

theorem X3_normalizations :
    FixedLogNormalization |(X3 : ℝ)| (-2) (4437270259 / 2500000000) ∧
    FixedLogNormalization (1 - (X3 : ℝ)) (-1) (5562729741 / 5000000000) ∧
    FixedLogNormalization (1 + (X3 : ℝ) ^ 2) (0) (119689367351405927081 / 100000000000000000000) := by
  norm_num [FixedLogNormalization, X3, Set.mem_Icc]

def X4 : ℚ := (634829897 / 1000000000)

def X4PrintedUpper : ℚ := (-52986653177 / 40000000000)

theorem X4_normalizations :
    FixedLogNormalization |(X4 : ℝ)| (-1) (634829897 / 500000000) ∧
    FixedLogNormalization (1 - (X4 : ℝ)) (-2) (365170103 / 250000000) ∧
    FixedLogNormalization (1 + (X4 : ℝ) ^ 2) (0) (1403008998125030609 / 1000000000000000000) := by
  norm_num [FixedLogNormalization, X4, Set.mem_Icc]

def X5 : ℚ := -1

def X5PrintedUpper : ℚ := (-1387909038763 / 500000000000)

theorem X5_normalizations :
    FixedLogNormalization |(X5 : ℝ)| (0) 1 ∧
    FixedLogNormalization (1 - (X5 : ℝ)) (1) 1 ∧
    FixedLogNormalization (1 + (X5 : ℝ) ^ 2) (1) 1 := by
  norm_num [FixedLogNormalization, X5, Set.mem_Icc]

def X6 : ℚ := (-1 / 2)

def X6PrintedUpper : ℚ := (-308811563981 / 200000000000)

theorem X6_normalizations :
    FixedLogNormalization |(X6 : ℝ)| (-1) 1 ∧
    FixedLogNormalization (1 - (X6 : ℝ)) (0) (3 / 2) ∧
    FixedLogNormalization (1 + (X6 : ℝ) ^ 2) (0) (5 / 4) := by
  norm_num [FixedLogNormalization, X6, Set.mem_Icc]

def X7 : ℚ := (1 / 2)

def X7PrintedUpper : ℚ := (-336889420219 / 250000000000)

theorem X7_normalizations :
    FixedLogNormalization |(X7 : ℝ)| (-1) 1 ∧
    FixedLogNormalization (1 - (X7 : ℝ)) (-1) 1 ∧
    FixedLogNormalization (1 + (X7 : ℝ) ^ 2) (0) (5 / 4) := by
  norm_num [FixedLogNormalization, X7, Set.mem_Icc]

def Y0 : ℚ := (266334893 / 5000000000)

def Y0PrintedUpper : ℚ := (-1142628921 / 800000000)

theorem Y0_normalizations :
    FixedLogNormalization (Y0 : ℝ) (-5) (266334893 / 156250000) ∧
    FixedLogNormalization (1 - (Y0 : ℝ)) (-1) (4733665107 / 2500000000) := by
  norm_num [FixedLogNormalization, Y0, Set.mem_Icc]

def Y1 : ℚ := (100169573 / 400000000)

def Y1PrintedUpper : ℚ := (-757801323681 / 500000000000)

theorem Y1_normalizations :
    FixedLogNormalization (Y1 : ℝ) (-2) (100169573 / 100000000) ∧
    FixedLogNormalization (1 - (Y1 : ℝ)) (-1) (299830427 / 200000000) := by
  norm_num [FixedLogNormalization, Y1, Set.mem_Icc]

def Y2 : ℚ := (2850869403 / 5000000000)

def Y2PrintedUpper : ℚ := (-357083933093 / 250000000000)

theorem Y2_normalizations :
    FixedLogNormalization (Y2 : ℝ) (-1) (2850869403 / 2500000000) ∧
    FixedLogNormalization (1 - (Y2 : ℝ)) (-2) (2149130597 / 1250000000) := by
  norm_num [FixedLogNormalization, Y2, Set.mem_Icc]

def Y3 : ℚ := (7966939383 / 10000000000)

def Y3PrintedUpper : ℚ := (-22901346323 / 15625000000)

theorem Y3_normalizations :
    FixedLogNormalization (Y3 : ℝ) (-1) (7966939383 / 5000000000) ∧
    FixedLogNormalization (1 - (Y3 : ℝ)) (-3) (2033060617 / 1250000000) := by
  norm_num [FixedLogNormalization, Y3, Set.mem_Icc]

def Y4 : ℚ := (4727245069 / 5000000000)

def Y4PrintedUpper : ℚ := (-1428335358167 / 1000000000000)

theorem Y4_normalizations :
    FixedLogNormalization (Y4 : ℝ) (-1) (4727245069 / 2500000000) ∧
    FixedLogNormalization (1 - (Y4 : ℝ)) (-5) (272754931 / 156250000) := by
  norm_num [FixedLogNormalization, Y4, Set.mem_Icc]

end InternalCatalan.Case1PointData

end

end OAI
