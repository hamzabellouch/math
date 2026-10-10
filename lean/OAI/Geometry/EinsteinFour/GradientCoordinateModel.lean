import OAI.Geometry.EinsteinFour.GradientOperator

namespace OAI

/-! Fixed twelve real coordinates for the inner generators in the cost calculation. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

def costShape : Shape where
  s := ![-1, -1, 2]
  trace := by norm_num [Fin.sum_univ_three]
  square := by norm_num [Fin.sum_univ_three]

/-- Only this fixed frame is needed for the invariant real-vector cost. -/
def costParameters (v : Fin 3 → Vec) : Tensor := parameters costShape (v 0) (v 1) (v 2)

def generatorCoefficients (s : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![![3, 2, -2], ![2/3, 5/3, -2/3], ![-10/3, -10/3, -5/3]],
    ![![3, -2, 2], ![-2/3, 5/3, -2/3], ![10/3, -10/3, -5/3]],
    ![![1, 0, 0], ![0, 11/3, 4/3], ![0, 20/3, -5/3]]] s

def generatorCoordinates (s : Fin 3) (v : Fin 3 → Vec) : Fin 3 → Vec := fun i =>
  quaternion s (∑ j, generatorCoefficients s i j • v j)

private theorem generator_coordinates_0_0 (v : Fin 3 → Vec) (b : Fin 3) :
    rawGradientGenerator 0 (costParameters v).matrix 0 b =
      (costParameters (generatorCoordinates 0 v)).matrix 0 b := by
  ext j
  fin_cases b <;> fin_cases j <;>
    simp [rawGradientGenerator, rawMatrixRotation, costParameters, parameters,
      costShape, Tensor.matrix, generatorCoordinates, generatorCoefficients,
      difference, next, previous, rotation, quaternion, Fin.sum_univ_succ]
  all_goals ring

private theorem generator_coordinates_0_1 (v : Fin 3 → Vec) (b : Fin 3) :
    rawGradientGenerator 0 (costParameters v).matrix 1 b =
      (costParameters (generatorCoordinates 0 v)).matrix 1 b := by
  ext j
  fin_cases b <;> fin_cases j <;>
    simp [rawGradientGenerator, rawMatrixRotation, costParameters, parameters,
      costShape, Tensor.matrix, generatorCoordinates, generatorCoefficients,
      difference, next, previous, rotation, quaternion, Fin.sum_univ_succ]
  all_goals ring

private theorem generator_coordinates_0_2 (v : Fin 3 → Vec) (b : Fin 3) :
    rawGradientGenerator 0 (costParameters v).matrix 2 b =
      (costParameters (generatorCoordinates 0 v)).matrix 2 b := by
  ext j
  fin_cases b <;> fin_cases j <;>
    simp [rawGradientGenerator, rawMatrixRotation, costParameters, parameters,
      costShape, Tensor.matrix, generatorCoordinates, generatorCoefficients,
      difference, next, previous, rotation, quaternion, Fin.sum_univ_succ]
  all_goals ring

private theorem generator_coordinates_1_0 (v : Fin 3 → Vec) (b : Fin 3) :
    rawGradientGenerator 1 (costParameters v).matrix 0 b =
      (costParameters (generatorCoordinates 1 v)).matrix 0 b := by
  ext j
  fin_cases b <;> fin_cases j <;>
    simp [rawGradientGenerator, rawMatrixRotation, costParameters, parameters,
      costShape, Tensor.matrix, generatorCoordinates, generatorCoefficients,
      difference, next, previous, rotation, quaternion, Fin.sum_univ_succ]
  all_goals ring

private theorem generator_coordinates_1_1 (v : Fin 3 → Vec) (b : Fin 3) :
    rawGradientGenerator 1 (costParameters v).matrix 1 b =
      (costParameters (generatorCoordinates 1 v)).matrix 1 b := by
  ext j
  fin_cases b <;> fin_cases j <;>
    simp [rawGradientGenerator, rawMatrixRotation, costParameters, parameters,
      costShape, Tensor.matrix, generatorCoordinates, generatorCoefficients,
      difference, next, previous, rotation, quaternion, Fin.sum_univ_succ]
  all_goals ring

private theorem generator_coordinates_1_2 (v : Fin 3 → Vec) (b : Fin 3) :
    rawGradientGenerator 1 (costParameters v).matrix 2 b =
      (costParameters (generatorCoordinates 1 v)).matrix 2 b := by
  ext j
  fin_cases b <;> fin_cases j <;>
    simp [rawGradientGenerator, rawMatrixRotation, costParameters, parameters,
      costShape, Tensor.matrix, generatorCoordinates, generatorCoefficients,
      difference, next, previous, rotation, quaternion, Fin.sum_univ_succ]
  all_goals ring

private theorem generator_coordinates_2_0 (v : Fin 3 → Vec) (b : Fin 3) :
    rawGradientGenerator 2 (costParameters v).matrix 0 b =
      (costParameters (generatorCoordinates 2 v)).matrix 0 b := by
  ext j
  fin_cases b <;> fin_cases j <;>
    simp [rawGradientGenerator, rawMatrixRotation, costParameters, parameters,
      costShape, Tensor.matrix, generatorCoordinates, generatorCoefficients,
      difference, next, previous, rotation, quaternion, Fin.sum_univ_succ]
  all_goals ring

private theorem generator_coordinates_2_1 (v : Fin 3 → Vec) (b : Fin 3) :
    rawGradientGenerator 2 (costParameters v).matrix 1 b =
      (costParameters (generatorCoordinates 2 v)).matrix 1 b := by
  ext j
  fin_cases b <;> fin_cases j <;>
    simp [rawGradientGenerator, rawMatrixRotation, costParameters, parameters,
      costShape, Tensor.matrix, generatorCoordinates, generatorCoefficients,
      difference, next, previous, rotation, quaternion, Fin.sum_univ_succ]
  all_goals ring

private theorem generator_coordinates_2_2 (v : Fin 3 → Vec) (b : Fin 3) :
    rawGradientGenerator 2 (costParameters v).matrix 2 b =
      (costParameters (generatorCoordinates 2 v)).matrix 2 b := by
  ext j
  fin_cases b <;> fin_cases j <;>
    simp [rawGradientGenerator, rawMatrixRotation, costParameters, parameters,
      costShape, Tensor.matrix, generatorCoordinates, generatorCoefficients,
      difference, next, previous, rotation, quaternion, Fin.sum_univ_succ]
  all_goals ring

/-- Exact generator action in the fixed Bianchi coordinate frame. -/
theorem generator_coordinates (s : Fin 3) (v : Fin 3 → Vec) :
    rawGradientGenerator s (costParameters v).matrix =
      (costParameters (generatorCoordinates s v)).matrix := by
  funext a b
  fin_cases s <;> fin_cases a
  · exact generator_coordinates_0_0 v b
  · exact generator_coordinates_0_1 v b
  · exact generator_coordinates_0_2 v b
  · exact generator_coordinates_1_0 v b
  · exact generator_coordinates_1_1 v b
  · exact generator_coordinates_1_2 v b
  · exact generator_coordinates_2_0 v b
  · exact generator_coordinates_2_1 v b
  · exact generator_coordinates_2_2 v b

/-- The fixed coordinates cover every trace-free Bianchi tensor. -/
theorem exists_costParameters (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    ∃ v : Fin 3 → Vec, costParameters v = Z := by
  refine ⟨![radialCoordinate costShape Z, secondCoordinate costShape Z, thirdCoordinate costShape Z], ?_⟩
  exact parameters_reconstruction costShape Z hz hb


theorem costParameters_matrix_add (v w : Fin 3 → Vec) :
    (costParameters (v + w)).matrix =
      (costParameters v).matrix + (costParameters w).matrix := by
  funext a b
  fin_cases a <;> fin_cases b <;>
    simp [costParameters, parameters, Tensor.matrix, costShape, difference,
      next, previous, quaternion_add, smul_add]
  all_goals module

theorem costParameters_matrix_smul (r : ℝ) (v : Fin 3 → Vec) :
    (costParameters (r • v)).matrix = r • (costParameters v).matrix := by
  funext a b
  fin_cases a <;> fin_cases b <;>
    simp [costParameters, parameters, Tensor.matrix, costShape, difference,
      next, previous, quaternion_smul, smul_smul]
  all_goals module

theorem costParameters_matrix_neg (v : Fin 3 → Vec) :
    (costParameters (-v)).matrix = -(costParameters v).matrix := by
  simpa only [neg_one_smul] using costParameters_matrix_smul (-1) v

theorem costParameters_matrix_sub (v w : Fin 3 → Vec) :
    (costParameters (v - w)).matrix =
      (costParameters v).matrix - (costParameters w).matrix := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ w, costParameters_matrix_add,
    costParameters_matrix_smul]
  simp only [neg_one_smul, sub_eq_add_neg]

/-- The actual Frobenius norm in these twelve real coordinates. -/
def coordinateNorm (v : Fin 3 → Vec) : ℝ :=
  10 * ‖v 0‖ ^ 2 + 30 * ‖v 1‖ ^ 2 + 6 * ‖v 2‖ ^ 2

theorem costParameters_norm (v : Fin 3 → Vec) :
    (costParameters v).squaredNorm = coordinateNorm v := by
  have h := parameters_energy costShape (v 0) (v 1) (v 2)
  unfold costParameters coordinateNorm
  linarith

/-- The three quaternion coefficients of the total action on `(7-K)L`. -/
def costCoefficientCoordinates (s r : Fin 3) (v : Fin 3 → Vec) : Fin 3 → Vec :=
  if r = s then (7 : ℝ) • v - generatorCoordinates s (generatorCoordinates s v)
  else if r = next s then
    generatorCoordinates (previous s) v -
      generatorCoordinates s (generatorCoordinates (next s) v)
  else -generatorCoordinates (next s) v -
      generatorCoordinates s (generatorCoordinates (previous s) v)

theorem generator_norm_0 (v : Fin 3 → Vec) :
    coordinateNorm (generatorCoordinates 0 v) =
      170 * ‖v 0‖ ^ 2 + 190 * ‖v 1‖ ^ 2 + 70 * ‖v 2‖ ^ 2 +
      (320) * inner ℝ (v 0) (v 1) + (-80) * inner ℝ (v 0) (v 2) +
      (-80) * inner ℝ (v 1) (v 2) := by
  simp [coordinateNorm, generatorCoordinates, generatorCoefficients, quaternion,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_succ]
  ring

private theorem coefficient_norm_0_0 (v : Fin 3 → Vec) :
    coordinateNorm (costCoefficientCoordinates 0 0 v) =
      6880 * ‖v 0‖ ^ 2 + 8160 * ‖v 1‖ ^ 2 + 2304 * ‖v 2‖ ^ 2 +
      (12480) * inner ℝ (v 0) (v 1) + (-3840) * inner ℝ (v 0) (v 2) +
      (-3840) * inner ℝ (v 1) (v 2) := by
  simp [coordinateNorm, costCoefficientCoordinates, generatorCoordinates,
    generatorCoefficients, quaternion,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_succ]
  ring

private theorem coefficient_norm_0_1 (v : Fin 3 → Vec) :
    coordinateNorm (costCoefficientCoordinates 0 1 v) =
      1120 * ‖v 0‖ ^ 2 + 160 * ‖v 1‖ ^ 2 + 640 * ‖v 2‖ ^ 2 +
      (0) * inner ℝ (v 0) (v 1) + (0) * inner ℝ (v 0) (v 2) +
      (640) * inner ℝ (v 1) (v 2) := by
  simp [coordinateNorm, costCoefficientCoordinates, generatorCoordinates,
    generatorCoefficients, next, previous, quaternion,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_succ]
  ring

private theorem coefficient_norm_0_2 (v : Fin 3 → Vec) :
    coordinateNorm (costCoefficientCoordinates 0 2 v) =
      320 * ‖v 0‖ ^ 2 + 2560 * ‖v 1‖ ^ 2 + 640 * ‖v 2‖ ^ 2 +
      (1600) * inner ℝ (v 0) (v 1) + (320) * inner ℝ (v 0) (v 2) +
      (-320) * inner ℝ (v 1) (v 2) := by
  simp [coordinateNorm, costCoefficientCoordinates, generatorCoordinates,
    generatorCoefficients, next, previous, quaternion,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_succ]
  ring

theorem generator_norm_1 (v : Fin 3 → Vec) :
    coordinateNorm (generatorCoordinates 1 v) =
      170 * ‖v 0‖ ^ 2 + 190 * ‖v 1‖ ^ 2 + 70 * ‖v 2‖ ^ 2 +
      (-320) * inner ℝ (v 0) (v 1) + (80) * inner ℝ (v 0) (v 2) +
      (-80) * inner ℝ (v 1) (v 2) := by
  simp [coordinateNorm, generatorCoordinates, generatorCoefficients, quaternion,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_succ]
  ring

private theorem coefficient_norm_1_0 (v : Fin 3 → Vec) :
    coordinateNorm (costCoefficientCoordinates 1 0 v) =
      1120 * ‖v 0‖ ^ 2 + 160 * ‖v 1‖ ^ 2 + 640 * ‖v 2‖ ^ 2 +
      (0) * inner ℝ (v 0) (v 1) + (0) * inner ℝ (v 0) (v 2) +
      (640) * inner ℝ (v 1) (v 2) := by
  simp [coordinateNorm, costCoefficientCoordinates, generatorCoordinates,
    generatorCoefficients, next, previous, quaternion,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_succ]
  ring

private theorem coefficient_norm_1_1 (v : Fin 3 → Vec) :
    coordinateNorm (costCoefficientCoordinates 1 1 v) =
      6880 * ‖v 0‖ ^ 2 + 8160 * ‖v 1‖ ^ 2 + 2304 * ‖v 2‖ ^ 2 +
      (-12480) * inner ℝ (v 0) (v 1) + (3840) * inner ℝ (v 0) (v 2) +
      (-3840) * inner ℝ (v 1) (v 2) := by
  simp [coordinateNorm, costCoefficientCoordinates, generatorCoordinates,
    generatorCoefficients, quaternion,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_succ]
  ring

private theorem coefficient_norm_1_2 (v : Fin 3 → Vec) :
    coordinateNorm (costCoefficientCoordinates 1 2 v) =
      320 * ‖v 0‖ ^ 2 + 2560 * ‖v 1‖ ^ 2 + 640 * ‖v 2‖ ^ 2 +
      (-1600) * inner ℝ (v 0) (v 1) + (-320) * inner ℝ (v 0) (v 2) +
      (-320) * inner ℝ (v 1) (v 2) := by
  simp [coordinateNorm, costCoefficientCoordinates, generatorCoordinates,
    generatorCoefficients, next, previous, quaternion,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_succ]
  ring

theorem generator_norm_2 (v : Fin 3 → Vec) :
    coordinateNorm (generatorCoordinates 2 v) =
      10 * ‖v 0‖ ^ 2 + 670 * ‖v 1‖ ^ 2 + 70 * ‖v 2‖ ^ 2 +
      (0) * inner ℝ (v 0) (v 1) + (0) * inner ℝ (v 0) (v 2) +
      (160) * inner ℝ (v 1) (v 2) := by
  simp [coordinateNorm, generatorCoordinates, generatorCoefficients, quaternion,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_succ]
  ring

private theorem coefficient_norm_2_0 (v : Fin 3 → Vec) :
    coordinateNorm (costCoefficientCoordinates 2 0 v) =
      320 * ‖v 0‖ ^ 2 + 2560 * ‖v 1‖ ^ 2 + 640 * ‖v 2‖ ^ 2 +
      (1600) * inner ℝ (v 0) (v 1) + (320) * inner ℝ (v 0) (v 2) +
      (-320) * inner ℝ (v 1) (v 2) := by
  simp [coordinateNorm, costCoefficientCoordinates, generatorCoordinates,
    generatorCoefficients, next, previous, quaternion,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_succ]
  ring

private theorem coefficient_norm_2_1 (v : Fin 3 → Vec) :
    coordinateNorm (costCoefficientCoordinates 2 1 v) =
      320 * ‖v 0‖ ^ 2 + 2560 * ‖v 1‖ ^ 2 + 640 * ‖v 2‖ ^ 2 +
      (-1600) * inner ℝ (v 0) (v 1) + (-320) * inner ℝ (v 0) (v 2) +
      (-320) * inner ℝ (v 1) (v 2) := by
  simp [coordinateNorm, costCoefficientCoordinates, generatorCoordinates,
    generatorCoefficients, next, previous, quaternion,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_succ]
  ring

private theorem coefficient_norm_2_2 (v : Fin 3 → Vec) :
    coordinateNorm (costCoefficientCoordinates 2 2 v) =
      640 * ‖v 0‖ ^ 2 + 26880 * ‖v 1‖ ^ 2 + 2304 * ‖v 2‖ ^ 2 +
      (0) * inner ℝ (v 0) (v 1) + (0) * inner ℝ (v 0) (v 2) +
      (7680) * inner ℝ (v 1) (v 2) := by
  simp [coordinateNorm, costCoefficientCoordinates, generatorCoordinates,
    generatorCoefficients, quaternion,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_succ]
  ring

private theorem costCoefficient_norm_0 (v : Fin 3 → Vec) :
    64 * coordinateNorm (generatorCoordinates 0 v) +
      (∑ r : Fin 3, coordinateNorm (costCoefficientCoordinates 0 r v)) =
        84 * coordinateNorm v + 108 * coordinateNorm (generatorCoordinates 0 v) := by
  rw [Fin.sum_univ_three, generator_norm_0,
    coefficient_norm_0_0, coefficient_norm_0_1, coefficient_norm_0_2]
  unfold coordinateNorm
  ring

private theorem costCoefficient_norm_1 (v : Fin 3 → Vec) :
    64 * coordinateNorm (generatorCoordinates 1 v) +
      (∑ r : Fin 3, coordinateNorm (costCoefficientCoordinates 1 r v)) =
        84 * coordinateNorm v + 108 * coordinateNorm (generatorCoordinates 1 v) := by
  rw [Fin.sum_univ_three, generator_norm_1,
    coefficient_norm_1_0, coefficient_norm_1_1, coefficient_norm_1_2]
  unfold coordinateNorm
  ring

private theorem costCoefficient_norm_2 (v : Fin 3 → Vec) :
    64 * coordinateNorm (generatorCoordinates 2 v) +
      (∑ r : Fin 3, coordinateNorm (costCoefficientCoordinates 2 r v)) =
        84 * coordinateNorm v + 108 * coordinateNorm (generatorCoordinates 2 v) := by
  rw [Fin.sum_univ_three, generator_norm_2,
    coefficient_norm_2_0, coefficient_norm_2_1, coefficient_norm_2_2]
  unfold coordinateNorm
  ring

/-- The scalar matrix certificate yielding the real-vector curvature cost. -/
theorem costCoefficient_norm (s : Fin 3) (v : Fin 3 → Vec) :
    64 * coordinateNorm (generatorCoordinates s v) +
      (∑ r : Fin 3, coordinateNorm (costCoefficientCoordinates s r v)) =
        84 * coordinateNorm v + 108 * coordinateNorm (generatorCoordinates s v) := by
  fin_cases s
  · exact costCoefficient_norm_0 v
  · exact costCoefficient_norm_1 v
  · exact costCoefficient_norm_2 v


theorem row_norm_0 (v : Fin 3 → Vec) :
    (∑ b, ‖(costParameters v).matrix 0 b‖ ^ 2) =
      2 * ‖v 0‖ ^ 2 + 14 * ‖v 1‖ ^ 2 + 2 * ‖v 2‖ ^ 2 -
        8 * inner ℝ (v 0) (v 1) + 2 * inner ℝ (v 0) (v 2) +
        2 * inner ℝ (v 1) (v 2) := by
  simp [costParameters, parameters, Tensor.matrix, costShape, difference,
    next, previous, quaternion, EuclideanSpace.real_norm_sq_eq,
    PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_succ]
  ring

theorem row_norm_1 (v : Fin 3 → Vec) :
    (∑ b, ‖(costParameters v).matrix 1 b‖ ^ 2) =
      2 * ‖v 0‖ ^ 2 + 14 * ‖v 1‖ ^ 2 + 2 * ‖v 2‖ ^ 2 +
        8 * inner ℝ (v 0) (v 1) - 2 * inner ℝ (v 0) (v 2) +
        2 * inner ℝ (v 1) (v 2) := by
  simp [costParameters, parameters, Tensor.matrix, costShape, difference,
    next, previous, quaternion, EuclideanSpace.real_norm_sq_eq,
    PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_succ]
  ring

theorem row_norm_2 (v : Fin 3 → Vec) :
    (∑ b, ‖(costParameters v).matrix 2 b‖ ^ 2) =
      6 * ‖v 0‖ ^ 2 + 2 * ‖v 1‖ ^ 2 + 2 * ‖v 2‖ ^ 2 -
        4 * inner ℝ (v 1) (v 2) := by
  simp [costParameters, parameters, Tensor.matrix, costShape, difference,
    next, previous, quaternion, EuclideanSpace.real_norm_sq_eq,
    PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_succ]
  ring

end
end PositiveEinsteinFour.Bianchi

end OAI
