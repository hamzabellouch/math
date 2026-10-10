import OAI.Geometry.EinsteinFour.RealVectorProjection
import OAI.Geometry.EinsteinFour.GradientCoordinates
import OAI.Geometry.EinsteinFour.CoupledOperator

namespace OAI

/-! The second real-vector projection identity in actual tensor coordinates. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian HighestHessian

/-- Frobenius norm of an arbitrary matrix of real four-vectors. -/
def rawNorm (Z : RawGradient) : ℝ := ∑ b, ∑ c, ‖Z b c‖ ^ 2

@[simp] theorem rawNorm_matrix (Z : Tensor) : rawNorm Z.matrix = Z.squaredNorm := rfl

theorem rawNorm_smul (r : ℝ) (Z : RawGradient) :
    rawNorm (r • Z) = r ^ 2 * rawNorm Z := by
  simp only [rawNorm, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, ← Finset.mul_sum]

/-- Quaternion coefficient of the total derivative of `(7-K)L`. -/
def rawCostCoefficient (s r : Fin 3) (Z : RawGradient) : RawGradient :=
  if r = s then (7 : ℝ) • Z - rawGradientGenerator s (rawGradientGenerator s Z)
  else if r = next s then
    rawGradientGenerator (previous s) Z -
      rawGradientGenerator s (rawGradientGenerator (next s) Z)
  else -rawGradientGenerator (next s) Z -
      rawGradientGenerator s (rawGradientGenerator (previous s) Z)

theorem rawCostCoefficient_coordinates (s r : Fin 3) (v : Fin 3 → Vec) :
    rawCostCoefficient s r (costParameters v).matrix =
      (costParameters (costCoefficientCoordinates s r v)).matrix := by
  unfold rawCostCoefficient costCoefficientCoordinates
  split_ifs <;>
    simp only [costParameters_matrix_sub, costParameters_matrix_smul,
      costParameters_matrix_neg, generator_coordinates]

/-- The coefficient identity uses the actual twelve Bianchi coordinates. -/
theorem rawCostCoefficient_norm (s : Fin 3) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    64 * rawNorm (rawGradientGenerator s Z.matrix) +
      (∑ r : Fin 3, rawNorm (rawCostCoefficient s r Z.matrix)) =
        84 * Z.squaredNorm + 108 * rawNorm (rawGradientGenerator s Z.matrix) := by
  obtain ⟨v, rfl⟩ := exists_costParameters Z hz hb
  simp_rw [rawCostCoefficient_coordinates, generator_coordinates, rawNorm_matrix,
    costParameters_norm]
  exact costCoefficient_norm s v

/-- A real outer quaternion combination, keeping all inner correlations. -/
def quaternionCombination (a : Vec) (Z : RawGradient)
    (C : Fin 3 → RawGradient) : Hessian := fun i j b c =>
  a i * Z b c j + ∑ s : Fin 3, quaternion s a i * C s b c j

private theorem quaternionCombination_slice_norm (a : Vec) (Z : RawGradient)
    (C : Fin 3 → RawGradient) (b c : Fin 3) (j : Fin 4) :
    (∑ i : Fin 4, quaternionCombination a Z C i j b c ^ 2) =
      ‖a‖ ^ 2 * (Z b c j ^ 2 + ∑ s : Fin 3, C s b c j ^ 2) := by
  have h := quaternion_combination_norm_sq a (Z b c j) (fun s => C s b c j)
  simpa only [quaternionCombination, mul_comm] using h

/-- No product assumption is made on the inner plus and minus factors. -/
theorem quaternionCombination_norm (a : Vec) (Z : RawGradient)
    (C : Fin 3 → RawGradient) :
    hessianNormSq (quaternionCombination a Z C) =
      ‖a‖ ^ 2 * (rawNorm Z + ∑ s : Fin 3, rawNorm (C s)) := by
  calc
    _ = ∑ b, ∑ c, ∑ j : Fin 4, ∑ i : Fin 4,
        quaternionCombination a Z C i j b c ^ 2 := by
      unfold hessianNormSq
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ c, ∑ j : Fin 4,
        ‖a‖ ^ 2 * (Z b c j ^ 2 + ∑ s : Fin 3, C s b c j ^ 2) := by
      simp_rw [quaternionCombination_slice_norm]
    _ = _ := by
      simp only [rawNorm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three,
        Fin.sum_univ_four]
      ring


theorem weightPlusPart_linearCombination (a : Vec) (Z : Tensor) :
    weightPlusPart a Z = (1 / 12 : ℝ) •
      ((7 : ℝ) • rawWeight a Z.matrix -
        ∑ r : Fin 3, rawWeight (quaternion r a) (rawGradientGenerator r Z.matrix)) := by
  funext i j b c
  simp [weightPlusPart, weightCoupling, rawWeight, Fin.sum_univ_three]
  ring

/-- The total generator is evaluated before taking its norm. -/
theorem totalPlus_weightPlusPart (s : Fin 3) (a : Vec) (Z : Tensor) :
    totalPlus s (weightPlusPart a Z) = (1 / 12 : ℝ) •
      quaternionCombination a ((8 : ℝ) • rawGradientGenerator s Z.matrix)
        (fun r => rawCostCoefficient s r Z.matrix) := by
  rw [weightPlusPart_linearCombination, totalPlus_smul]
  congr 1
  rw [sub_eq_add_neg,
    ← neg_one_smul ℝ (∑ r : Fin 3,
      rawWeight (quaternion r a) (rawGradientGenerator r Z.matrix))]
  simp only [Fin.sum_univ_three, totalPlus_add, totalPlus_smul, totalPlus_rawWeight]
  funext i j b c
  fin_cases s <;> fin_cases i <;>
    simp [rawWeight, quaternionCombination, rawCostCoefficient, quaternion,
      next, previous, Fin.sum_univ_three]
  all_goals ring

private theorem hessianNormSq_smul (r : ℝ) (X : Hessian) :
    hessianNormSq (r • X) = r ^ 2 * hessianNormSq X := by
  change (∑ a, ∑ b, ∑ i, ∑ j, (r * X i j a b) ^ 2) = _
  simp only [mul_pow, hessianNormSq, ← Finset.mul_sum]

/-- The real-vector identity is proved separately for each actual generator. -/
theorem totalPlus_weightPlusPart_norm (s : Fin 3) (a : Vec) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    hessianNormSq (totalPlus s (weightPlusPart a Z)) = ‖a‖ ^ 2 *
      ((7 / 12) * Z.squaredNorm +
        (3 / 4) * rawNorm (rawGradientGenerator s Z.matrix)) := by
  rw [totalPlus_weightPlusPart, hessianNormSq_smul, quaternionCombination_norm,
    rawNorm_smul]
  norm_num only [show (8 : ℝ) ^ 2 = 64 by norm_num]
  rw [rawCostCoefficient_norm s Z hz hb]
  ring

/-- The weighted trace-free contraction, with the source's positive one-half
coefficient and without a partial-trace assumption. -/
theorem totalPlus_weightPlusPart_curvature (t : Fin 3 → ℝ)
    (ht : ∑ s, t s = 0) (a : Vec) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    -(∑ s, t s * hessianNormSq (totalPlus s (weightPlusPart a Z))) / 60 =
      (1 / 2 : ℝ) * ‖a‖ ^ 2 *
        (-(∑ s, t s * rawNorm (rawGradientGenerator s Z.matrix)) / 40) := by
  simp_rw [totalPlus_weightPlusPart_norm _ a Z hz hb]
  have htrace := congrArg (fun z : ℝ => z * (‖a‖ ^ 2 * Z.squaredNorm)) ht
  simp only [Fin.sum_univ_three] at htrace ⊢
  nlinarith


/-- The second real-vector identity ends in the actual matrix-slot contraction. -/
theorem totalPlus_weightPlusPart_matrixCost (t : Fin 3 → ℝ)
    (ht : ∑ s, t s = 0) (a : Vec) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    -(∑ s, t s * hessianNormSq (totalPlus s (weightPlusPart a Z))) / 60 =
      (1 / 2 : ℝ) * ‖a‖ ^ 2 *
        (∑ s, t s * (∑ b, ‖Z.matrix s b‖ ^ 2)) := by
  rw [totalPlus_weightPlusPart_curvature t ht a Z hz hb]
  unfold rawNorm
  rw [weighted_generator_matrixForm t ht Z hz hb]


/-- The raw inner energy is the Bianchi Casimir. -/
theorem rawGenerator_energy (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ s : Fin 3, rawNorm (rawGradientGenerator s Z.matrix)) = 35 * Z.squaredNorm := by
  calc
    _ = ∑ a, ∑ b, ∑ s : Fin 3, ‖gradientGenerator s Z a b‖ ^ 2 := by
      simp only [rawNorm, rawGradientGenerator_matrix]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := gradientGenerator_energy Z hz hb

/-- The explicit real plus part has actual total-plus energy forty-eight. -/
theorem weightPlusPart_plus_energy (a : Vec) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ s : Fin 3, hessianNormSq (totalPlus s (weightPlusPart a Z))) =
      48 * hessianNormSq (weightPlusPart a Z) := by
  calc
    _ = ‖a‖ ^ 2 * ((7 / 4) * Z.squaredNorm +
        (3 / 4) * ∑ s : Fin 3, rawNorm (rawGradientGenerator s Z.matrix)) := by
      simp only [totalPlus_weightPlusPart_norm _ a Z hz hb, Fin.sum_univ_three]
      ring
    _ = _ := by rw [rawGenerator_energy Z hz hb, weightPlusPart_norm a Z hz hb]; ring

/-- This is the same explicit polynomial as the self-adjoint coupled operator. -/
theorem weightPlusPart_eq_plusPolynomial (a : Vec) (Z : Tensor) :
    weightPlusPart a Z = plusPolynomial (weightTensor a Z) := by
  rw [weightPlusPart_linearCombination]
  change _ = plusPolynomial (rawWeight a Z.matrix)
  rw [plusPolynomial, coupledOperator_rawWeight]

end
end PositiveEinsteinFour.Bianchi

end OAI
