import OAI.Geometry.EinsteinFour.BianchiCurvature

namespace OAI

/-!
# The Hessian matrix on actual quaternionic Bianchi tensors

The energy pairing and the matrix-slot operator are transported through the
proved bijective parametrization. Thus the squared-operator term uses the
inverse energy metric automatically.
-/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators

/-- The normalized Hilbert--Schmidt pairing. -/
def Tensor.pairing (T U : Tensor) : ℝ := (∑ i, ∑ j, inner ℝ (T.matrix i j) (U.matrix i j)) / 6

private theorem parameters_add_matrix (S : Shape) (p k l p' k' l' : Vec) (i j : Fin 3) :
    (parameters S (p + p') (k + k') (l + l')).matrix i j =
      (parameters S p k l).matrix i j + (parameters S p' k' l').matrix i j := by
  fin_cases i <;> fin_cases j <;> simp [Tensor.matrix, parameters] <;> module

/-- The full inner product, not just the norm, is transported by the coordinate
map with metric `diag(5/3,5,1)`. -/
theorem parameters_pairing (S : Shape) (p k l p' k' l' : Vec) :
    (parameters S p k l).pairing (parameters S p' k' l') =
      (5 / 3) * inner ℝ p p' + 5 * inner ℝ k k' + inner ℝ l l' := by
  have hn : (parameters S (p + p') (k + k') (l + l')).squaredNorm =
      (parameters S p k l).squaredNorm +
      2 * (∑ i, ∑ j, inner ℝ ((parameters S p k l).matrix i j)
        ((parameters S p' k' l').matrix i j)) + (parameters S p' k' l').squaredNorm := by
    unfold Tensor.squaredNorm
    simp_rw [parameters_add_matrix, norm_add_sq_real]
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have h0 := parameters_energy S (p + p') (k + k') (l + l')
  have h1 := parameters_energy S p k l
  have h2 := parameters_energy S p' k' l'
  simp only [norm_add_sq_real] at h0
  unfold Tensor.pairing
  linarith

def curvatureActionP (S : Shape) (v : ℝ) (p k : Vec) : Vec :=
  v • (((4 / 5) * S.sigma) • p - ((12 / 5) * S.skewMoment) • k)

def curvatureActionK (S : Shape) (v : ℝ) (p k l : Vec) : Vec :=
  v • ((-(4 / 5) * S.skewMoment) • p - ((4 / 5) * S.sigma) • k - (1 / 5 : ℝ) • l)

def curvatureActionL (v : ℝ) (k : Vec) : Vec := (-v) • k

/-- The matrix-slot curvature operator on the concrete Bianchi space. -/
def curvatureAction (S : Shape) (v : ℝ) (p k l : Vec) : Tensor :=
  parameters S (curvatureActionP S v p k) (curvatureActionK S v p k l) (curvatureActionL v k)

/-- The transported operator is self-adjoint for the actual energy pairing. -/
theorem curvatureAction_pairing (S : Shape) (v : ℝ) (p k l p' k' l' : Vec) :
    (curvatureAction S v p k l).pairing (parameters S p' k' l') =
      v * ((4 / 3) * S.sigma * inner ℝ p p' -
        4 * S.skewMoment * (inner ℝ p k' + inner ℝ k p') -
        4 * S.sigma * inner ℝ k k' - inner ℝ k l' - inner ℝ l k') := by
  unfold curvatureAction
  rw [parameters_pairing]
  unfold curvatureActionP curvatureActionK curvatureActionL
  simp only [inner_sub_left, real_inner_smul_left]
  ring

/-- The quadratic form of the transported operator is exactly contraction
with the diagonal Weyl block, computed from matrix entries. -/
theorem curvatureAction_quadratic (S : Shape) (v : ℝ) (p k l : Vec) :
    (curvatureAction S v p k l).pairing (parameters S p k l) =
      curvatureContraction S v (parameters S p k l) := by
  rw [curvatureAction_pairing, curvatureContraction_parameters,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_comm p k, real_inner_comm k l]
  have hr : 8 * S.rho / Real.sqrt 3 = 8 * S.skewMoment := by
    rw [mul_div_assoc, S.rho_div_sqrt_three]
  rw [hr]
  ring

/-- The `B H⁻¹ B` term is the squared Hilbert--Schmidt norm of the actual
transported operator, with all tangent correlations retained. -/
theorem curvatureAction_energy (S : Shape) (v : ℝ) (p k l : Vec) :
    (curvatureAction S v p k l).squaredNorm / 6 =
      v ^ 2 * ((16 / 15) * ‖p‖ ^ 2 + (21 / 5) * ‖k‖ ^ 2 + ‖l‖ ^ 2 / 5 +
        (8 / 5) * S.skewMoment * inner ℝ p l + (8 / 5) * S.sigma * inner ℝ k l) := by
  unfold curvatureAction
  rw [parameters_energy]
  unfold curvatureActionP curvatureActionK curvatureActionL
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_sub_sq_real,
    inner_sub_left, real_inner_smul_left, real_inner_smul_right]
  linear_combination
    v ^ 2 * ((16 / 15) * ‖p‖ ^ 2 + (16 / 5) * ‖k‖ ^ 2) * S.sigma_skew_circle

/-- The first-derivative Hessian form expressed directly using concrete matrix
contractions and the actual inverse-energy-metric operator. -/
def hessianTensorForm (S : Shape) (v b : ℝ) (p k l : Vec) : ℝ :=
  (-42 - 3 * b ^ 2 - (10 / 3) * v ^ 2) * ((parameters S p k l).squaredNorm / 6) +
    75 * curvatureContraction S v (parameters S p k l) +
    (25 / 3) * squareCurvatureContraction S v (parameters S p k l) -
    (100 / 3) * ((curvatureAction S v p k l).squaredNorm / 6) + 5 * v ^ 2 * ‖p‖ ^ 2

/-- Equation (12) on real tangent vectors, with the precise off-diagonal
pairings and without assumptions about their signs. -/
theorem hessianTensor_matrix (S : Shape) (v b : ℝ) (p k l : Vec) :
    hessianTensorForm S v b p k l =
      (-70 - 5 * b ^ 2 + 100 * S.sigma * v - 25 * v ^ 2) * ‖p‖ ^ 2 +
      (-210 - 15 * b ^ 2 - 300 * S.sigma * v - 190 * v ^ 2) * ‖k‖ ^ 2 +
      (-42 - 3 * b ^ 2 - 10 * v ^ 2) * ‖l‖ ^ 2 -
      200 * Real.sqrt 3 * S.rho * v * inner ℝ p k -
      70 * S.rho * v ^ 2 / Real.sqrt 3 * inner ℝ p l -
      2 * (75 * v + 35 * S.sigma * v ^ 2) * inner ℝ k l := by
  unfold hessianTensorForm
  rw [parameters_energy, curvatureContraction_parameters,
    squareCurvatureContraction_parameters, curvatureAction_energy]
  unfold Shape.rho
  have hs : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp [hn]
  ring_nf
  rw [hs]
  ring

/-- The projected quadratic cost is bounded by the exact coefficients used in
equation (19) for the concrete Bianchi tensor. -/
theorem projection_cost_coefficients (S : Shape) {v : ℝ} (hv : 0 ≤ v)
    (y : ℝ) (p k l : Vec) :
    (7 / 12) * (4 + y) * ((parameters S p k l).squaredNorm / 6) -
      (5 / 4) * curvatureContraction S v (parameters S p k l) ≤
    QuarticEnergy.projectionCoefficient v y S.sigma S.rho * ((5 / 3) * ‖p‖ ^ 2) +
      Energy.defectCoefficient v y * ((parameters S p k l).squaredNorm / 6 -
        (5 / 3) * ‖p‖ ^ 2) := by
  have hs : S.sigma ≤ 1 := by nlinarith [S.sigma_rho_circle, sq_nonneg S.rho]
  rw [parameters_energy, curvatureContraction_parameters]
  convert HessianAlgebra.projection_bracket_bound (y := y) (ρ := S.rho) hv hs p k l using 1 <;> ring

private theorem binary_inner_nonneg (r h s : ℝ) (hr : 0 ≤ r) (hh : 0 ≤ h)
    (hd : s ^ 2 ≤ r * h) (p k : Vec) :
    0 ≤ r * ‖p‖ ^ 2 + 2 * s * inner ℝ p k + h * ‖k‖ ^ 2 := by
  have hi := abs_real_inner_le_norm p k
  by_cases hs : 0 ≤ s
  · have hform := quadratic_form_nonneg_of_det r h s hr hh hd ‖p‖ (-‖k‖)
    have hcross := mul_le_mul_of_nonneg_left (abs_le.mp hi).1 (show 0 ≤ 2 * s by positivity)
    nlinarith only [hform, hcross]
  · have hform := quadratic_form_nonneg_of_det r h s hr hh hd ‖p‖ ‖k‖
    have hcross := mul_le_mul_of_nonpos_left (abs_le.mp hi).2 (show 2 * s ≤ 0 by linarith)
    nlinarith only [hform, hcross]

/-- The unit normalized matrix-slot action is a contraction for the complete
Bianchi energy metric. -/
theorem normalized_curvature_bound (S : Shape) (p k l : Vec) :
    |(4 / 3) * S.sigma * ‖p‖ ^ 2 - 8 * S.skewMoment * inner ℝ p k -
      4 * S.sigma * ‖k‖ ^ 2 - 2 * inner ℝ k l| ≤
      (5 / 3) * ‖p‖ ^ 2 + 5 * ‖k‖ ^ 2 + ‖l‖ ^ 2 := by
  have hc := S.sigma_skew_circle
  have hslo : -1 ≤ S.sigma := by nlinarith [sq_nonneg S.skewMoment]
  have hshi : S.sigma ≤ 1 := by nlinarith [sq_nonneg S.skewMoment]
  have hminus := binary_inner_nonneg ((5 - 4 * S.sigma) / 3) (4 + 4 * S.sigma)
    (4 * S.skewMoment) (by linarith) (by linarith) (by nlinarith) p k
  have hplus := binary_inner_nonneg ((5 + 4 * S.sigma) / 3) (4 - 4 * S.sigma)
    (-4 * S.skewMoment) (by linarith) (by linarith) (by nlinarith) p k
  have hlminus := sq_nonneg ‖l - k‖
  have hlplus := sq_nonneg ‖l + k‖
  rw [norm_sub_sq_real, real_inner_comm k l] at hlminus
  rw [norm_add_sq_real, real_inner_comm k l] at hlplus
  apply abs_le.mpr
  constructor <;> linarith

/-- Operator bound stated using the actual matrix contraction and energy. -/
theorem curvatureContraction_abs_le (S : Shape) {v : ℝ} (hv : 0 ≤ v) (p k l : Vec) :
    |curvatureContraction S v (parameters S p k l)| ≤
      v * ((parameters S p k l).squaredNorm / 6) := by
  rw [curvatureContraction_parameters, parameters_energy]
  have hr : 8 * S.rho / Real.sqrt 3 = 8 * S.skewMoment := by
    rw [mul_div_assoc, S.rho_div_sqrt_three]
  rw [hr, abs_mul, abs_of_nonneg hv]
  exact mul_le_mul_of_nonneg_left (normalized_curvature_bound S p k l) hv

end
end PositiveEinsteinFour.Bianchi

end OAI
