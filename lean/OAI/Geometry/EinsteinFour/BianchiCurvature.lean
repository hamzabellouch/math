import OAI.Geometry.EinsteinFour.Bianchi
import OAI.Geometry.EinsteinFour.HessianAlgebra

namespace OAI

/-!
# Curvature contractions of the concrete Bianchi tensor

The normalized spectral moments and the matrix-slot contraction are computed
from the actual symmetric matrix of Euclidean four-vectors in `Bianchi`.
-/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators

/-- Normalized cubic spectral moment. -/
def Shape.sigma (S : Shape) : ℝ := (∑ i, S.s i ^ 3) / 6

/-- Rational form of `ρ / √3`. -/
def Shape.skewMoment (S : Shape) : ℝ := (∑ i, S.s i ^ 2 * difference S.s i) / 18

/-- The oriented companion spectral moment. -/
def Shape.rho (S : Shape) : ℝ := Real.sqrt 3 * S.skewMoment

/-- The normalized quarter-turn spectral vector. -/
def Shape.tilde (S : Shape) (i : Fin 3) : ℝ := difference S.s i / Real.sqrt 3

theorem Shape.trace_coordinates (S : Shape) : S.s 2 = -S.s 0 - S.s 1 := by
  have h := S.trace
  simp [Fin.sum_univ_succ] at h
  linarith

theorem Shape.norm_coordinates (S : Shape) :
    S.s 0 ^ 2 + S.s 0 * S.s 1 + S.s 1 ^ 2 = 3 := by
  have h := S.square
  simp [Fin.sum_univ_succ, S.trace_coordinates] at h
  nlinarith

theorem Shape.sigma_skew_circle (S : Shape) : S.sigma ^ 2 + 3 * S.skewMoment ^ 2 = 1 := by
  have h := S.norm_coordinates
  unfold Shape.sigma Shape.skewMoment
  simp [Fin.sum_univ_succ, difference, next, previous]
  rw [S.trace_coordinates]
  linear_combination
    (S.s 0 ^ 4 + 2 * S.s 0 ^ 3 * S.s 1 + 3 * S.s 0 ^ 2 * S.s 1 ^ 2 +
      3 * S.s 0 ^ 2 + 2 * S.s 0 * S.s 1 ^ 3 + 3 * S.s 0 * S.s 1 +
      S.s 1 ^ 4 + 3 * S.s 1 ^ 2 + 9) / 27 * h

/-- The exact normalized identity used by every spectral matrix estimate. -/
theorem Shape.sigma_rho_circle (S : Shape) : S.rho ^ 2 = 1 - S.sigma ^ 2 := by
  unfold Shape.rho
  rw [mul_pow, Real.sq_sqrt (by norm_num)]
  linarith [S.sigma_skew_circle]

theorem Shape.rho_div_sqrt_three (S : Shape) : S.rho / Real.sqrt 3 = S.skewMoment := by
  unfold Shape.rho
  have hn : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp [hn]

theorem Shape.rho_eq_source (S : Shape) :
    S.rho = (∑ i, S.s i ^ 2 * S.tilde i) / 6 := by
  unfold Shape.rho Shape.skewMoment Shape.tilde
  have hs : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  field_simp [hn]
  ring_nf
  rw [hs]
  ring

/-- The normalized trace-free square is expanded in the two spectral vectors. -/
theorem Shape.square_decomposition (S : Shape) (i : Fin 3) :
    S.s i ^ 2 - 2 = S.sigma * S.s i + S.rho * S.tilde i := by
  have h := S.norm_coordinates
  have hr : S.rho * S.tilde i = S.skewMoment * difference S.s i := by
    unfold Shape.rho Shape.tilde
    have hn : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp [hn]
  rw [hr]
  unfold Shape.sigma Shape.skewMoment
  simp [Fin.sum_univ_succ, difference, next, previous]
  rw [S.trace_coordinates]
  fin_cases i
  · norm_num at *
    rw [S.trace_coordinates]
    linear_combination -(S.s 0 ^ 2 - 2 * S.s 0 * S.s 1 - 2 * S.s 1 ^ 2 - 6) / 9 * h
  · norm_num at *
    rw [S.trace_coordinates]
    linear_combination (2 * S.s 0 ^ 2 + 2 * S.s 0 * S.s 1 - S.s 1 ^ 2 + 6) / 9 * h
  · norm_num at *
    rw [S.trace_coordinates]
    linear_combination -(S.s 0 ^ 2 + 4 * S.s 0 * S.s 1 + S.s 1 ^ 2 - 6) / 9 * h

/-- Cubic moment in the unnormalized quarter-turn vector. -/
theorem Shape.mixed_cubic (S : Shape) :
    (∑ i, S.s i * difference S.s i ^ 2) = -18 * S.sigma := by
  unfold Shape.sigma
  simp [Fin.sum_univ_succ, difference, next, previous]
  rw [S.trace_coordinates]
  ring

/-- Direct matrix-slot quadratic contraction with diagonal Weyl block `v*s`.
The second sum is the off-diagonal contribution, because the spectral trace
vanishes. -/
def curvatureContraction (S : Shape) (v : ℝ) (T : Tensor) : ℝ :=
  (v / 6) * ((∑ i, S.s i * ‖T.diagonal i‖ ^ 2) - ∑ i, S.s i * ‖T.off i‖ ^ 2)

/-- This is the contraction of the actual three-by-three matrix, not an
independent scalar surrogate. -/
theorem curvatureContraction_eq_matrix (S : Shape) (v : ℝ) (T : Tensor) :
    curvatureContraction S v T = (v / 6) * ∑ i, ∑ j, S.s i * ‖T.matrix i j‖ ^ 2 := by
  have ht := S.trace
  simp [Fin.sum_univ_succ] at ht
  unfold curvatureContraction
  simp [Tensor.matrix, Fin.sum_univ_succ]
  left
  linear_combination
    -(‖T.off 0‖ ^ 2 + ‖T.off 1‖ ^ 2 + ‖T.off 2‖ ^ 2) * ht

private theorem diagonal_contraction (S : Shape) (p k l : Vec) :
    (∑ i, S.s i * ‖(parameters S p k l).diagonal i‖ ^ 2) =
      (∑ i, S.s i ^ 3) * ‖p‖ ^ 2 -
      2 * (∑ i, S.s i ^ 2 * difference S.s i) * inner ℝ p k +
      (∑ i, S.s i * difference S.s i ^ 2) * ‖k‖ ^ 2 := by
  change (∑ i, S.s i * ‖S.s i • p - difference S.s i • k‖ ^ 2) = _
  simp only [Fin.sum_univ_succ, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_smul_left, real_inner_smul_right]
  ring

private theorem off_contraction (S : Shape) (p k l : Vec) :
    (∑ i, S.s i * ‖(parameters S p k l).off i‖ ^ 2) =
      (∑ i, S.s i) * ‖l‖ ^ 2 + 2 * (∑ i, S.s i ^ 2) * inner ℝ l k +
      (2 / 3) * (∑ i, S.s i * difference S.s i) * inner ℝ l p +
      (∑ i, S.s i ^ 3) * ‖k‖ ^ 2 +
      (2 / 3) * (∑ i, S.s i ^ 2 * difference S.s i) * inner ℝ k p +
      (1 / 9) * (∑ i, S.s i * difference S.s i ^ 2) * ‖p‖ ^ 2 := by
  change (∑ i, S.s i * ‖-quaternion i (l + S.s i • k + (difference S.s i / 3) • p)‖ ^ 2) = _
  simp only [norm_neg, quaternion_norm, Fin.sum_univ_succ, norm_add_sq_real,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_add_left,
    real_inner_smul_left, real_inner_smul_right]
  ring

/-- The `B/v` matrix in Section 5 follows from the concrete parameter tensor.
All three variables remain real tangent four-vectors. -/
theorem curvatureContraction_parameters (S : Shape) (v : ℝ) (p k l : Vec) :
    curvatureContraction S v (parameters S p k l) =
      v * ((4 / 3) * S.sigma * ‖p‖ ^ 2 -
        8 * S.rho / Real.sqrt 3 * inner ℝ p k -
        4 * S.sigma * ‖k‖ ^ 2 - 2 * inner ℝ k l) := by
  unfold curvatureContraction
  rw [diagonal_contraction, off_contraction, S.trace, S.square,
    difference_orthogonal, S.mixed_cubic, real_inner_comm p k, real_inner_comm k l]
  have hc : (∑ i, S.s i ^ 3) = 6 * S.sigma := by unfold Shape.sigma; ring
  have hd : (∑ i, S.s i ^ 2 * difference S.s i) = 18 * S.skewMoment := by
    unfold Shape.skewMoment
    ring
  rw [hc, hd]
  have hr : 8 * S.rho / Real.sqrt 3 = 8 * S.skewMoment := by rw [mul_div_assoc, S.rho_div_sqrt_three]
  rw [hr]
  ring

/-- Rational form of the same trace-free square decomposition. -/
theorem Shape.squareWeight_eq (S : Shape) (i : Fin 3) :
    S.s i ^ 2 - 2 = S.sigma * S.s i + S.skewMoment * difference S.s i := by
  have h := S.square_decomposition i
  have hr : S.rho * S.tilde i = S.skewMoment * difference S.s i := by
    unfold Shape.rho Shape.tilde
    have hn : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp [hn]
  rwa [hr] at h

/-- The normalized eigenvalues of the trace-free square of the Weyl block. -/
def Shape.squareWeight (S : Shape) (i : Fin 3) : ℝ := S.s i ^ 2 - 2

private theorem cube_sum (S : Shape) : (∑ i, S.s i ^ 3) = 6 * S.sigma := by
  unfold Shape.sigma
  ring

private theorem mixed_cube_sum (S : Shape) :
    (∑ i, S.s i ^ 2 * difference S.s i) = 18 * S.skewMoment := by
  unfold Shape.skewMoment
  ring

private theorem difference_cube_sum (S : Shape) :
    (∑ i, difference S.s i ^ 3) = -54 * S.skewMoment := by
  calc
    _ = -3 * ∑ i, S.s i ^ 2 * difference S.s i := by
      simp [difference, next, previous, Fin.sum_univ_succ]
      ring
    _ = _ := by rw [mixed_cube_sum]; ring

private theorem squareWeight_moments (S : Shape) :
    (∑ i, S.squareWeight i) = 0 ∧
    (∑ i, S.squareWeight i * S.s i) = 6 * S.sigma ∧
    (∑ i, S.squareWeight i * difference S.s i) = 18 * S.skewMoment ∧
    (∑ i, S.squareWeight i * S.s i ^ 2) = 6 ∧
    (∑ i, S.squareWeight i * S.s i * difference S.s i) = 0 ∧
    (∑ i, S.squareWeight i * difference S.s i ^ 2) = -18 := by
  have hsq : ∑ i, S.squareWeight i = 0 := by
    unfold Shape.squareWeight
    simp only [Finset.sum_sub_distrib, S.square, Finset.sum_const, Finset.card_fin]
    norm_num
  have hs : (∑ i, S.squareWeight i * S.s i) = 6 * S.sigma := by
    calc
      _ = (∑ i, S.s i ^ 3) - 2 * ∑ i, S.s i := by
        simp only [Shape.squareWeight, Fin.sum_univ_succ]
        ring
      _ = _ := by rw [cube_sum, S.trace]; ring
  have hd : (∑ i, S.squareWeight i * difference S.s i) = 18 * S.skewMoment := by
    calc
      _ = (∑ i, S.s i ^ 2 * difference S.s i) - 2 * ∑ i, difference S.s i := by
        simp only [Shape.squareWeight, Fin.sum_univ_succ]
        ring
      _ = _ := by rw [mixed_cube_sum, difference_sum]; ring
  have hs2 : (∑ i, S.squareWeight i * S.s i ^ 2) = 6 := by
    calc
      _ = S.sigma * (∑ i, S.s i ^ 3) +
          S.skewMoment * ∑ i, S.s i ^ 2 * difference S.s i := by
        simp_rw [Shape.squareWeight, S.squareWeight_eq]
        simp only [Fin.sum_univ_succ]
        ring
      _ = _ := by rw [cube_sum, mixed_cube_sum]; nlinarith [S.sigma_skew_circle]
  have hsd : (∑ i, S.squareWeight i * S.s i * difference S.s i) = 0 := by
    calc
      _ = S.sigma * (∑ i, S.s i ^ 2 * difference S.s i) +
          S.skewMoment * ∑ i, S.s i * difference S.s i ^ 2 := by
        simp_rw [Shape.squareWeight, S.squareWeight_eq]
        simp only [Fin.sum_univ_succ]
        ring
      _ = _ := by rw [mixed_cube_sum, S.mixed_cubic]; ring
  have hd2 : (∑ i, S.squareWeight i * difference S.s i ^ 2) = -18 := by
    calc
      _ = S.sigma * (∑ i, S.s i * difference S.s i ^ 2) +
          S.skewMoment * ∑ i, difference S.s i ^ 3 := by
        simp_rw [Shape.squareWeight, S.squareWeight_eq]
        simp only [Fin.sum_univ_succ]
        ring
      _ = _ := by rw [S.mixed_cubic, difference_cube_sum]; nlinarith [S.sigma_skew_circle]
  exact ⟨hsq, hs, hd, hs2, hsd, hd2⟩

/-- The actual matrix-slot contraction with `N = (T²)₀`. -/
def squareCurvatureContraction (S : Shape) (v : ℝ) (T : Tensor) : ℝ :=
  (v ^ 2 / 6) * ((∑ i, S.squareWeight i * ‖T.diagonal i‖ ^ 2) -
    ∑ i, S.squareWeight i * ‖T.off i‖ ^ 2)

private theorem weighted_diagonal_contraction
    (S : Shape) (w : Fin 3 → ℝ) (p k l : Vec) :
    (∑ i, w i * ‖(parameters S p k l).diagonal i‖ ^ 2) =
      (∑ i, w i * S.s i ^ 2) * ‖p‖ ^ 2 -
      2 * (∑ i, w i * S.s i * difference S.s i) * inner ℝ p k +
      (∑ i, w i * difference S.s i ^ 2) * ‖k‖ ^ 2 := by
  change (∑ i, w i * ‖S.s i • p - difference S.s i • k‖ ^ 2) = _
  simp only [Fin.sum_univ_succ, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_smul_left, real_inner_smul_right]
  ring

private theorem weighted_off_contraction
    (S : Shape) (w : Fin 3 → ℝ) (p k l : Vec) :
    (∑ i, w i * ‖(parameters S p k l).off i‖ ^ 2) =
      (∑ i, w i) * ‖l‖ ^ 2 + 2 * (∑ i, w i * S.s i) * inner ℝ l k +
      (2 / 3) * (∑ i, w i * difference S.s i) * inner ℝ l p +
      (∑ i, w i * S.s i ^ 2) * ‖k‖ ^ 2 +
      (2 / 3) * (∑ i, w i * S.s i * difference S.s i) * inner ℝ k p +
      (1 / 9) * (∑ i, w i * difference S.s i ^ 2) * ‖p‖ ^ 2 := by
  change (∑ i, w i * ‖-quaternion i (l + S.s i • k + (difference S.s i / 3) • p)‖ ^ 2) = _
  simp only [norm_neg, quaternion_norm, Fin.sum_univ_succ, norm_add_sq_real,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_add_left,
    real_inner_smul_left, real_inner_smul_right]
  ring

/-- The `C_N/v²` matrix in Section 5 from the concrete four-vector tensor. -/
theorem squareCurvatureContraction_parameters (S : Shape) (v : ℝ) (p k l : Vec) :
    squareCurvatureContraction S v (parameters S p k l) =
      v ^ 2 * ((4 / 3) * ‖p‖ ^ 2 - 2 * S.rho / Real.sqrt 3 * inner ℝ p l -
        4 * ‖k‖ ^ 2 - 2 * S.sigma * inner ℝ k l) := by
  obtain ⟨h0, hs, hd, hs2, hsd, hd2⟩ := squareWeight_moments S
  unfold squareCurvatureContraction
  rw [weighted_diagonal_contraction, weighted_off_contraction,
    h0, hs, hd, hs2, hsd, hd2, real_inner_comm p l, real_inner_comm k l]
  have hr : 2 * S.rho / Real.sqrt 3 = 2 * S.skewMoment := by rw [mul_div_assoc, S.rho_div_sqrt_three]
  rw [hr]
  ring

end
end PositiveEinsteinFour.Bianchi

end OAI
