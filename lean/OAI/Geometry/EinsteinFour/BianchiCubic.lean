import OAI.Geometry.EinsteinFour.BianchiHessian

namespace OAI

/-!
# The sharp cubic contraction in a normalized diagonal frame

The contraction is defined from the actual symmetric matrix of four-vectors.
The displayed diagonal-frame hypothesis is the pointwise spectral-frame
condition used in the curvature calculation, and is not a differential-geometric input.
-/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators

def normalizedCurvatureForm (S : Shape) (p k l : Vec) : ℝ :=
  (4 / 3) * S.sigma * ‖p‖ ^ 2 - 8 * S.skewMoment * inner ℝ p k -
    4 * S.sigma * ‖k‖ ^ 2 - 2 * inner ℝ k l

/-- The distinguished tangent component loses one fifth of its energy in
this quadratic contraction. The other components retain the full bound. -/
theorem distinguished_component_bound (S : Shape) (a p k l : Vec) (ν : ℝ)
    (ha : ‖a‖ = 1) (hap : inner ℝ a p = ν) (hak : inner ℝ a k = 0) :
    |normalizedCurvatureForm S p k l| ≤
      (5 / 3) * ‖p‖ ^ 2 + 5 * ‖k‖ ^ 2 + ‖l‖ ^ 2 - ν ^ 2 / 3 := by
  let u := p - ν • a
  have hup : ‖p‖ ^ 2 = ν ^ 2 + ‖u‖ ^ 2 := by
    have hu : ‖u‖ ^ 2 = ‖p‖ ^ 2 - ν ^ 2 := by
      dsimp [u]
      rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
        real_inner_smul_right, real_inner_comm a p, hap, ha]
      ring
    linarith
  have huk : inner ℝ p k = inner ℝ u k := by
    dsimp [u]
    rw [inner_sub_left, real_inner_smul_left, hak]
    ring
  have hform : normalizedCurvatureForm S p k l = (4 / 3) * S.sigma * ν ^ 2 + normalizedCurvatureForm S u k l := by
    unfold normalizedCurvatureForm
    rw [hup, huk]
    ring
  have hs : |S.sigma| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [S.sigma_skew_circle, sq_nonneg S.skewMoment]
  have hrad : |(4 / 3) * S.sigma * ν ^ 2| ≤ (4 / 3) * ν ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3), abs_of_nonneg (sq_nonneg ν)]
    nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg ν)]
  have hrest : |normalizedCurvatureForm S u k l| ≤ (5 / 3) * ‖u‖ ^ 2 + 5 * ‖k‖ ^ 2 + ‖l‖ ^ 2 :=
    normalized_curvature_bound S u k l
  rw [hform]
  calc
    _ ≤ |(4 / 3) * S.sigma * ν ^ 2| + |normalizedCurvatureForm S u k l| := abs_add_le _ _
    _ ≤ (4 / 3) * ν ^ 2 + ((5 / 3) * ‖u‖ ^ 2 + 5 * ‖k‖ ^ 2 + ‖l‖ ^ 2) := add_le_add hrad hrest
    _ = _ := by rw [hup]; ring

/-- The literal matrix contraction `tr(Z_a Σ_j Z_j²)/6`. Each inner product
contracts the derivative (four-vector) index. -/
def cubicContraction (a : Vec) (T : Tensor) : ℝ :=
  (∑ i, ∑ j, ∑ k, inner ℝ a (T.matrix i j) *
    inner ℝ (T.matrix j k) (T.matrix k i)) / 6

/-- In the diagonalizing frame for `Z_a`, the cubic contraction is the
normalized matrix-slot quadratic contraction times its scale. -/
theorem cubicContraction_diagonal (S : Shape) (a : Vec) (T : Tensor) (ν : ℝ)
    (hdiag : ∀ i j, inner ℝ a (T.matrix i j) = if i = j then ν * S.s i else 0) :
    cubicContraction a T = ν * curvatureContraction S 1 T := by
  have hsum (i j : Fin 3) :
      (∑ k, inner ℝ a (T.matrix i j) * inner ℝ (T.matrix j k) (T.matrix k i)) =
        if i = j then ν * S.s i * ∑ k, ‖T.matrix i k‖ ^ 2 else 0 := by
    by_cases hij : i = j
    · subst j
      rw [hdiag]
      simp only [ite_true]
      have hinner (k : Fin 3) :
          inner ℝ (T.matrix i k) (T.matrix k i) = ‖T.matrix i k‖ ^ 2 := by
        rw [T.matrix_symmetric k i, real_inner_self_eq_norm_sq]
      simp_rw [hinner]
      rw [Finset.mul_sum]
    · simp [hdiag, hij]
  unfold cubicContraction
  simp_rw [hsum]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [curvatureContraction_eq_matrix]
  simp only [Fin.sum_univ_succ]
  ring

/-- The diagonal-frame condition determines the radial and orthogonal
components along the chosen tangent direction. -/
theorem diagonal_parameter_components (S : Shape) (a p k l : Vec) (ν : ℝ)
    (hdiag : ∀ i j, inner ℝ a ((parameters S p k l).matrix i j) =
      if i = j then ν * S.s i else 0) :
    inner ℝ a p = ν ∧ inner ℝ a k = 0 := by
  have hd (i : Fin 3) : inner ℝ a ((parameters S p k l).diagonal i) = ν * S.s i := by
    have h := hdiag i i
    have hm : (parameters S p k l).matrix i i = (parameters S p k l).diagonal i := by
      fin_cases i <;> rfl
    simpa only [hm, ite_true] using h
  constructor
  · rw [← radialCoordinate_parameters S p k l]
    unfold radialCoordinate
    simp only [real_inner_smul_right, inner_sum]
    simp_rw [hd]
    have hsum : ∑ i, S.s i * (ν * S.s i) = ν * ∑ i, S.s i ^ 2 := by
      simp only [Fin.sum_univ_succ]
      ring
    rw [hsum, S.square]
    ring
  · rw [← secondCoordinate_parameters S p k l]
    unfold secondCoordinate
    simp only [real_inner_smul_right, inner_sum]
    simp_rw [hd]
    have hsum : ∑ i, difference S.s i * (ν * S.s i) = ν * ∑ i, S.s i * difference S.s i := by
      simp only [Fin.sum_univ_succ]
      ring
    rw [hsum, difference_orthogonal]
    ring

/-- The sharp constant in (13), proved from the actual tensor contraction in
any normalized diagonal frame for the distinguished derivative. -/
theorem cubicContraction_sharp_diagonal (S : Shape) (a p k l : Vec) {ν : ℝ}
    (ha : ‖a‖ = 1) (hν : 0 ≤ ν)
    (hdiag : ∀ i j, inner ℝ a ((parameters S p k l).matrix i j) =
      if i = j then ν * S.s i else 0) :
    |cubicContraction a (parameters S p k l)| ≤
      (4 / 5) * Real.sqrt (3 / 5) * ((parameters S p k l).squaredNorm / 6) *
        Real.sqrt ((parameters S p k l).squaredNorm / 6) := by
  obtain ⟨hap, hak⟩ := diagonal_parameter_components S a p k l ν hdiag
  have hbound := distinguished_component_bound S a p k l ν ha hap hak
  have he : (5 / 3) * ν ^ 2 ≤ (5 / 3) * ‖p‖ ^ 2 + 5 * ‖k‖ ^ 2 + ‖l‖ ^ 2 := by
    have hp : ν ^ 2 ≤ ‖p‖ ^ 2 := by
      have hi := abs_real_inner_le_norm a p
      rw [ha, one_mul, hap] at hi
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg ν) (norm_nonneg p)).2 hi
    nlinarith [sq_nonneg ‖k‖, sq_nonneg ‖l‖]
  rw [cubicContraction_diagonal S a _ ν hdiag, curvatureContraction_parameters,
    parameters_energy]
  have hr : 8 * S.rho / Real.sqrt 3 = 8 * S.skewMoment := by
    rw [mul_div_assoc, S.rho_div_sqrt_three]
  rw [hr]
  simp only [one_mul]
  change |ν * normalizedCurvatureForm S p k l| ≤ _
  rw [abs_mul, abs_of_nonneg hν]
  calc
    _ ≤ ν * ((5 / 3) * ‖p‖ ^ 2 + 5 * ‖k‖ ^ 2 + ‖l‖ ^ 2 - ν ^ 2 / 3) :=
      mul_le_mul_of_nonneg_left hbound hν
    _ ≤ _ := HessianAlgebra.cubic_energy_optimization hν he

end
end PositiveEinsteinFour.Bianchi

end OAI
