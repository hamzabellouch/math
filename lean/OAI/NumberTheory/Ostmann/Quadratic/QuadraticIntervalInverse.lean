import OAI.NumberTheory.Ostmann.QuadraticCenter.WeightedQuadraticInverse

namespace OAI

/-! # The inverse quadratic estimate on translated integer intervals -/

namespace Ostmann

open scoped BigOperators

noncomputable def integerQuadraticPhase (α β : ℝ) (j : ℤ) : ℂ :=
  realAdditivePhase (α * (j : ℝ) ^ 2 + β * j)

theorem integerQuadraticPhase_translate (α β : ℝ) (z : ℤ) (j : ℕ) :
    integerQuadraticPhase α β (z + j) =
      realAdditivePhase (α * (z : ℝ) ^ 2 + β * z) *
        realQuadraticPhase α (β + 2 * α * z) j := by
  unfold integerQuadraticPhase realQuadraticPhase
  rw [← realAdditivePhase_add]
  congr 1
  push_cast
  ring

theorem weighted_quadratic_translate_norm (w : ℕ → ℂ) (α β : ℝ) (z : ℤ) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, w j * integerQuadraticPhase α β (z + j)‖ =
      ‖∑ j ∈ Finset.range N, w j * realQuadraticPhase α (β + 2 * α * z) j‖ := by
  simp_rw [integerQuadraticPhase_translate]
  have heq : (∑ j ∈ Finset.range N, w j *
      (realAdditivePhase (α * (z : ℝ) ^ 2 + β * z) * realQuadraticPhase α (β + 2 * α * z) j)) =
      realAdditivePhase (α * (z : ℝ) ^ 2 + β * z) *
        ∑ j ∈ Finset.range N, w j * realQuadraticPhase α (β + 2 * α * z) j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq, Complex.norm_mul, norm_realAdditivePhase, one_mul]

/-- The original interval location affects only the linear coefficient,
which is arbitrary in the proved inverse theorem. -/
theorem weighted_integer_quadratic_inverse (w : ℕ → ℂ) (α β δ : ℝ) (z : ℤ) (N : ℕ)
    (hN : 0 < N) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hscale : 512 * (1 + 2 * Real.log (N : ℝ)) ≤ δ ^ 3 * N)
    (hlarge : discreteVariation w N * (δ * N) <
      ‖∑ j ∈ Finset.range N, w j * integerQuadraticPhase α β (z + j)‖) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ 1024 / δ ^ 2 ∧
      |(q : ℝ) * α - (round ((q : ℝ) * α) : ℤ)| ≤
        1024 * (1 + 2 * Real.log (N : ℝ)) / (δ ^ 4 * (N : ℝ) ^ 2) := by
  rw [weighted_quadratic_translate_norm] at hlarge
  exact weighted_quadratic_inverse w α (β + 2 * α * z) δ N hN hδ hδ1 hscale hlarge

end Ostmann

end OAI
