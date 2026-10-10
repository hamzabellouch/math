import OAI.NumberTheory.Ostmann.Construction.SmoothGiantTransfer
import OAI.NumberTheory.Ostmann.Arithmetic.MovingGiantSupportedTransfer

namespace OAI

namespace Ostmann
open scoped Classical BigOperators

/-- The actual normalizer of (7.3), not a factorial or an assumed transfer
loss, gives the loss in (7.13). The off-diagonal on the right is the exact
weighted positive-integer substitution. -/
theorem smoothGiantPrior_transfer_on_prior {Y A : Type*} [Fintype Y] [Fintype A]
    (P I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPI : P ⊆ I)
    (hI : ∀ p ∈ I, 0 < p)
    (φ : ℝ → ℝ) (G : ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (hpos : 0 < smoothGiantMass P φ G)
    (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hμmass : ∑ y, μ y = 1)
    (U : Y → ℕ) (hU : ∀ y, 0 < U y)
    (row : ∀ y, (p : P) → Fin ((p : ℕ) * U y) → ℂ)
    (hrow : ∀ y p, (∑ t, ‖row y p t‖ ^ 2) ≤ (p : ℕ) * (U y : ℝ))
    (L : Y → A → ℕ) (v : Y → A → ℤ) (c : Y → ℕ → A → ℂ)
    (hcoprime : ∀ y p, p ∈ I → ∀ a, c y p a ≠ 0 → (L y a).Coprime (p * U y))
    (N H V : ℕ)
    (hv : ∀ y p, p ∈ I → ∀ a, c y p a ≠ 0 → (v y a).natAbs ≤ N)
    (hL : ∀ y, μ y ≠ 0 → ∀ p, p ∈ I → ∀ a, c y p a ≠ 0 → L y a ≤ H)
    (hscale : ∀ y, μ y ≠ 0 → ∀ p, p ∈ I → 2 * N * H ≤ V * (p * U y)) :
    Real.exp (-smoothGiantLogNormalizer P φ G) *
      ‖∑ y, (μ y : ℂ) * ∑ p : P, (smoothGiantPrior P φ G p : ℂ) *
        ∑ a, row y p (positiveIntegerPivotKey _
          (Nat.mul_pos (hP p p.property).pos (hU y)) (L y a) (v y a)) * c y p a‖ ^ 2 ≤
      (∑ y, μ y * (U y : ℝ) *
        ∑ p ∈ I, φ (Real.log p - G) * (pivotDiagonal (L y) (v y) (c y p)).re) +
      ‖∑ y, ((μ y * (U y : ℝ) : ℝ) : ℂ) *
        movingGiantOffDiagonal I V (U y) (L y) (v y)
          (fun p => φ (Real.log p - G)) (c y)‖ := by
  have ht := moving_giant_transfer_on_prior P I hP hPI hI μ hμ hμmass
    (fun p => φ (Real.log p - G)) (fun _ _ => hφ _)
    (Real.exp (smoothGiantLogNormalizer P φ G)) (Real.exp_nonneg _)
    (smoothGiantPrior_mass P φ G hpos) U hU row hrow L v c hcoprime N H V hv hL hscale
  change ‖∑ y, (μ y : ℂ) * ∑ p : P, (smoothGiantPrior P φ G p : ℂ) *
    ∑ a, row y p (positiveIntegerPivotKey _
      (Nat.mul_pos (hP p p.property).pos (hU y)) (L y a) (v y a)) * c y p a‖ ^ 2 ≤ _ at ht
  have hh := mul_le_mul_of_nonneg_left ht
    (Real.exp_nonneg (-smoothGiantLogNormalizer P φ G))
  rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] at hh
  exact hh.trans (add_le_add le_rfl (Complex.re_le_norm _))

end Ostmann

end OAI
