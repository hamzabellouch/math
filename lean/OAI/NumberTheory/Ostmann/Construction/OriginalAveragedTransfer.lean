import OAI.NumberTheory.Ostmann.Construction.OriginalPivotTransfer
import OAI.NumberTheory.Ostmann.Arithmetic.AveragedArithmeticTransfer

namespace OAI

/-! # The actual averaged arithmetic step with its forced integer substitution -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

noncomputable def reconstructedOffDiagonal {A : Type*} [Fintype A]
    (T : Finset ℕ) (V : ℕ) (L : A → ℕ) (v : A → ℤ) (c : ℕ → A → ℂ) : ℂ :=
  ∑ s ∈ transferFrequencyRange V, ∑ a, ∑ b,
    if validTransferredPivot T (v a * L b - v b * L a) s then
      c (reconstructedPivot (v a * L b - v b * L a) s) a *
        conj (c (reconstructedPivot (v a * L b - v b * L a) s) b) else 0

/-- The original prime-tuple prior, both Cauchy steps, and the entire
integer off-diagonal are included in this normalized transfer inequality. -/
theorem original_averaged_pivot_transfer {A Y : Type*} [Fintype A] [Fintype Y]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (Q : Fin n → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (S : Finset (Fin n → P)) (hS : ∀ x ∈ S, Function.Injective x)
    (T : Finset ℕ) (hTpos : ∀ M ∈ T, 0 < M)
    (hT : ∀ x ∈ S, (∏ i, (x i : ℕ)) ∈ T)
    (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hmass : ∑ y, μ y ≤ 1)
    (row : Y → (x : Fin n → P) → Fin (∏ i, (x i : ℕ)) → ℂ)
    (hrow : ∀ y x, x ∈ S → ∀ u, ‖row y x u‖ ≤ 1)
    (L : A → ℕ) (v : A → ℤ) (c : Y → ℕ → A → ℂ)
    (hcoprime : ∀ y M, M ∈ T → ∀ a, c y M a ≠ 0 → (L a).Coprime M)
    (hpositive : ∀ y M, M ∈ T → ∀ a, c y M a ≠ 0 → 0 < L a)
    (B H V : ℕ)
    (hv : ∀ y M, M ∈ T → ∀ a, c y M a ≠ 0 → (v a).natAbs ≤ B)
    (hL : ∀ y M, M ∈ T → ∀ a, c y M a ≠ 0 → L a ≤ H)
    (hscale : ∀ M ∈ T, 2 * B * H ≤ V * M)
    (d : ℝ) (hcost : ((n.factorial : ℝ) * ∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) ≤ Real.exp d) :
    Real.exp (-d) *
      ‖∑ y, (μ y : ℂ) * (∑ x ∈ S, (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) *
        ∑ a, row y x (primeTuplePivotKey P hP x (L a) (v a)) * c y (∏ i, (x i : ℕ)) a)‖ ^ 2 ≤
      (∑ y, μ y * (∑ M ∈ T, (pivotDiagonal L v (c y M)).re)) +
        ‖∑ y, (μ y : ℂ) * reconstructedOffDiagonal T V L v (c y)‖ := by
  let η : Y → ℂ := fun y => ∑ x ∈ S,
    (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) *
      ∑ a, row y x (primeTuplePivotKey P hP x (L a) (v a)) * c y (∏ i, (x i : ℕ)) a
  let D : Y → ℝ := fun y => ∑ M ∈ T, (pivotDiagonal L v (c y M)).re
  let θ : Y → ℂ := fun y => reconstructedOffDiagonal T V L v (c y)
  let K := (n.factorial : ℝ) * ∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹
  have hlocal (y : Y) : ‖η y‖ ^ 2 ≤ K * (D y + (θ y).re) := by
    have ht := original_pivot_transfer_real P hP Q hQP hQ S hS T hTpos hT
      (row y) (hrow y) L v (c y) (hcoprime y)
    have he := sum_pivotOffDiagonal_substitution_on_support T hTpos B H V L v (c y)
      (hv y) (hL y) hscale
    rw [he] at ht
    exact ht
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hD : 0 ≤ ∑ y, μ y * D y := by
    apply Finset.sum_nonneg
    intro y _
    apply mul_nonneg (hμ y)
    apply Finset.sum_nonneg
    intro M hMT
    exact pivotDiagonal_nonneg_of_positive_support L v (c y M) (hpositive y M hMT)
  exact normalized_arithmetic_transfer _ _ _ K d hD hcost
    (averaged_arithmetic_transfer μ hμ hmass η θ D K hK hlocal)

end Ostmann

end OAI
