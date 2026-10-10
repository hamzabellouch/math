import OAI.NumberTheory.Ostmann.Arithmetic.MovingNormalizedSymmetrizedEnergy
import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeSymmetrizedMasked

namespace OAI

/-! # The full original diagonal reduces to its masked symmetrized integral -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingAmplitudeSymmetrizedRegularEnergy_norm_le
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (hμ : ∀ j a, 0 ≤ μ j a) (n r m : ℕ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (G : ℕ → ℝ)
    (Q : MovingRegularSlot n r m → Finset ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (center b : ℝ)
    (hb : ∀ a, μ n a ≠ 0 → (a : ℝ) ≤ Real.exp b) :
    let H := G (n + 1)
    let Pg := smoothGiantPrimeRange H
    let Pivots := Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊
    let ν := movingTemplateRestoredPrior n r m (μ n) (fun i => primeSubsetPrior P (Q i))
    movingAmplitudeSymmetrizedRegularEnergy P Pg Pivots outside μ childBound pivotBound V
      F φ G n r m Q greg ≤
    Real.exp (((2 ^ n * 4 : ℕ) : ℝ) * b + smoothGiantLogNormalizer Pg φ H + center) *
      ‖movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F φ G
        n (4 + r) m ν (movingRestoredActive n r m) greg H H false
        (H - 1) (H + 1) (H - 1) (H + 1) center‖ := by
  intro H Pg Pivots ν
  have hid := movingSymmetrizedMaskedTemplateEnergy_original_interval P hP outside μ
    childBound pivotBound V F φ hout G n r m Q greg center
  dsimp only at hid
  have hn := congrArg norm hid
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hn
  have hm := (le_abs_self _).trans_eq hn
  have he := movingAmplitudeSymmetrizedRegularEnergy_le_masked P Pg Pivots hP outside μ hμ
    childBound pivotBound V F φ hφ G n r m Q greg b hb
  apply he.trans
  apply (mul_le_mul_of_nonneg_left hm (Real.exp_nonneg _)).trans_eq
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

end Ostmann

end OAI
