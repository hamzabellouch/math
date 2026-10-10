import OAI.NumberTheory.Ostmann.Arithmetic.MovingNormalizedMaskedEnergy
import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeMaskedEnergy

namespace OAI

/-! # The original one-branch energy controlled by its exact mixed integral -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingAmplitudeRegularEnergy_original_norm_le {J : Type}
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (q : J → ℕ) [∀ i, Fact (q i).Prime]
    (outside : List ℕ) (μ : ℕ → P → ℝ) (hμ : ∀ j a, 0 ≤ μ j a) (n r m : ℕ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ)
    (hφ : ∀ x, 0 ≤ φ x) (hout : ∀ x, 1 ≤ |x| → φ x = 0) (G : ℕ → ℝ)
    (Q : MovingRegularSlot n r m → Finset ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (center b : ℝ)
    (hb : ∀ a, μ n a ≠ 0 → (a : ℝ) ≤ Real.exp b) :
    let H := G (n + 1)
    let Pg := smoothGiantPrimeRange H
    let Pivots := Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊
    let ν := movingTemplateRestoredPrior n r m (μ n) (fun i => primeSubsetPrior P (Q i))
    movingAmplitudeRegularEnergy P Pg Pivots outside μ childBound pivotBound V
      (movingOriginalLeaf Subtype.val q (fun _ => f) g Dq S ψ X lo hi) φ G n r m Q greg ≤
    Real.exp (((2 ^ n * 4 : ℕ) : ℝ) * b + smoothGiantLogNormalizer Pg φ H + center) *
      ‖movingWeightedDiagonalEnergy q Subtype.val outside μ ν childBound pivotBound V f g Dq S
        ψ X lo hi φ G n (movingTemplateSmall n (4 + r) m)
        (bulkSlotLeaves n m (movingTemplateBulk n (4 + r) m))
        (fun s => movingTemplateExternalMultiplier P hP n (4 + r) m
          (movingRestoredActive n r m) outside greg s φ H H false)
        (H - 1) (H + 1) (H - 1) (H + 1) center‖ := by
  intro H Pg Pivots ν
  have hid := movingMaskedTemplateEnergy_original_interval P hP q outside μ n r m
    childBound pivotBound V f g Dq S ψ X lo hi φ hout G Q greg center
  dsimp only at hid
  have hn := congrArg norm hid
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hn
  have hm := (le_abs_self _).trans_eq hn
  have he := movingAmplitudeRegularEnergy_le_masked P Pg Pivots hP outside μ hμ
    childBound pivotBound V (movingOriginalLeaf Subtype.val q (fun _ => f) g Dq S ψ X lo hi)
    φ hφ G n r m Q greg b hb
  apply he.trans
  apply (mul_le_mul_of_nonneg_left hm (Real.exp_nonneg _)).trans_eq
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

end Ostmann

end OAI
