import OAI.NumberTheory.Ostmann.Arithmetic.MovingNormalizedMaskedEnergy
import OAI.NumberTheory.Ostmann.Arithmetic.MovingWeightedEnergyPartition
import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeMaskedEnergy

namespace OAI

/-! # Transferring the arithmetic cell bound to the original discrete energy -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingMaskedTemplateEnergy_original_bound {J : Type}
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (q : J → ℕ) [∀ i, Fact (q i).Prime]
    (outside : List ℕ) (μ : ℕ → P → ℝ) (n r m : ℕ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (G : ℕ → ℝ)
    (Q : MovingRegularSlot n r m → Finset ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (center E : ℝ)
    (hcell : ∀ i j : Bool, ‖movingWeightedDiagonalEnergy q Subtype.val outside μ
      (movingTemplateRestoredPrior n r m (μ n) (fun i => primeSubsetPrior P (Q i)))
      childBound pivotBound V f g Dq S ψ X lo hi φ G n
      (movingTemplateSmall n (4 + r) m) (bulkSlotLeaves n m (movingTemplateBulk n (4 + r) m))
      (fun s => movingTemplateExternalMultiplier P hP n (4 + r) m
        (movingRestoredActive n r m) outside greg s φ (G (n + 1)) (G (n + 1)) false)
      (if i then G (n + 1) else G (n + 1) - 1) ((if i then G (n + 1) else G (n + 1) - 1) + 1)
      (if j then G (n + 1) else G (n + 1) - 1) ((if j then G (n + 1) else G (n + 1) - 1) + 1)
      center‖ ≤ E) :
    movingMaskedTemplateEnergy P (smoothGiantPrimeRange (G (n + 1)))
      (Finset.Ioc ⌊Real.exp (G (n + 1) - 1)⌋₊ ⌊Real.exp (G (n + 1) + 1)⌋₊)
      hP outside μ childBound pivotBound V
      (movingOriginalLeaf Subtype.val q (fun _ => f) g Dq S ψ X lo hi) φ G n r m Q greg (fun _ => 1) ≤
    Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange (G (n + 1))) φ (G (n + 1)) + center) *
      (4 * E) := by
  have hid := movingMaskedTemplateEnergy_original_interval P hP q outside μ n r m
    childBound pivotBound V f g Dq S ψ X lo hi φ hout G Q greg center
  dsimp only at hid
  have hn := congrArg norm hid
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] at hn
  have hc := movingWeightedDiagonalEnergy_full_cell_bound q Subtype.val outside μ
    (movingTemplateRestoredPrior n r m (μ n) (fun i => primeSubsetPrior P (Q i)))
    childBound pivotBound V f g Dq S ψ X lo hi φ G n
    (movingTemplateSmall n (4 + r) m) (bulkSlotLeaves n m (movingTemplateBulk n (4 + r) m))
    (fun s => movingTemplateExternalMultiplier P hP n (4 + r) m
      (movingRestoredActive n r m) outside greg s φ (G (n + 1)) (G (n + 1)) false)
    (G (n + 1)) (G (n + 1)) center E hcell
  exact (le_abs_self _).trans (hn.trans_le (mul_le_mul_of_nonneg_left hc (Real.exp_nonneg _)))

end Ostmann

end OAI
