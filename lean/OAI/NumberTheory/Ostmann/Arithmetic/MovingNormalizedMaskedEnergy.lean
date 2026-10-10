import OAI.NumberTheory.Ostmann.Arithmetic.MovingMaskedOriginalIntegral
import OAI.NumberTheory.Ostmann.Characters.MixedExternalPartition

namespace OAI

/-! # The exact normalization of the original masked diagonal energy -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingMaskedTemplateEnergy_original_interval {J : Type}
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (q : J → ℕ) [∀ i, Fact (q i).Prime]
    (outside : List ℕ) (μ : ℕ → P → ℝ) (n r m : ℕ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (G : ℕ → ℝ)
    (Q : MovingRegularSlot n r m → Finset ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (center : ℝ) :
    let H := G (n + 1)
    let Pg := smoothGiantPrimeRange H
    let Pivots := Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊
    let ν := movingTemplateRestoredPrior n r m (μ n) (fun i => primeSubsetPrior P (Q i))
    (movingMaskedTemplateEnergy P Pg Pivots hP outside μ childBound pivotBound V
      (movingOriginalLeaf Subtype.val q (fun _ => f) g Dq S ψ X lo hi) φ G n r m Q greg
      (fun _ => 1) : ℂ) =
    (Real.exp (smoothGiantLogNormalizer Pg φ H + center) : ℂ) *
      movingWeightedDiagonalEnergy q Subtype.val outside μ ν childBound pivotBound V f g Dq S
        ψ X lo hi φ G n (movingTemplateSmall n (4 + r) m)
        (bulkSlotLeaves n m (movingTemplateBulk n (4 + r) m))
        (fun s => movingTemplateExternalMultiplier P hP n (4 + r) m
          (movingRestoredActive n r m) outside greg s φ H H false)
        (H - 1) (H + 1) (H - 1) (H + 1) center := by
  intro H Pg Pivots ν
  have h := movingMaskedTemplateEnergy_interval P hP outside μ childBound pivotBound V
    (movingOriginalLeaf Subtype.val q (fun _ => f) g Dq S ψ X lo hi) φ hout G n r m Q greg center
  have hi := movingMaskedTemplateKernel_original_integral P hP q outside μ n r m ν
    childBound pivotBound V f g Dq S ψ X lo hi φ G greg H
    (H - 1) (H + 1) (H - 1) (H + 1) center
  exact h.trans (congrArg (fun z : ℂ =>
    (Real.exp (smoothGiantLogNormalizer Pg φ H + center) : ℂ) * z) hi)

end Ostmann

end OAI
