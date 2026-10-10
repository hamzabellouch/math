import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplatePrimeCore
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOneGiant

namespace OAI

/-! # The transfer's tagged full factor is the arithmetic prime core -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- This identifies the full factor used in the literal integer-node
recursion with the prime statistic at its original two prime arguments. -/
theorem movingTemplatePrimeCore_eq_tagged {σ I : Type} [Fintype σ]
    (pSpec : I → ℕ) [∀ i, Fact (pSpec i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (pSpec i) → ℂ) (Dq : ∀ i, (ZMod (pSpec i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n r m : ℕ) (s : ℤ) (y : MovingRegularSlot n r m → σ)
    (q : Bool → ℕ) [∀ b, Fact (q b).Prime]
    (hprime : ∀ i, (value (y i)).Prime)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) :
    movingPrimeCore pSpec value outside μ childBound pivotBound V f g Dq S ψ X lo hi φ G
      n m (movingTemplateSmall n r m) (movingTemplateBulk n r m) greg ggiant favorable
      s y (Real.log (q true)) (Real.log (q false)) =
    movingTaggedTransform (Sum.elim q (value ∘ y))
      (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s *
      movingTemplateCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value pSpec (fun _ => f) g Dq S ψ X lo hi) φ G n r m s y
        (q true) (q false) := by
  let : ∀ i, Fact ((value ∘ y) i).Prime := fun i => ⟨hprime i⟩
  have h := movingTemplatePrimeCore_eq_full pSpec value outside μ childBound pivotBound V f
    g Dq S ψ X lo hi φ G n r m s y q hprime greg ggiant favorable
  have ht := movingTaggedTransform_full q (value ∘ y) greg ggiant favorable outside.prod s
  apply h.trans
  apply congrArg (fun z : ℂ => z * movingTemplateCoefficient value outside μ childBound pivotBound V
    (movingOriginalLeaf value pSpec (fun _ => f) g Dq S ψ X lo hi) φ G n r m s y (q true) (q false))
  convert ht.symm using 1
  unfold movingRegularTransform
  apply Finset.prod_congr rfl
  intro i _
  cases i <;> rfl

end Ostmann

end OAI
