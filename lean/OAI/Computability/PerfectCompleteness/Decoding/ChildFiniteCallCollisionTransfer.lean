import OAI.Computability.PerfectCompleteness.Algebra.ChildBilinearCollisionTransfer
import OAI.Computability.PerfectCompleteness.Sampling.ChildCallNumberingLaws

namespace OAI

section

namespace PerfectCompleteness.ChildFiniteCallCollisionTransfer

noncomputable section

open scoped Classical
open RecursiveSpaces TreeSourceSpaces
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n t : Nat} {C : Type*} [Fintype C]
  {Z : Fin (branch n) → Type*} [∀ i, Fintype (Z i)]

theorem marked_restricted_le_uniform_full
    (rows : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (projected : (i : Fin (branch n)) → Z i → Slots branch n → Fin t → MixedSupport.Slot)
    (p : ∀ i z s k, MixedSupport.Projection
      (childSlots slots i s k) (projected i z s k))
    (choiceLaw : (i : Fin (branch n)) → FiniteDistribution (Z i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (F₀ F₁ : CutChildGrouping.Raw (C := C) slots rows →
      Option (ChildBilinearCollisionTransfer.ParentForm slots)) :
    (SparseReplacement.markedLaw
        (fun i => FiniteDistribution.uniform
          (ChildCallNumbering.Raw (C := C) rows (childSlots slots i)))
        (ChildCallNumberingLaws.replacementLaws (C := C) rows (childSlots slots)
          projected p choiceLaw) β hβ hβ'.le).probability
      (fun z => BilinearCollisionTransfer.restrictedCollision
        (F₀ z.2) (F₁ z.2) (ChildUnmarkedSpace.space slots z.1)) ≤
      (FiniteProduct.law (fun i => FiniteDistribution.uniform
        (ChildCallNumbering.Raw (C := C) rows (childSlots slots i)))).probability
          (fun x => BilinearCollisionTransfer.fullCollision (F₀ x) (F₁ x)) +
        2 * (β * (ChildBlockCardinality.bound branch n t (Fintype.card C) rows : ℝ) /
          (1 - β)) +
        Real.sqrt ((1 + β ^ 2 *
          ((ChildBlockCardinality.bound branch n t (Fintype.card C) rows : ℝ) - 1)) ^
            branch n - 1) / 2 := by
  have h := ChildBilinearCollisionTransfer.marked_restricted_le_uniform_full
    (Fintype.card C) rows slots projected p choiceLaw β hβ hβ'
    (fun x => F₀ (ChildCallNumberingLaws.unnumber (C := C) rows (childSlots slots) x))
    (fun x => F₁ (ChildCallNumberingLaws.unnumber (C := C) rows (childSlots slots) x))
  rw [← ChildCallNumberingLaws.markedLaw_numbered (C := C) rows (childSlots slots)
    projected p choiceLaw β hβ hβ'.le, FiniteDistribution.probability_pushforward] at h
  rw [← ChildCallNumberingLaws.uniform_product_numbered (C := C) rows (childSlots slots),
    FiniteDistribution.probability_pushforward] at h
  simpa only [ChildCallNumberingLaws.unnumber_number] using h

end
end PerfectCompleteness.ChildFiniteCallCollisionTransfer

end

end OAI
