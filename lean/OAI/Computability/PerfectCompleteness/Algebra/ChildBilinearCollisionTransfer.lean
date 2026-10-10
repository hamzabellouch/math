import OAI.Computability.PerfectCompleteness.Algebra.BilinearWitnessLemmas
import OAI.Computability.PerfectCompleteness.Construction.ChildUnmarkedSpace
import OAI.Computability.PerfectCompleteness.Decoding.ChildBlockProjection
import OAI.Computability.PerfectCompleteness.Sampling.RationalFiniteLawLemmas

namespace OAI

section

namespace PerfectCompleteness.ChildBilinearCollisionTransfer

noncomputable section

open scoped Classical
open RecursiveSpaces TreeSourceSpaces PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n t : Nat}

abbrev ParentForm (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :=
  H slots →ₗ[F2] H slots →ₗ[F2] F2

abbrev Raw (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :=
  (i : Fin (branch n)) → ChildBlockCardinality.Raw calls rows (childSlots slots i)

variable {Z : Fin (branch n) → Type*} [∀ i, Fintype (Z i)]

theorem marked_restricted_le_uniform_full
    (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (projected : (i : Fin (branch n)) → Z i → Slots branch n → Fin t → MixedSupport.Slot)
    (p : ∀ i z s k, MixedSupport.Projection
      (childSlots slots i s k) (projected i z s k))
    (choiceLaw : (i : Fin (branch n)) → FiniteDistribution (Z i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (F₀ F₁ : Raw calls rows slots → Option (ParentForm slots)) :
    (SparseReplacement.markedLaw
        (fun i => FiniteDistribution.uniform
          (ChildBlockCardinality.Raw calls rows (childSlots slots i)))
        (ChildBlockProjection.replacementLaws calls rows (childSlots slots)
          projected p choiceLaw) β hβ hβ'.le).probability
      (fun z => BilinearCollisionTransfer.restrictedCollision
        (F₀ z.2) (F₁ z.2) (ChildUnmarkedSpace.space slots z.1)) ≤
      (FiniteProduct.law (fun i => FiniteDistribution.uniform
        (ChildBlockCardinality.Raw calls rows (childSlots slots i)))).probability
          (fun x => BilinearCollisionTransfer.fullCollision (F₀ x) (F₁ x)) +
        2 * (β * (ChildBlockCardinality.bound branch n t calls rows : ℝ) / (1 - β)) +
        Real.sqrt ((1 + β ^ 2 *
          ((ChildBlockCardinality.bound branch n t calls rows : ℝ) - 1)) ^
            branch n - 1) / 2 := by
  let P : (i : Fin (branch n)) → FiniteDistribution
      (ChildBlockCardinality.Raw calls rows (childSlots slots i)) :=
    fun i => FiniteDistribution.uniform
      (ChildBlockCardinality.Raw calls rows (childSlots slots i))
  let Q := ChildBlockProjection.replacementLaws calls rows (childSlots slots)
    projected p choiceLaw
  let L : ℝ := ChildBlockCardinality.bound branch n t calls rows
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have hcard : ∀ i : Fin (branch n),
      (Fintype.card (ChildBlockCardinality.Raw calls rows (childSlots slots i)) : ℝ) ≤ L := by
    intro i
    dsimp only [L]
    exact_mod_cast ChildBlockCardinality.fintype_card_le calls rows (childSlots slots i)
  have hdom : ∀ i x, (Q i).weight x ≤ L * (P i).weight x :=
    CoordinateReplacement.uniform_domination Q L hcard
  have hsupport := CoordinateReplacement.support_of_domination P Q L hdom
  have hbound : ∀ i x, CoordinateReplacement.ratio P Q i x ≤ L :=
    fun i x => (CoordinateReplacement.ratio_bounds_of_domination P Q L hL hdom i x).2
  have htransfer := BilinearCollisionTransfer.full_collision_transfer
    (ChildUnmarkedSpace.childMap slots) (ChildUnmarkedSpace.assemble_surjective slots)
    F₀ F₁ (fun _ mask => ChildUnmarkedSpace.space slots mask)
    (fun _ mask i hi v => ChildUnmarkedSpace.childMap_mem_space slots mask i hi v)
    P (CoordinateReplacement.ratio P Q) (CoordinateReplacement.ratio_nonnegative P Q)
    (CoordinateReplacement.ratio_mean_one_of_support P Q hsupport)
    β hβ hβ' L hL hbound (FiniteProduct.law P)
  rw [SparseReplacement.forward_eq P Q hsupport β hβ hβ',
    SparseReplacement.markedLaw_marginal] at htransfer
  have hvariation := SparseReplacement.observed_variation P Q β hβ hβ'.le L hL hdom
    (id : Raw calls rows slots → Raw calls rows slots)
  simp only [FiniteDistribution.pushforward_id, Fintype.card_fin] at hvariation
  change (SparseReplacement.markedLaw P Q β hβ hβ'.le).probability
      (fun z => BilinearCollisionTransfer.restrictedCollision
        (F₀ z.2) (F₁ z.2) (ChildUnmarkedSpace.space slots z.1)) ≤
    (FiniteProduct.law P).probability
      (fun x => BilinearCollisionTransfer.fullCollision (F₀ x) (F₁ x)) +
      2 * (β * L / (1 - β)) +
      Real.sqrt ((1 + β ^ 2 * (L - 1)) ^ branch n - 1) / 2
  linarith

end
end PerfectCompleteness.ChildBilinearCollisionTransfer

end

end OAI
