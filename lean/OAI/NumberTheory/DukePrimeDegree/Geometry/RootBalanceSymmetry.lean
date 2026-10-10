import OAI.NumberTheory.PrimePackets.RootSubgroups
import Mathlib.Data.Finset.Card

namespace OAI

/-!
# A finite balance criterion for symmetry of invariant roots

A reflexive transitive relation on a finite set is symmetric if every
vertex has the same incoming and outgoing degree. This applies to the
root-invariance relation when its degrees are balanced.
-/

noncomputable section
open MeasureTheory
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

/-- In a finite preorder, balanced in- and out-degrees rule out a strict
comparison. This includes the reflexive loop in both counts. -/
theorem symmetric_of_finite_preorder_balance
    {I : Type*} [Fintype I] (R : I → I → Prop)
    (hrefl : ∀ i, R i i)
    (htrans : ∀ ⦃i j k⦄, R i j → R j k → R i k)
    (hbalance : ∀ i,
      (Finset.univ.filter (R i)).card =
        (Finset.univ.filter (fun j => R j i)).card) :
    Std.Symm R := by
  classical
  constructor
  intro i j hij
  have hout : Finset.univ.filter (R j) ⊆ Finset.univ.filter (R i) := by
    intro k hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      htrans hij (Finset.mem_filter.mp hk).2⟩
  have hin : Finset.univ.filter (fun k => R k i) ⊆
      Finset.univ.filter (fun k => R k j) := by
    intro k hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      htrans (Finset.mem_filter.mp hk).2 hij⟩
  have hcard : (Finset.univ.filter (R i)).card ≤
      (Finset.univ.filter (R j)).card := by
    rw [hbalance i, hbalance j]
    exact Finset.card_le_card hin
  have heq := Finset.eq_of_subset_of_card_le hout hcard
  have hi : i ∈ Finset.univ.filter (R j) := by
    rw [heq]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrefl i⟩
  exact (Finset.mem_filter.mp hi).2

/-- Balanced degrees make the root-invariance relation symmetric. -/
theorem rootInvarianceRelation_symmetric_of_balance {n : ℕ}
    (μ : Measure (X n))
    (hbalance : ∀ i,
      (Finset.univ.filter (rootInvarianceRelation μ i)).card =
        (Finset.univ.filter (fun j => rootInvarianceRelation μ j i)).card) :
    Std.Symm (rootInvarianceRelation μ) :=
  symmetric_of_finite_preorder_balance (rootInvarianceRelation μ)
    (fun _ => Or.inl rfl) (rootInvarianceRelation_trans μ) hbalance

end DukePrimeDegree

end

end OAI
