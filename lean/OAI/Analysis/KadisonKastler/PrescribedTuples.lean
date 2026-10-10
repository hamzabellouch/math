import OAI.Analysis.KadisonKastler.OrderedTuples
import Mathlib.Data.List.Permutation
import Mathlib.Data.Sym.Card

namespace OAI

/-!
# Ordered tuples with a prescribed label multiset

A prescribed multiset may have repeated labels. Its ordered tuples embed
in the permutations of one representative list, giving the uniform
factorial bound. For a multiset without repetitions they are precisely
the ordered tuples of its underlying finite set.
-/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

variable {α : Type*} {r : ℕ}

abbrev PrescribedLabelTuple (s : Sym α r) :=
  {f : Fin r → α // (List.ofFn f : Multiset α) = (s : Multiset α)}

instance [Fintype α] (s : Sym α r) : Fintype (PrescribedLabelTuple s) := by
  classical
  unfold PrescribedLabelTuple
  infer_instance

def labelTupleSym (f : Fin r → α) : Sym α r :=
  ⟨(List.ofFn f : Multiset α), by simp⟩

/-- Forgetting the prescribed multiset gives all label functions exactly
once when the multiset itself is also summed over. -/
def prescribedTupleSigmaEquiv :
    (Σ s : Sym α r, PrescribedLabelTuple s) ≃ (Fin r → α) where
  toFun t := t.2.val
  invFun f := ⟨labelTupleSym f, ⟨f, rfl⟩⟩
  left_inv t := by
    rcases t with ⟨s, f, hf⟩
    have hs : labelTupleSym f = s := Subtype.ext hf
    subst s
    rfl
  right_inv _ := rfl

theorem sum_labelTuples_by_multiset [Fintype α] [DecidableEq α]
    {B : Type*} [AddCommMonoid B]
    (f : (Fin r → α) → B) :
    (∑ t : Fin r → α, f t) =
      ∑ s : Sym α r, ∑ t : PrescribedLabelTuple s, f t.val := by
  classical
  rw [← Fintype.sum_sigma']
  symm
  exact Fintype.sum_equiv prescribedTupleSigmaEquiv _ _ (fun _ => rfl)

/-- Repetitions only reduce the number of distinct orderings. -/
theorem card_prescribedLabelTuple_le [Fintype α] (s : Sym α r) :
    Fintype.card (PrescribedLabelTuple s) ≤ r.factorial := by
  classical
  let S : Finset (List α) := s.val.toList.permutations.toFinset
  let f : PrescribedLabelTuple s → S := fun t =>
    ⟨List.ofFn t.val, by
      apply List.mem_toFinset.mpr
      apply List.mem_permutations.mpr
      exact Multiset.coe_eq_coe.mp (t.property.trans (Multiset.coe_toList _).symm)⟩
  have hf : Function.Injective f := by
    intro t u h
    apply Subtype.ext
    exact List.ofFn_injective (congrArg Subtype.val h)
  calc
    Fintype.card (PrescribedLabelTuple s) ≤ Fintype.card S :=
      Fintype.card_le_of_injective f hf
    _ = S.card := Fintype.card_coe S
    _ ≤ s.val.toList.permutations.length := List.toFinset_card_le _
    _ = r.factorial := by rw [List.length_permutations, Multiset.length_toList, s.property]

variable [DecidableEq α]

omit [DecidableEq α] in
/-- A prescribed tuple is injective exactly when its multiset has no
repetitions. -/
theorem prescribedLabelTuple_injective (s : Sym α r) (hs : s.val.Nodup)
    (t : PrescribedLabelTuple s) : Function.Injective t.val := by
  apply List.nodup_ofFn.mp
  apply Multiset.coe_nodup.mp
  rw [t.property]
  exact hs

theorem prescribedLabelTuple_mem (s : Sym α r) (t : PrescribedLabelTuple s)
    (i : Fin r) : t.val i ∈ s.val.toFinset := by
  apply Multiset.mem_toFinset.mpr
  apply Eq.mp (congrArg (fun m : Multiset α => t.val i ∈ m) t.property)
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

/-- In the distinct case, both tuple types have literally the same
underlying label function. -/
def prescribedTupleOrderedEquiv (s : Sym α r) (hs : s.val.Nodup) :
    PrescribedLabelTuple s ≃ OrderedLabelTuple s.val.toFinset r where
  toFun t := ⟨t.val, prescribedLabelTuple_injective s hs t,
    prescribedLabelTuple_mem s t⟩
  invFun t := ⟨t.val, by
    have hn : (List.ofFn t.val : Multiset α).Nodup :=
      Multiset.coe_nodup.mpr (List.nodup_ofFn_ofInjective t.property.1)
    apply Multiset.Nodup.toFinset_inj hn hs
    have he : (tupleSubset t).val = s.val.toFinset := by
      apply Finset.eq_of_subset_of_card_le (tupleSubset t).property.1
      rw [(tupleSubset t).property.2, Multiset.toFinset_card_of_nodup hs, s.property]
    exact (toFinset_orderedTupleList t).trans he⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem prescribedTupleOrderedEquiv_apply_val (s : Sym α r) (hs : s.val.Nodup)
    (t : PrescribedLabelTuple s) : (prescribedTupleOrderedEquiv s hs t).val = t.val := rfl

@[simp]
theorem prescribedTupleOrderedEquiv_symm_apply_val (s : Sym α r) (hs : s.val.Nodup)
    (t : OrderedLabelTuple s.val.toFinset r) :
    ((prescribedTupleOrderedEquiv s hs).symm t).val = t.val := rfl

/-- Exact reindexing preserves every noncommutative word in the tuple. -/
theorem sum_prescribedLabelTuple_eq_ordered [Fintype α] {B : Type*} [AddCommMonoid B]
    (s : Sym α r) (hs : s.val.Nodup) (f : (Fin r → α) → B) :
    (∑ t : PrescribedLabelTuple s, f t.val) =
      ∑ t : OrderedLabelTuple s.val.toFinset r, f t.val := by
  classical
  exact Fintype.sum_equiv (prescribedTupleOrderedEquiv s hs) _ _ (fun _ => rfl)

theorem card_prescribedLabelTuple_of_nodup [Fintype α]
    (s : Sym α r) (hs : s.val.Nodup) :
    Fintype.card (PrescribedLabelTuple s) = r.factorial := by
  rw [Fintype.card_congr (prescribedTupleOrderedEquiv s hs)]
  exact card_full_orderedLabelTuple _
    ((Multiset.toFinset_card_of_nodup hs).trans s.property)

end

end KadisonKastler

end OAI
