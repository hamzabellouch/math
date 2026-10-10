import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Local.LowReuseOrder

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Finset

theorem SmallReuseOrder.image {ι α β : Type*}
    [DecidableEq ι] [DecidableEq α] [DecidableEq β]
    {A : ι → Finset α} {l : List ι} (h : SmallReuseOrder A l)
    (f : α → β) (hf : Function.Injective f) :
    SmallReuseOrder (fun i => (A i).image f) l := by
  induction l with
  | nil => trivial
  | cons i l ih =>
    refine ⟨ih h.1, ?_⟩
    rw [← Finset.biUnion_image, ← Finset.image_inter _ _ hf,
      Finset.card_image_of_injective _ hf]
    exact h.2

theorem get_mem_drop_of_le {ι : Type*} (l : List ι) (i : Fin l.length)
    (n : ℕ) (hn : n ≤ i.val) : l.get i ∈ l.drop n := by
  apply List.mem_drop_iff_getElem.mpr
  refine ⟨i.val - n, by omega, ?_⟩
  simp only [Nat.add_sub_of_le hn, List.get_eq_getElem]

theorem SmallReuseOrder.tail_overlap {ι α : Type*}
    [DecidableEq ι] [DecidableEq α] {A : ι → Finset α} {l : List ι}
    (h : SmallReuseOrder A l) (i : Fin l.length) :
    (A (l.get i) ∩ (l.drop (i.val + 1)).toFinset.biUnion A).card ≤ 1 := by
  induction l with
  | nil => exact Fin.elim0 i
  | cons a l ih =>
    obtain ⟨htail, hhead⟩ := h
    rcases i with ⟨n, hn⟩
    cases n with
    | zero => simpa using hhead
    | succ n =>
      have hn' : n < l.length := by simpa using hn
      simpa using ih htail ⟨n, hn'⟩

theorem exists_perm_of_list_tail_overlap {α : Type*} [DecidableEq α]
    {b : ℕ} (A : Fin b → Finset α) (l : List (Fin b))
    (hnd : l.Nodup) (hfull : l.toFinset = Finset.univ)
    (hsmall : ∀ i : Fin l.length,
      (A (l.get i) ∩ (l.drop (i.val + 1)).toFinset.biUnion A).card ≤ 1) :
    ∃ π : Equiv.Perm (Fin b), ∀ i : Fin b,
      (A (π i) ∩ (Finset.univ.filter (fun j : Fin b => j < i)).biUnion
        (fun j => A (π j))).card ≤ 1 := by
  have hlen : l.length = b := by
    rw [← List.toFinset_card_of_nodup hnd, hfull]
    simp
  have hall : ∀ x : Fin b, x ∈ l := by
    intro x
    have hx : x ∈ l.toFinset := by rw [hfull]; exact Finset.mem_univ _
    simpa using hx
  let e : Fin b ≃ Fin l.length := Fin.revPerm.trans (finCongr hlen.symm)
  let π : Equiv.Perm (Fin b) := e.trans (List.Nodup.getEquivOfForallMemList l hnd hall)
  refine ⟨π, fun i => ?_⟩
  change (A (l.get (e i)) ∩ _).card ≤ 1
  apply le_trans (Finset.card_le_card ?_) (hsmall (e i))
  apply Finset.inter_subset_inter_left
  intro a ha
  obtain ⟨j, hj, haj⟩ := Finset.mem_biUnion.mp ha
  have hji : j < i := (Finset.mem_filter.mp hj).2
  have heij : (e i).val < (e j).val := by
    change (Fin.rev i).val < (Fin.rev j).val
    exact Fin.rev_lt_rev.mpr hji
  apply Finset.mem_biUnion.mpr
  refine ⟨l.get (e j), ?_, haj⟩
  apply List.mem_toFinset.mpr
  exact get_mem_drop_of_le l (e j) ((e i).val + 1) (by omega)

end Balanced

end OAI
