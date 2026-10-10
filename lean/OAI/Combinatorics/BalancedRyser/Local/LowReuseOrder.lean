import OAI.Combinatorics.BalancedRyser.Local.ReuseOrdering

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Finset

def SmallReuseOrder {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (A : ι → Finset α) : List ι → Prop
  | [] => True
  | i :: l => SmallReuseOrder A l ∧ (A i ∩ l.toFinset.biUnion A).card ≤ 1

theorem family_reuse_erase {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (A : ι → Finset α) (s : Finset ι) (i : ι) (hi : i ∈ s) :
    (∑ j ∈ s, (A j).card) - (s.biUnion A).card =
      ((∑ j ∈ s.erase i, (A j).card) - ((s.erase i).biUnion A).card) +
        (A i ∩ (s.erase i).biUnion A).card := by
  simpa only [Finset.insert_erase hi] using
    family_reuse_insert A (s.erase i) i (Finset.notMem_erase i s)

theorem exists_low_reuse_leaf {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (A : ι → Finset α) (s : Finset ι) (hs : s.Nonempty)
    (hcompat : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (A i ∩ A j).card ≤ 1)
    (hexcess : (∑ i ∈ s, (A i).card) - (s.biUnion A).card ≤ 2) :
    ∃ i ∈ s, (A i ∩ (s.erase i).biUnion A).card ≤ 1 := by
  obtain ⟨i, hi⟩ := hs
  by_cases hsmall : (A i ∩ (s.erase i).biUnion A).card ≤ 1
  · exact ⟨i, hi, hsmall⟩
  have hdecomp := family_reuse_erase A s i hi
  have hzero : (∑ j ∈ s.erase i, (A j).card) -
      ((s.erase i).biUnion A).card = 0 := by omega
  have hrest : (s.erase i).Nonempty := by
    by_contra h
    have he : s.erase i = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he] at hsmall
  obtain ⟨j, hj⟩ := hrest
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hjs : j ∈ s := (Finset.mem_erase.mp hj).2
  have hjdecomp := family_reuse_erase A (s.erase i) j hj
  have hjzero : (A j ∩ ((s.erase i).erase j).biUnion A).card = 0 := by omega
  have hjempty : A j ∩ ((s.erase i).erase j).biUnion A = ∅ :=
    Finset.card_eq_zero.mp hjzero
  refine ⟨j, hjs, (Finset.card_le_card ?_).trans (hcompat j hjs i hi hji)⟩
  intro x hx
  obtain ⟨hxj, hxrest⟩ := Finset.mem_inter.mp hx
  obtain ⟨k, hk, hxk⟩ := Finset.mem_biUnion.mp hxrest
  by_cases hki : k = i
  · exact Finset.mem_inter.mpr ⟨hxj, hki ▸ hxk⟩
  · have hk' : k ∈ (s.erase i).erase j := by
      obtain ⟨hkj, hks⟩ := Finset.mem_erase.mp hk
      exact Finset.mem_erase.mpr ⟨hkj, Finset.mem_erase.mpr ⟨hki, hks⟩⟩
    have hxin : x ∈ A j ∩ ((s.erase i).erase j).biUnion A :=
      Finset.mem_inter.mpr ⟨hxj, Finset.mem_biUnion.mpr ⟨k, hk', hxk⟩⟩
    simp only [hjempty, Finset.notMem_empty] at hxin

theorem exists_smallReuseOrder {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (A : ι → Finset α) (s : Finset ι)
    (hcompat : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (A i ∩ A j).card ≤ 1)
    (hexcess : (∑ i ∈ s, (A i).card) - (s.biUnion A).card ≤ 2) :
    ∃ l : List ι, l.Nodup ∧ l.toFinset = s ∧ SmallReuseOrder A l := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨i, hi, hleaf⟩ := exists_low_reuse_leaf A s hs hcompat hexcess
      have hexcess' : (∑ j ∈ s.erase i, (A j).card) -
          ((s.erase i).biUnion A).card ≤ 2 := by
        have hdecomp := family_reuse_erase A s i hi
        omega
      obtain ⟨l, hnd, hset, horder⟩ := ih (s.erase i) (Finset.erase_ssubset hi)
        (fun j hj k hk hne => hcompat j (Finset.mem_of_mem_erase hj)
          k (Finset.mem_of_mem_erase hk) hne) hexcess'
      refine ⟨i :: l, List.nodup_cons.mpr ⟨?_, hnd⟩, ?_, ?_⟩
      · intro hil
        have hiset : i ∈ l.toFinset := List.mem_toFinset.mpr hil
        rw [hset] at hiset
        exact Finset.notMem_erase i s hiset
      · rw [List.toFinset_cons, hset, Finset.insert_erase hi]
      · exact ⟨horder, by simpa only [hset] using hleaf⟩
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      exact ⟨[], by simp, by simp, trivial⟩

end Balanced

end OAI
