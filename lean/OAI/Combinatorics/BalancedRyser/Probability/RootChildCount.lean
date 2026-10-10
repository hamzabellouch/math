import OAI.Combinatorics.BalancedRyser.Construction.RootChildPartition
import OAI.Combinatorics.BalancedRyser.Probability.EqualityPatternOrdering

namespace OAI

namespace Balanced.RootChildPartition

open scoped BigOperators
variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

omit [DecidableEq ι] in

theorem reuse_roots_eq_zero (A : ι → Finset α) (R : Finset ι)
    (hroots : DisjointRoots A R) :
    (∑ i ∈ R, (A i).card) - (R.biUnion A).card = 0 := by
  have hc : (R.biUnion A).card = ∑ i ∈ R, (A i).card :=
    Finset.card_biUnion (by intro i hi j hj hij; exact hroots i hi j hj hij)
  rw [hc, Nat.sub_self]

theorem child_overlap_intermediate (A : ι → Finset α) (s R t : Finset ι)
    (hchildren : ∀ i ∈ s, i ∉ R →
      (A i ∩ R.biUnion A).card = 1 ∧
      A i ∩ (s.erase i).biUnion A ⊆ R.biUnion A)
    (i : ι) (hi : i ∈ s) (hin : i ∉ R)
    (hRt : R ⊆ t) (ht : t ⊆ s.erase i) :
    (A i ∩ t.biUnion A).card = 1 := by
  obtain ⟨hc, hs⟩ := hchildren i hi hin
  have he : A i ∩ t.biUnion A = A i ∩ R.biUnion A := by
    apply Finset.Subset.antisymm
    · intro a ha
      obtain ⟨hai, hat⟩ := Finset.mem_inter.mp ha
      have har : a ∈ (s.erase i).biUnion A :=
        Finset.biUnion_subset_biUnion_of_subset_left A ht hat
      exact Finset.mem_inter.mpr ⟨hai, hs (Finset.mem_inter.mpr ⟨hai, har⟩)⟩
    · apply Finset.inter_subset_inter_left
      exact Finset.biUnion_subset_biUnion_of_subset_left A hRt
  rw [he, hc]

theorem child_card_eq_reuse (A : ι → Finset α) (s R : Finset ι)
    (hRs : R ⊆ s) (hroots : DisjointRoots A R)
    (hchildren : ∀ i ∈ s, i ∉ R →
      (A i ∩ R.biUnion A).card = 1 ∧
      A i ∩ (s.erase i).biUnion A ⊆ R.biUnion A) :
    (s \ R).card = (∑ i ∈ s, (A i).card) - (s.biUnion A).card := by
  have hcount (t : Finset ι) (ht : t ⊆ s \ R) :
      (∑ i ∈ R ∪ t, (A i).card) - ((R ∪ t).biUnion A).card = t.card := by
    induction t using Finset.induction_on with
    | empty => simpa using reuse_roots_eq_zero A R hroots
    | @insert i t hin ih =>
      have his : i ∈ s := (Finset.mem_sdiff.mp (ht (Finset.mem_insert_self _ _))).1
      have hinR : i ∉ R := (Finset.mem_sdiff.mp (ht (Finset.mem_insert_self _ _))).2
      have hts : t ⊆ s \ R := fun j hj => ht (Finset.mem_insert_of_mem hj)
      have hnot : i ∉ R ∪ t := by simp [hinR, hin]
      have hsub : R ∪ t ⊆ s.erase i := by
        intro j hj
        rcases Finset.mem_union.mp hj with hjR | hjt
        · exact Finset.mem_erase.mpr ⟨fun h => hinR (h ▸ hjR), hRs hjR⟩
        · exact Finset.mem_erase.mpr ⟨fun h => hin (h ▸ hjt),
            (Finset.mem_sdiff.mp (hts hjt)).1⟩
      have hoverlap := child_overlap_intermediate A s R (R ∪ t)
        hchildren i his hinR Finset.subset_union_left hsub
      rw [Finset.union_insert, Balanced.family_reuse_insert A (R ∪ t) i hnot,
        ih hts, hoverlap, Finset.card_insert_of_notMem hin]
  have h := hcount (s \ R) (fun _ h => h)
  rw [Finset.union_sdiff_of_subset hRs] at h
  exact h.symm

theorem exists_pattern_roots_exact {b κ : ℕ} (P : Local.EqualityPattern b κ)
    (hκ : κ ≤ 2) (hfit : κ ≤ 4 * b) :
    ∃ R : Finset (Fin b), DisjointRoots P.classSet R ∧
      (Finset.univ \ R).card = κ ∧
      ∀ i, i ∉ R →
        (P.classSet i ∩ R.biUnion P.classSet).card = 1 ∧
        P.classSet i ∩ (Finset.univ.erase i).biUnion P.classSet ⊆
          R.biUnion P.classSet := by
  obtain ⟨R, hroots, hchildren⟩ := exists_pattern_roots P hκ
  have hc := child_card_eq_reuse P.classSet Finset.univ R (Finset.subset_univ _)
    hroots (fun i _ hin => hchildren i hin)
  rw [P.classSet_reuse_eq hfit] at hc
  exact ⟨R, hroots, hc, hchildren⟩

theorem exists_pattern_roots_exact_of_three_le {b κ : ℕ}
    (P : Local.EqualityPattern b κ) (hb : 3 ≤ b) (hκ : κ ≤ 2) :
    ∃ R : Finset (Fin b), DisjointRoots P.classSet R ∧
      (Finset.univ \ R).card = κ ∧
      ∀ i, i ∉ R →
        (P.classSet i ∩ R.biUnion P.classSet).card = 1 ∧
        P.classSet i ∩ (Finset.univ.erase i).biUnion P.classSet ⊆
          R.biUnion P.classSet :=
  exists_pattern_roots_exact P hκ (by omega)

end Balanced.RootChildPartition

end OAI
