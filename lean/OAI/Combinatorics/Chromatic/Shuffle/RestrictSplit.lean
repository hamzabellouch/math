import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.Split

namespace OAI

section
namespace ElementaryPositivity.ShuffleConvolution
variable {A : Type*} [Fintype A] [DecidableEq A]

def restrictSplit {s t : Finset A} (ht : t ⊆ s) (q : Split s) : Split t :=
  ⟨(q.val.1 ∩ t,q.val.2 ∩ t),q.property.1.mono Finset.inter_subset_left Finset.inter_subset_left,by
    change (q.val.1 ∩ t) ∪ (q.val.2 ∩ t) = t
    rw [← Finset.union_inter_distrib_right,q.property.2]
    exact Finset.inter_eq_right.mpr ht⟩

def grid {s : Finset A} (p : Split s) : Split s ≃ Split p.val.1 × Split p.val.2 where
  toFun q := (restrictSplit p.left_subset q,restrictSplit p.right_subset q)
  invFun q := ⟨(q.1.val.1 ∪ q.2.val.1,q.1.val.2 ∪ q.2.val.2),by
    constructor
    · apply Finset.disjoint_union_left.mpr
      constructor
      · apply Finset.disjoint_union_right.mpr
        exact ⟨q.1.property.1,p.property.1.mono q.1.left_subset q.2.right_subset⟩
      · apply Finset.disjoint_union_right.mpr
        exact ⟨p.property.1.symm.mono q.2.left_subset q.1.right_subset,q.2.property.1⟩
    · calc
        (q.1.val.1 ∪ q.2.val.1) ∪ (q.1.val.2 ∪ q.2.val.2) =
            (q.1.val.1 ∪ q.1.val.2) ∪ (q.2.val.1 ∪ q.2.val.2) := by ac_rfl
        _ = s := by rw [q.1.property.2,q.2.property.2,p.property.2]⟩
  left_inv q := by
    apply Subtype.ext
    dsimp [restrictSplit]
    congr 1
    · rw [← Finset.inter_union_distrib_left,p.property.2]
      exact Finset.inter_eq_left.mpr q.left_subset
    · rw [← Finset.inter_union_distrib_left,p.property.2]
      exact Finset.inter_eq_left.mpr q.right_subset
  right_inv q := by
    apply Prod.ext <;> apply Subtype.ext
    · dsimp [restrictSplit]
      have h1 := p.property.1.symm.mono_left q.2.left_subset
      have h2 := p.property.1.symm.mono_left q.2.right_subset
      rw [Finset.union_inter_distrib_right,Finset.union_inter_distrib_right,
        Finset.inter_eq_left.mpr q.1.left_subset,Finset.inter_eq_left.mpr q.1.right_subset,
        Finset.disjoint_iff_inter_eq_empty.mp h1,Finset.disjoint_iff_inter_eq_empty.mp h2]
      simp
    · dsimp [restrictSplit]
      have h1 := p.property.1.mono_left q.1.left_subset
      have h2 := p.property.1.mono_left q.1.right_subset
      rw [Finset.union_inter_distrib_right,Finset.union_inter_distrib_right,
        Finset.inter_eq_left.mpr q.2.left_subset,Finset.inter_eq_left.mpr q.2.right_subset,
        Finset.disjoint_iff_inter_eq_empty.mp h1,Finset.disjoint_iff_inter_eq_empty.mp h2]
      simp

end ElementaryPositivity.ShuffleConvolution

end

end OAI
