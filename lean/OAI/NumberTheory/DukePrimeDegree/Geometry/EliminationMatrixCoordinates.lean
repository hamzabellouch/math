import OAI.NumberTheory.DukePrimeDegree.Geometry.EliminationWordEntries

namespace OAI

/-! # Each Gaussian root parameter is its corresponding matrix entry -/

noncomputable section
open Matrix Set
open scoped BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

theorem word_entry_eq_time (c : EliminationChain P D)
    (hpos : ∀ p ∈ c.finalEntries, p.1 < p.2) (t : c.Time) (k : Fin c.roots.length) :
    (c.word t).val (c.roots.get k).1 (c.roots.get k).2 = c.timeVectorHomeomorph t k := by
  have hp : c.roots.get k ∈ c.finalEntries := by
    rw [c.finalEntries_eq_union_roots]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.get_mem _ _))
  have hne := ne_of_lt (hpos _ hp)
  have H := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ =>
    M (c.roots.get k).1 (c.roots.get k).2) (c.word_val_eq_sum_single t)
  simp only [Matrix.add_apply,Matrix.sum_apply,Matrix.one_apply,ite_eq_right hne,zero_add] at H
  rw [H,Finset.sum_eq_single k]
  · simp
  · intro l _ hl
    have hr : c.roots.get l ≠ c.roots.get k :=
      fun he => hl ((c.roots_nodup hpos).injective_get he)
    rw [Matrix.single_apply]
    split_ifs with h
    · exact (hr (Prod.ext h.1 h.2)).elim
    · rfl
  · simp

end EliminationChain

theorem upperRootEuclideanCoordinates_entry (n : ℕ) (t : UpperRootTime n)
    (p : allPositiveRoots n) :
    ((completeRootChain n).word t).val p.val.1 p.val.2 = upperRootEuclideanCoordinates n t p := by
  have he : (completeRootChain n).roots.get ((upperRootIndexEquiv n).symm p) = p.val :=
    congrArg Subtype.val ((upperRootIndexEquiv n).apply_symm_apply p)
  have H := (completeRootChain n).word_entry_eq_time (by
    intro q hq
    rw [completeRootChain_final] at hq
    exact (Finset.mem_filter.mp hq).2) t ((upperRootIndexEquiv n).symm p)
  change ((completeRootChain n).word t).val p.val.1 p.val.2 =
    (completeRootChain n).timeVectorHomeomorph t ((upperRootIndexEquiv n).symm p)
  simpa only [he] using H

end DukePrimeDegree

end

end OAI
