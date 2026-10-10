import OAI.GroupTheory.PolycyclicRecognition.Algebra.PositiveZeroSums
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! # Compact convex hulls in the finite character space

Only dimension-plus-one tuples are needed, by Carathéodory. Their coefficient
simplex and their point tuples are compact, so their finite union is compact.
-/

noncomputable section
namespace PolycyclicRecognition
open Convexity Set
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def finiteConvexCombinationRange (C : Set E) (n : ℕ) : Set E :=
  Set.range (fun p : StdSimplex ℝ (Fin n) × (Fin n → C) =>
    ∑ i, p.1.weights i • (p.2 i : E))

theorem finiteConvexCombinationRange_compact {C : Set E} (hC : IsCompact C) (n : ℕ) :
    IsCompact (finiteConvexCombinationRange C n) := by
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  apply isCompact_range
  fun_prop

theorem finiteConvexCombinationRange_subset (C : Set E) (n : ℕ) :
    finiteConvexCombinationRange C n ⊆ convexHull ℝ C := by
  rintro x ⟨p, rfl⟩
  exact (convex_convexHull ℝ C).sum_mem
    (fun i _ => p.1.weights_nonneg i) (by simp)
    (fun i _ => subset_convexHull ℝ C (p.2 i).property)

theorem mem_small_finiteConvexCombinationRange [FiniteDimensional ℝ E]
    {C : Set E} {x : E} (hx : x ∈ convexHull ℝ C) :
    ∃ n ≤ Module.finrank ℝ E + 1, x ∈ finiteConvexCombinationRange C n := by
  classical
  obtain ⟨ι, hi, z, w, hz, haff, hw, hsum, hzx⟩ := eq_pos_convex_span_of_mem_convexHull hx
  let := hi
  let f := Fintype.equivFin ι
  let a : StdSimplex ℝ (Fin (Fintype.card ι)) :=
    { weights := Finsupp.equivFunOnFinite.symm (fun i => w (f.symm i))
      nonneg := by intro i; simpa using (hw (f.symm i)).le
      total := by
        rw [Finsupp.sum_fintype _ _ (by simp)]
        change (∑ i, w (f.symm i)) = 1
        exact (f.symm.sum_comp w).trans hsum }
  refine ⟨Fintype.card ι,
    haff.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1), ?_⟩
  refine ⟨(a, fun i => ⟨z (f.symm i), hz (mem_range_self _)⟩), ?_⟩
  change (∑ i, w (f.symm i) • z (f.symm i)) = x
  exact (f.symm.sum_comp (fun i => w i • z i)).trans hzx

theorem compact_finiteDimensional_convexHull [FiniteDimensional ℝ E]
    {C : Set E} (hC : IsCompact C) : IsCompact (convexHull ℝ C) := by
  classical
  have he : convexHull ℝ C =
      ⋃ n ∈ Finset.range (Module.finrank ℝ E + 2), finiteConvexCombinationRange C n := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn, hx⟩ := mem_small_finiteConvexCombinationRange hx
      exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega), hx⟩⟩
    · intro hx
      obtain ⟨n, hx⟩ := mem_iUnion.mp hx
      obtain ⟨_, hx⟩ := mem_iUnion.mp hx
      exact finiteConvexCombinationRange_subset C n hx
  rw [he]
  exact (Finset.range _).finite_toSet.isCompact_biUnion
    (fun n _ => finiteConvexCombinationRange_compact hC n)

end PolycyclicRecognition

end

end OAI
