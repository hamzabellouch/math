import OAI.NumberTheory.Ostmann.Characters.CycleAction
import OAI.NumberTheory.Ostmann.Tree.IncidenceCycle

namespace OAI

/-!
# The two-edge cycle

Two leaves in the same component and the same quartet give a balanced
sign vector supported on precisely those two leaves. No additional
assumption is needed for this degenerate cycle.
-/

namespace Ostmann

open scoped BigOperators

def parallelCycleSign {I : Type*} [DecidableEq I] (i j k : I) : ℤ :=
  (if k = i then 1 else 0) - (if k = j then 1 else 0)

theorem parallelCycleSign_left {I : Type*} [DecidableEq I] (i j : I) (hij : i ≠ j) :
    parallelCycleSign i j i = 1 := by simp [parallelCycleSign, hij]

theorem parallelCycleSign_right {I : Type*} [DecidableEq I] (i j : I) (hij : i ≠ j) :
    parallelCycleSign i j j = -1 := by simp [parallelCycleSign, Ne.symm hij]

theorem parallelCycleSign_other {I : Type*} [DecidableEq I] (i j k : I)
    (hki : k ≠ i) (hkj : k ≠ j) : parallelCycleSign i j k = 0 := by
  simp [parallelCycleSign, hki, hkj]

theorem sum_parallelCycleSign {I : Type*} [DecidableEq I] (s : Finset I) (i j : I) :
    (∑ k ∈ s, parallelCycleSign i j k) =
      (if i ∈ s then 1 else 0) - (if j ∈ s then 1 else 0) := by
  simp [parallelCycleSign, Finset.sum_sub_distrib]

/-- The same block membership cancels the two signs. -/
theorem parallelCycleSign_balanced {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (block : I → J) (i j : I) (hij : block i = block j) (b : J) :
    (∑ k ∈ Finset.univ.filter (fun k => block k = b), parallelCycleSign i j k) = 0 := by
  rw [sum_parallelCycleSign]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hij, sub_self]

/-- Reciprocal multiplication on parallel leaves preserves every component product. -/
theorem parallelCycle_preserves_blocks {I J G : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq J] [CommGroup G] (block : I → J) (i j : I)
    (hij : block i = block j) (b : J) (z : G) (m : I → G) :
    (∏ k ∈ Finset.univ.filter (fun k => block k = b),
      cycleMultiply (parallelCycleSign i j) z m k) =
      ∏ k ∈ Finset.univ.filter (fun k => block k = b), m k := by
  exact cycleMultiply_preserves_product _ _ (parallelCycleSign_balanced block i j hij b) z m

end Ostmann

end OAI
