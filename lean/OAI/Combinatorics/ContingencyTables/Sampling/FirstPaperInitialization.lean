import OAI.Combinatorics.ContingencyTables.Sampling.GreedyFeasibleTable
import OAI.Combinatorics.ContingencyTables.Transport.ReferenceFiniteDraw
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperSuccessEvent

namespace OAI

/-! # Concrete initial state and completion fallbacks -/

namespace ContingencyTables.GreedyFeasibleTable

open scoped BigOperators

/-- Reindex the row/column recursion without changing its arithmetic. -/
noncomputable def reindexed {I J : Type*} [Fintype I] [Fintype J]
    (r : I → ℕ) (c : J → ℕ) (h : (∑ i,r i)=∑ j,c j) : Table r c :=
  (tableReindex (Fintype.equivFin I).symm (Fintype.equivFin J).symm r c).symm
    (table (fun i => r ((Fintype.equivFin I).symm i))
      (fun j => c ((Fintype.equivFin J).symm j)) (by
        rw [(Fintype.equivFin I).symm.sum_comp,(Fintype.equivFin J).symm.sum_comp]
        exact h))

end ContingencyTables.GreedyFeasibleTable

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open CompletionCounts

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)

/-- The image of a greedily filled original table is an actual positive
small state with its own successful retained completion. -/
def initialJoint (htotal : (∑ i,r i)=∑ j,c j) : PaperStateJoint r c :=
  (originalStateSuccessEquiv r c (GreedyFeasibleTable.reindexed r c htotal)).val

lemma initialJoint_success (htotal : (∑ i,r i)=∑ j,c j) :
    StateJointSuccess r c (initialJoint r c htotal) :=
  (originalStateSuccessEquiv r c (GreedyFeasibleTable.reindexed r c htotal)).property

variable (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
variable (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))

/-- A fallback is computed for the current residual margins, then moved
back through the entry-preserving completion equivalence. -/
def greedyFibre (z : PaperStates r c) : PaperFibre r c z :=
  (paperReferenceEquiv r c i₀ j₀ z).symm
    (GreedyFeasibleTable.reindexed
      (referenceRows r c _ _ (stateCapacity r c) i₀ z)
      (referenceColumns r c _ _ (stateCapacity r c) j₀ z)
      (reference_totals r c _ _ _ i₀ j₀ z
        (physical_paper_capacity _ r c _ _ _ dimension_le_allowance z)))

end
end ContingencyTables.SmallGraphProfiles

end OAI
