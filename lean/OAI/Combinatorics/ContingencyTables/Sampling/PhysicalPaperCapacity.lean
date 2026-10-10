import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalResidualMargins

namespace OAI

/-! # The manuscript capacity bounds every physical residual completion -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma physical_paper_capacity (small : I → J → Bool) (r : I → ℕ) (c : J → ℕ)
    (d L U : ℕ) (hd : Fintype.card I*Fintype.card J ≤ d)
    (z : PhysicalStates small (paperCapacity small r d L U) r c L) :
    ∀ i j,small i j=false →
      (∑ k,residualRows small (paperCapacity small r d L U) r c L z k) ≤
        paperCapacity small r d L U i j :=
  paper_capacity_excludes_none small
    (smallView small (physicalProfile small (paperCapacity small r d L U) r c L z) false)
    r d L U hd

end ContingencyTables.SmallGraphProfiles

end OAI
