import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationSelectedCost

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
open Construction Conclusion HistoryPairPattern HistoryPairRows HistoryPairFlags
open HistoryPairRepresentatives HistorySelectedFlagMassBounds HistoryUnnormalizedFlagError

theorem selectedUnitBudget_reindex (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ) {l : ℕ}
    (h g : History l) {β : Type*} [Fintype β] (e : Representative h g ≃ β) :
    selectedUnitBudget Bs BD Bz k L h g=
      ∑q : β,errorBudget 1
        (((2*Fintype.card (Fiber h g (e.symm q))+(Fintype.card (Fiber h g (e.symm q)))^2:ℕ):ℝ))
        (((4*degreeBudget h g:ℕ):ℝ))
        (max 0 (Real.log (envelope h g (frequencyBound Bs BD Bz k L)
          (HistorySignedResidues.actualFactorCap Bs BD Bz k L)))/Real.log 2)
        (atomCap k L) (massCap k L) (Fintype.card (PairKey h g)) :=
  (e.symm.sum_comp _).symm

end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation

end

end OAI
