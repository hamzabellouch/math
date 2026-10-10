import OAI.NumberTheory.Jacobsthal.Paths.CanonicalHighRatioVisit
import OAI.NumberTheory.Jacobsthal.Paths.GeometricRegularWords

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CanonicalCrossingTail
open _root_.Set _root_.Erdos970.Set _root_.Filter _root_.Erdos970.Filter
open _root_.MeasureTheory _root_.Erdos970.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures FiniteHistoryTransport FiniteHistoryOccurrence
open TransitionKernels GoodCrossingVisit CrossingBandGeometry ErdosHighRatioBandTail


theorem crossing_arrival_subset (v H T : ℝ) (N : ℕ) :
    arrivalOccurrence (crossingHighEvent v H T) N ⊆
      positiveVisit (highBand T (crossingCenter v H) crossingWidth) N := by
  intro path hp
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hp
  apply (mem_positiveVisit _ _ _).mpr
  refine ⟨⟨j.1+1,Finset.mem_Iic.mpr (Nat.succ_le_of_lt j.2)⟩,Nat.zero_lt_succ _,?_,?_⟩
  · exact hj.1.le
  · exact hj.2

theorem canonical_crossing_tail (eps : ℝ) (heps : 0 < eps) :
    ∃ T : ℝ,3 ≤ T ∧ ∀ v H : ℝ,∀ s : EvenState,199/100 ≤ s.1 → s.1 ≤ 23/10 → ∀ N : ℕ,
      finitePathMeasure (.inl s) N (arrivalOccurrence (crossingHighEvent v H T) N) ≤ ENNReal.ofReal eps := by
  obtain ⟨T,hT,hTail⟩ := exists_canonical_visit_threshold crossingWidth eps heps
  refine ⟨T,hT,?_⟩
  intro v H s h199 h23 N
  exact (measure_mono (crossing_arrival_subset v H T N)).trans (hTail T le_rfl (crossingCenter v H) s h199 h23 N)
end NumberTheoryLean.CanonicalCrossingTail


end Erdos970

end OAI
