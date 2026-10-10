import OAI.NumberTheory.Jacobsthal.Estimates.UnlistedLocalMass
import OAI.NumberTheory.Jacobsthal.Partitions.SourceRawBoxFactory

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ActualUnlistedEvent
open ErdosCofactorChoices ErdosSubsetWord ErdosVarianceEligible
open EligibleBoxLists ExpandedCompactPartition FilteredBoxWordMass UnlistedLocalMass
open LogarithmicBinScale
attribute [local instance] Classical.propDecidable

theorem selected_unlisted_le_unwitnessed_mass {w top xi Cs C B K L alpha beta eps : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Y : ℕ)
    (M : Finset (Fin (binCount w top xi) → ℕ))
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ)
    (m : Fin (binCount w top xi) → ℕ) (hm : m∈M)
    (a : ℕ → ℕ) (z : PrimeHistories.Node) (F : Finset (List ℕ)) :
    selectedWordMass (globalBins w top xi) m
      (unlistedGeometric hw htop hxi Cs C B K L alpha beta a z (eligibleLists Y w Cs M Q)
        (CountErrorClassification.badCompactWords w K eps Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a
          (SmallSieveFinite.smallEuler ⌊w⌋₊) z F)) ≤
      ∑ f∈(selections (globalBins w top xi) m).filter
        (unwitnessedSelection hw htop hxi Y Cs C B K L alpha beta eps a z (Q m)),
        (selectionProduct f:ℝ)⁻¹ := by
  simp only [selectedWordMass,Finset.sum_filter]
  apply Finset.sum_le_sum
  intro f hf
  split_ifs with hU hActual hActual
  · exact le_rfl
  · apply False.elim
    apply hActual
    exact EligibleListWord.unlisted_compact_selected_data hw htop hxi Y M Q m hm f hf a z F hU
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · exact le_rfl
end NumberTheoryLean.ActualUnlistedEvent


end Erdos970

end OAI
