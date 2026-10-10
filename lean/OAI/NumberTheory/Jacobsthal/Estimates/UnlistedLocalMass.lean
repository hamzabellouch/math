import OAI.NumberTheory.Jacobsthal.Paths.OutsideExceptionsWitness

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.UnlistedLocalMass
open ErdosCofactorChoices ErdosSubsetWord ErdosInverseAlignment
open EligibleListWord EligibleBoxLists ExpandedCompactPartition ActualBinOwners FilteredBoxWordMass
open LogarithmicBinScale ErdosPrimeInputs.HarmonicPrimeMeasure

attribute [local instance] Classical.propDecidable

theorem unlisted_mass_le_local_event {w top xi Cs C B K L alpha beta eps : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Y : ℕ)
    (M : Finset (Fin (binCount w top xi) → ℕ))
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ)
    (m : Fin (binCount w top xi) → ℕ) (hm : m∈M)
    (a : ℕ → ℕ) (z : PrimeHistories.Node) (F : Finset (List ℕ)) :
    selectedWordMass (globalBins w top xi) m
      (unlistedGeometric hw htop hxi Cs C B K L alpha beta a z (eligibleLists Y w Cs M Q)
        (CountErrorClassification.badCompactWords w K eps Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a
          (SmallSieveFinite.smallEuler ⌊w⌋₊) z F)) ≤
    ∑ f∈(selections (globalBins w top xi) m).filter (fun f =>
      descendingWord f∈GeometricRegularWords.geometricWords hw htop hxi C B K L alpha beta z ∧
      eps < |ActualCountErrorEdges.wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a
        (SmallSieveFinite.smallEuler ⌊w⌋₊) (descendingWord f)| ∧
      ¬∃ q∈Q m,eligible Y w Cs q ∧
        ∀ p∈descendingWord f,Cs < primeExponent w p → aligns (SourceStopPredicate.sourceClass a) q p),
      (selectionProduct f:ℝ)⁻¹ := by
  simp only [selectedWordMass,Finset.sum_filter]
  apply Finset.sum_le_sum
  intro f hf
  split_ifs with hU hLocal hLocal
  · exact le_rfl
  · exact False.elim (hLocal (unlisted_compact_selected_data hw htop hxi Y M Q m hm f hf a z F hU))
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · exact le_rfl
end NumberTheoryLean.UnlistedLocalMass


end Erdos970

end OAI
