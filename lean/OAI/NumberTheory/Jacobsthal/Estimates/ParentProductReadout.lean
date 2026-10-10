import OAI.NumberTheory.Jacobsthal.Paths.GeometricEdgeWitness

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ParentProductReadout
open ErdosCofactorChoices ErdosSubsetWord SingletonBinSelection SingletonBinProduct TwoPrimeObservableSum ParentTailPartition
open PrimeHistories BinCutSelections BinCutPrefixGeometry SelectionWordSplit GeometricEdgeWitness
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition

attribute [local instance] Classical.propDecidable

theorem parent_product_readout {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (f : Fin n → Finset ℕ) (hf : f ∈ selections P m) (i j : Fin n) (hji : j < i) (hi : m i=1) :
    selectionProduct (aboveSelection f j)=pickedPrime f i*selectionProduct (parentCofactorSelection f i j) := by
  obtain ⟨p,_hp,hfi,_⟩ := singleton_selection_recovery P m i hi f hf
  have hA : aboveSelection f j i={p} := by simp [aboveSelection,hji,hfi]
  have hpick : pickedPrime f i=p := by simp [pickedPrime,hfi]
  have he : eraseSelection (aboveSelection f j) i i=∅ := by simp [eraseSelection]
  have hh := filled_product (eraseSelection (aboveSelection f j) i) i p he
  rw [fill_erase (aboveSelection f j) i p hA,← hpick] at hh
  exact hh

theorem actual_prefix_product_readout {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (i j : Fin (binCount w top xi)) (hji : j < i) (hi : m i=1)
    (pre tail : List ℕ) (u : ℕ) (he : descendingWord f=pre++u::tail) (hfu : f j={u}) :
    pre.prod=pickedPrime f i*selectionProduct (parentCofactorSelection f i j) ∧ pickedPrime f j=u := by
  have hsplit := selected_word_split hw htop hxi m f hf j u hfu
  have hpre := decreasing_edge_prefix_unique (descendingWord f) pre tail (descendingWord (aboveSelection f j))
    (descendingWord (belowSelection f j)) u (descendingWord_strict f) he hsplit
  refine ⟨?_,by simp [pickedPrime,hfu]⟩
  rw [hpre,above_word_product hw htop hxi m f hf j]
  exact parent_product_readout (globalBins w top xi) m f hf i j hji hi
end NumberTheoryLean.ParentProductReadout


end Erdos970

end OAI
