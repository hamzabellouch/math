import OAI.NumberTheory.Jacobsthal.Paths.FullWordHighAlignment
import OAI.NumberTheory.Jacobsthal.Primes.SourcePrimeProductData

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.FullIsolatedCofactor
open ErdosCofactorChoices ErdosSubsetWord ErdosInverseAlignment
open SingletonBinSelection SingletonBinProduct TwoPrimeObservableSum
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinEndpoints LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure


theorem isolated_product {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (f : Fin n → Finset ℕ) (hf : f∈selections P m) (i : Fin n) (hi : m i=1) :
    selectionProduct f=pickedPrime f i*selectionProduct (eraseSelection f i) := by
  obtain ⟨p,_hp,hfi,hfill⟩ := singleton_selection_recovery P m i hi f hf
  have hprod := filled_product (eraseSelection f i) i p (by simp [eraseSelection])
  rw [hfill] at hprod
  simpa [pickedPrime,hfi] using hprod

theorem full_word_isolated_product {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f∈selections (globalBins w top xi) m) (i : Fin (binCount w top xi)) (hi : m i=1) :
    (descendingWord f).prod=pickedPrime f i*selectionProduct (eraseSelection f i) := by
  rw [descendingWord_product (globalBins w top xi)
    (fun k l hkl => bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi k l hkl)
    f (fun k => ((mem_selections _ _ _).mp hf k).1)]
  exact isolated_product _ m f hf i hi

theorem full_cofactor_alignment_word {w top xi Cs : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f∈selections (globalBins w top xi) m) (i : Fin (binCount w top xi)) (hi : m i=1)
    (a : ℕ → ℤ) (q : ℚ)
    (ha : ∀ p∈(pickedPrime f i*selectionProduct (eraseSelection f i)).primeFactors,
      Cs < primeExponent w p → aligns a q p) :
    ∀ p∈descendingWord f,Cs < primeExponent w p → aligns a q p := by
  intro p hp hhigh
  apply ha p _ hhigh
  rw [← isolated_product _ m f hf i hi,
    selectionProduct_primeFactors (globalBins w top xi)
      (fun k _p hp => (bin_prime_in_source (zero_lt_one.trans hw) htop hxi k hp).1)
      (fun k l hkl => bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi k l hkl)
      f (fun k => ((mem_selections _ _ _).mp hf k).1)]
  obtain ⟨k,hpk⟩ := (mem_descendingWord f p).mp hp
  exact Finset.mem_biUnion.mpr ⟨k,Finset.mem_univ _,hpk⟩
end NumberTheoryLean.FullIsolatedCofactor



namespace NumberTheoryLean.EndpointCofactorSplit
open ErdosCofactorChoices ErdosSubsetWord SingletonBinSelection TwoPrimeObservableSum
open ParentTailPartition ParentCofactorChoices BinCutSelections SelectionWordSplit
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinEndpoints LogarithmicBinPartition


theorem endpoint_cofactor_split {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f∈selections (globalBins w top xi) m) (i j : Fin (binCount w top xi))
    (hji : j < i) (hj : m j=1) :
    selectionProduct (eraseSelection f i)=selectionProduct (parentCofactorSelection f i j)*
      (pickedPrime f j*selectionProduct (belowSelection f j)) := by
  obtain ⟨u,_hu,hfu,_hfill⟩ := singleton_selection_recovery _ m j hj f hf
  have hfi : eraseSelection f i j={u} := by simp [eraseSelection,ne_of_lt hji,hfu]
  have hErase := erase_selection_mem _ m f hf i
  have hParent := erase_selection_mem _ _ _ (above_selection_mem _ m f hf j) i
  have hBelow := below_selection_mem _ m f hf j
  have hA : aboveSelection (eraseSelection f i) j=parentCofactorSelection f i j := by
    funext k
    by_cases hki : k=i <;> by_cases hjk : j < k <;>
      simp [aboveSelection,eraseSelection,parentCofactorSelection,hki,hjk]
  have hD : belowSelection (eraseSelection f i) j=belowSelection f j := by
    funext k
    by_cases hki : k=i
    · subst k
      simp [belowSelection,not_lt_of_ge hji.le]
    · simp [belowSelection,eraseSelection,hki]
  have hd : Pairwise (fun k l => Disjoint (globalBins w top xi k) (globalBins w top xi l)) :=
    fun k l hkl => bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi k l hkl
  have hword := selected_word_split hw htop hxi _ _ hErase j u hfi
  have hprod := congrArg List.prod hword
  rw [List.prod_append,List.prod_cons,hA,hD] at hprod
  rw [descendingWord_product _ hd _ (fun k => ((mem_selections _ _ _).mp hErase k).1),
    descendingWord_product _ hd (parentCofactorSelection f i j) (fun k => ((mem_selections _ _ _).mp hParent k).1),
    descendingWord_product _ hd _ (fun k => ((mem_selections _ _ _).mp hBelow k).1)] at hprod
  simpa [pickedPrime,hfu] using hprod

theorem endpoint_extra_factor_pos {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f∈selections (globalBins w top xi) m) (j : Fin (binCount w top xi)) (hj : m j=1) :
    0 < pickedPrime f j*selectionProduct (belowSelection f j) := by
  obtain ⟨u,hu,hfu,_hfill⟩ := singleton_selection_recovery _ m j hj f hf
  have hp : 0 < pickedPrime f j := by
    simpa [pickedPrime,hfu] using (bin_prime_in_source (zero_lt_one.trans hw) htop hxi j hu).1.pos
  have hd : 0 < selectionProduct (belowSelection f j) := selectionProduct_pos (globalBins w top xi)
    (fun k _p hp => (bin_prime_in_source (zero_lt_one.trans hw) htop hxi k hp).1) _
    (fun k => ((mem_selections _ _ _).mp (below_selection_mem _ m f hf j) k).1)
  exact Nat.mul_pos hp hd
end NumberTheoryLean.EndpointCofactorSplit


end Erdos970

end OAI
