import OAI.NumberTheory.Jacobsthal.Primes.TwoPrimeObservableSum
import OAI.NumberTheory.Jacobsthal.Sieve.CofactorAllChoiceBounds

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ParentTailPartition
open ErdosCofactorChoices SingletonBinSelection TwoSingletonBins TwoPrimeObservableSum
open BinCutSelections ParentCofactorChoices PartitionedSelections

attribute [local instance] Classical.propDecidable

noncomputable def aboveIndexSet {n : ℕ} (j : Fin n) : Finset (Fin n) := Finset.univ.filter (fun k => j<k)

theorem residual_partition_multiplicity {n : ℕ} (m : Fin n → ℕ) (i j : Fin n) (hji : j < i) :
    restrictMultiplicity (eraseTwo m i j) (aboveIndexSet j)=parentCofactorMultiplicity m i j ∧
    restrictMultiplicity (eraseTwo m i j) (aboveIndexSet j)ᶜ=belowMultiplicity m j := by
  constructor <;> funext k <;>
    simp only [restrictMultiplicity,eraseTwo,eraseMultiplicity,parentCofactorMultiplicity,
      aboveMultiplicity,belowMultiplicity,aboveIndexSet,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_compl] <;>
    split_ifs <;> omega

noncomputable def parentCofactorSelection {n : ℕ} (f : Fin n → Finset ℕ) (i j : Fin n) : Fin n → Finset ℕ :=
  eraseSelection (aboveSelection f j) i

theorem filled_parent_tail {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (i j : Fin n) (hji : j < i) (f g : Fin n → Finset ℕ)
    (hf : f ∈ selections P (parentCofactorMultiplicity m i j))
    (hg : g ∈ selections P (belowMultiplicity m j)) (p u : ℕ) :
    parentCofactorSelection (fillTwo (joinSelection (aboveIndexSet j) f g) i j p u) i j=f ∧
    belowSelection (fillTwo (joinSelection (aboveIndexSet j) f g) i j p u) j=g := by
  have hfmem := (mem_selections P _ f).mp hf
  have hgmem := (mem_selections P _ g).mp hg
  constructor <;> funext k
  · by_cases hki : k=i
    · subst k
      have he : f i=∅ := Finset.card_eq_zero.mp ((hfmem i).2.trans (cofactor_slots_zero m i j).1)
      simp [parentCofactorSelection,eraseSelection,he]
    · by_cases hjk : j<k
      · have hkj : k≠j := ne_of_gt hjk
        simp [parentCofactorSelection,eraseSelection,aboveSelection,fillTwo,fillSelection,
          joinSelection,aboveIndexSet,hki,hjk,hkj]
      · have he : f k=∅ := by
          have hh := (hfmem k).2
          simpa [parentCofactorMultiplicity,eraseMultiplicity,aboveMultiplicity,hki,hjk] using hh
        simp [parentCofactorSelection,eraseSelection,aboveSelection,hki,hjk,he]
  · by_cases hkj : k<j
    · have hki : k≠i := ne_of_lt (hkj.trans hji)
      have hkje : k≠j := ne_of_lt hkj
      simp [belowSelection,fillTwo,fillSelection,joinSelection,aboveIndexSet,hkj,hki,hkje,not_lt_of_ge hkj.le]
    · have he : g k=∅ := by
        have hh := (hgmem k).2
        simpa [belowMultiplicity,hkj] using hh
      simp [belowSelection,hkj,he]
end NumberTheoryLean.ParentTailPartition



namespace NumberTheoryLean.FourCoordinateBoxSum
open ErdosCofactorChoices SingletonBinSelection TwoSingletonBins TwoPrimeObservableSum OriginalCofactorSums
open BinCutSelections ParentCofactorChoices ParentTailPartition PartitionedSelections PartitionedSelectionSums

attribute [local instance] Classical.propDecidable

theorem four_selection_sum {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (i j : Fin n) (hji : j < i) (hi : m i=1) (hj : m j=1)
    (G : ℕ → ℕ → ℕ → ℕ → ℝ) :
    (∑ f ∈ selections P m,(selectionProduct f:ℝ)⁻¹*
      G (pickedPrime f i) (pickedPrime f j) (selectionProduct (parentCofactorSelection f i j)) (selectionProduct (belowSelection f j)))=
    ∑ p ∈ P i,∑ u ∈ P j,∑ f ∈ selections P (parentCofactorMultiplicity m i j),∑ g ∈ selections P (belowMultiplicity m j),
      ((p:ℝ)⁻¹*(u:ℝ)⁻¹*(selectionProduct f:ℝ)⁻¹*(selectionProduct g:ℝ)⁻¹)*G p u (selectionProduct f) (selectionProduct g) := by
  have hij : i≠j := ne_of_gt hji
  rw [two_singleton_weighted_sum P m i j hij hi hj]
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro u _hu
  let H : (Fin n → Finset ℕ) → ℝ := fun f =>
    G (pickedPrime (fillTwo f i j p u) i) (pickedPrime (fillTwo f i j p u) j)
      (selectionProduct (parentCofactorSelection (fillTwo f i j p u) i j))
      (selectionProduct (belowSelection (fillTwo f i j p u) j))
  change (∑ f ∈ selections P (eraseTwo m i j),((p:ℝ)⁻¹*(u:ℝ)⁻¹*(selectionProduct f:ℝ)⁻¹)*H f)=_
  calc
    _ = ∑ f ∈ selections P (eraseTwo m i j),(selectionProduct f:ℝ)⁻¹*((p:ℝ)⁻¹*(u:ℝ)⁻¹*H f) := by
      apply Finset.sum_congr rfl
      intro f _hf
      ring
    _ = _ := by
      rw [partitioned_weighted_sum P (eraseTwo m i j) (aboveIndexSet j)]
      have he := residual_partition_multiplicity m i j hji
      rw [he.1,he.2]
      apply Finset.sum_congr rfl
      intro f hf
      apply Finset.sum_congr rfl
      intro g hg
      have hpick := picked_fillTwo (joinSelection (aboveIndexSet j) f g) i j hij p u
      have hsplit := filled_parent_tail P m i j hji f g hf hg p u
      dsimp only [H]
      rw [hpick.1,hpick.2,hsplit.1,hsplit.2]
      ring

theorem four_coordinate_sum {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (hP : ∀ i,∀ p ∈ P i,p.Prime) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (i j : Fin n) (hji : j < i) (hi : m i=1) (hj : m j=1) (G : ℕ → ℕ → ℕ → ℕ → ℝ) :
    (∑ f ∈ selections P m,(selectionProduct f:ℝ)⁻¹*
      G (pickedPrime f i) (pickedPrime f j) (selectionProduct (parentCofactorSelection f i j)) (selectionProduct (belowSelection f j)))=
    ∑ p ∈ P i,∑ u ∈ P j,∑ q ∈ cofactorChoices P (parentCofactorMultiplicity m i j),∑ d ∈ cofactorChoices P (belowMultiplicity m j),
      ((p:ℝ)⁻¹*(u:ℝ)⁻¹*(q:ℝ)⁻¹*(d:ℝ)⁻¹)*G p u q d := by
  rw [four_selection_sum P m i j hji hi hj]
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro u _hu
  calc
    _ = ∑ f ∈ selections P (parentCofactorMultiplicity m i j),∑ d ∈ cofactorChoices P (belowMultiplicity m j),
        ((p:ℝ)⁻¹*(u:ℝ)⁻¹*(selectionProduct f:ℝ)⁻¹*(d:ℝ)⁻¹)*G p u (selectionProduct f) d := by
      apply Finset.sum_congr rfl
      intro f _hf
      exact cofactor_sum P (belowMultiplicity m j) hP hd (fun d =>
        ((p:ℝ)⁻¹*(u:ℝ)⁻¹*(selectionProduct f:ℝ)⁻¹*(d:ℝ)⁻¹)*G p u (selectionProduct f) d)
    _ = _ := cofactor_sum P (parentCofactorMultiplicity m i j) hP hd (fun q =>
      ∑ d ∈ cofactorChoices P (belowMultiplicity m j),((p:ℝ)⁻¹*(u:ℝ)⁻¹*(q:ℝ)⁻¹*(d:ℝ)⁻¹)*G p u q d)
end NumberTheoryLean.FourCoordinateBoxSum



namespace NumberTheoryLean.ActualBoxFourSum
open ErdosCofactorChoices ErdosSubsetWord FourCoordinateBoxSum TwoPrimeObservableSum ParentTailPartition
open BinCutSelections ParentCofactorChoices
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinEndpoints


theorem actual_box_four_coordinate_sum {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (i j : Fin (binCount w top xi))
    (hji : j < i) (hi : m i=1) (hj : m j=1) (G : ℕ → ℕ → ℕ → ℕ → ℝ) :
    (∑ f ∈ selections (globalBins w top xi) m,(selectionProduct f:ℝ)⁻¹*
      G (pickedPrime f i) (pickedPrime f j) (selectionProduct (parentCofactorSelection f i j)) (selectionProduct (belowSelection f j)))=
    ∑ p ∈ globalBins w top xi i,∑ u ∈ globalBins w top xi j,
      ∑ q ∈ cofactorChoices (globalBins w top xi) (parentCofactorMultiplicity m i j),
      ∑ d ∈ cofactorChoices (globalBins w top xi) (belowMultiplicity m j),
      ((p:ℝ)⁻¹*(u:ℝ)⁻¹*(q:ℝ)⁻¹*(d:ℝ)⁻¹)*G p u q d :=
  four_coordinate_sum (globalBins w top xi) m
    (fun k _p hp => (bin_prime_in_source (zero_lt_one.trans hw) htop hxi k hp).1)
    (fun k l hkl => bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi k l hkl) i j hji hi hj G
end NumberTheoryLean.ActualBoxFourSum


end Erdos970

end OAI
