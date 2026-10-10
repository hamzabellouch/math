import OAI.NumberTheory.Jacobsthal.Paths.GeometricRegularWords

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.GeometricBoxImages
open PrimeHistories ActualWordSelection ActualRegularBoxes GeometricRegularWords
open SafeSubsetBoxGeometry ErdosSubsetWord LogarithmicBinScale LogarithmicBinLabels
attribute [local instance] Classical.propDecidable

noncomputable def geometricBoxes {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (C B R L alpha beta : ℝ) (z : Node) : Finset (Fin (binCount w top xi) → ℕ) :=
  (geometricWords hw htop hxi C B R L alpha beta z).image
    (wordMultiplicity (label (zero_lt_one.trans hw) htop hxi))

theorem geometric_boxes_subset {w top xi C B R L alpha beta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (z : Node) :
    geometricBoxes hw htop hxi C B R L alpha beta z ⊆ regularBoxes hw htop hxi C B R z := by
  intro mult hm
  obtain ⟨ps,hps,rfl⟩ := Finset.mem_image.mp hm
  exact Finset.mem_image.mpr ⟨ps,(Finset.mem_filter.mp hps).1,rfl⟩

theorem geometric_box_anchor {w top xi C B R L alpha beta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (hC : 0 ≤ C) (hcomp : Real.log B ≤ 2*Real.log w)
    (hsmall : 2*(xi/Real.log w) ≤ 6*(2*C*xi)) (z : Node) :
    ∀ mult ∈ geometricBoxes hw htop hxi C B R L alpha beta z,SafeAnchor hw htop hxi C B R z mult := by
  intro mult hm
  exact regular_boxes_anchors hw htop hxi hC hcomp hsmall z mult (geometric_boxes_subset hw htop hxi z hm)

end NumberTheoryLean.GeometricBoxImages



namespace NumberTheoryLean.BinCutSelections
open ErdosCofactorChoices ErdosSubsetWord
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
attribute [local instance] Classical.propDecidable

noncomputable def aboveMultiplicity {n : ℕ} (m : Fin n → ℕ) (j : Fin n) : Fin n → ℕ :=
  fun k => if j<k then m k else 0
noncomputable def aboveSelection {n : ℕ} (f : Fin n → Finset ℕ) (j : Fin n) : Fin n → Finset ℕ :=
  fun k => if j<k then f k else ∅

noncomputable def belowMultiplicity {n : ℕ} (m : Fin n → ℕ) (j : Fin n) : Fin n → ℕ :=
  fun k => if k<j then m k else 0
noncomputable def belowSelection {n : ℕ} (f : Fin n → Finset ℕ) (j : Fin n) : Fin n → Finset ℕ :=
  fun k => if k<j then f k else ∅

theorem above_selection_mem {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (f : Fin n → Finset ℕ)
    (hf : f ∈ selections P m) (j : Fin n) : aboveSelection f j ∈ selections P (aboveMultiplicity m j) := by
  apply (mem_selections _ _ _).mpr
  intro k
  by_cases h : j<k
  · simpa only [aboveSelection,aboveMultiplicity,ite_eq_left h] using (mem_selections P m f).mp hf k
  · simp [aboveSelection,aboveMultiplicity,h]

theorem below_selection_mem {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (f : Fin n → Finset ℕ)
    (hf : f ∈ selections P m) (j : Fin n) : belowSelection f j ∈ selections P (belowMultiplicity m j) := by
  apply (mem_selections _ _ _).mpr
  intro k
  by_cases h : k<j
  · simpa only [belowSelection,belowMultiplicity,ite_eq_left h] using (mem_selections P m f).mp hf k
  · simp [belowSelection,belowMultiplicity,h]

theorem above_word_membership {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (j : Fin (binCount w top xi)) (p : ℕ) :
    p ∈ descendingWord (aboveSelection f j) ↔ p ∈ descendingWord f ∧ j<label (zero_lt_one.trans hw) htop hxi p := by
  rw [mem_descendingWord,mem_descendingWord]
  constructor
  · rintro ⟨k,hp⟩
    by_cases h : j<k
    · have hpf : p ∈ f k := by simpa only [aboveSelection,ite_eq_left h] using hp
      refine ⟨⟨k,hpf⟩,?_⟩
      rwa [selected_prime_label hw htop hxi m f hf k hpf]
    · simp [aboveSelection,h] at hp
  · rintro ⟨⟨k,hp⟩,hj⟩
    have h : j<k := by rwa [selected_prime_label hw htop hxi m f hf k hp] at hj
    exact ⟨k,by simpa only [aboveSelection,ite_eq_left h] using hp⟩

theorem below_word_membership {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (j : Fin (binCount w top xi)) (p : ℕ) :
    p ∈ descendingWord (belowSelection f j) ↔ p ∈ descendingWord f ∧ label (zero_lt_one.trans hw) htop hxi p<j := by
  rw [mem_descendingWord,mem_descendingWord]
  constructor
  · rintro ⟨k,hp⟩
    by_cases h : k<j
    · have hpf : p ∈ f k := by simpa only [belowSelection,ite_eq_left h] using hp
      refine ⟨⟨k,hpf⟩,?_⟩
      rwa [selected_prime_label hw htop hxi m f hf k hpf]
    · simp [belowSelection,h] at hp
  · rintro ⟨⟨k,hp⟩,hj⟩
    have h : k<j := by rwa [selected_prime_label hw htop hxi m f hf k hp] at hj
    exact ⟨k,by simpa only [belowSelection,ite_eq_left h] using hp⟩
end NumberTheoryLean.BinCutSelections



namespace NumberTheoryLean.SourceLabelStrictOrder
open ErdosSubsetWord LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition

theorem prime_lt_of_label_lt {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    {p q : ℕ} (hp : p ∈ sourcePrimeSet w top) (hq : q ∈ sourcePrimeSet w top)
    (hl : label (zero_lt_one.trans hw) htop hxi p<label (zero_lt_one.trans hw) htop hxi q) : p<q := by
  by_contra! hn
  exact (not_le_of_gt hl) (global_label_mono hw htop hxi hp hq hn)
end NumberTheoryLean.SourceLabelStrictOrder



namespace NumberTheoryLean.AssembleAtBin
open ErdosCofactorChoices BinCutSelections SingletonBinSelection
attribute [local instance] Classical.propDecidable

noncomputable def assemble {n : ℕ} (anchor parent : Fin n → Finset ℕ) (j : Fin n) (u : ℕ) : Fin n → Finset ℕ :=
  fun k => if j<k then parent k else if k=j then {u} else anchor k

theorem above_zero_outside {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (parent : Fin n → Finset ℕ) (j k : Fin n) (hf : parent ∈ selections P (aboveMultiplicity m j))
    (hk : ¬j<k) : parent k=∅ := by
  have hh := ((mem_selections _ _ _).mp hf k).2
  simpa only [aboveMultiplicity,ite_eq_right hk,Finset.card_eq_zero] using hh

theorem assembled_mem {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (anchor parent : Fin n → Finset ℕ) (j : Fin n) (u : ℕ)
    (ha : anchor ∈ selections P m) (hf : parent ∈ selections P (aboveMultiplicity m j))
    (hj : m j=1) (hu : u ∈ P j) : assemble anchor parent j u ∈ selections P m := by
  apply (mem_selections _ _ _).mpr
  intro k
  by_cases hk : j<k
  · have hh := (mem_selections _ _ _).mp hf k
    simpa only [assemble,aboveMultiplicity,ite_eq_left hk] using hh
  · by_cases hkj : k=j
    · subst k; simp [assemble,hj,hu]
    · simpa only [assemble,ite_eq_right hk,ite_eq_right hkj] using (mem_selections _ _ _).mp ha k

theorem assembled_above {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (anchor parent : Fin n → Finset ℕ) (j : Fin n) (u : ℕ)
    (hf : parent ∈ selections P (aboveMultiplicity m j)) :
    aboveSelection (assemble anchor parent j u) j=parent := by
  funext k
  by_cases hk : j<k
  · simp [aboveSelection,assemble,hk]
  · simp only [aboveSelection,ite_eq_right hk]
    exact (above_zero_outside P m parent j k hf hk).symm

theorem assembled_edge {n : ℕ} (anchor parent : Fin n → Finset ℕ) (j : Fin n) (u : ℕ) :
    assemble anchor parent j u j={u} := by simp [assemble]

theorem assembled_below {n : ℕ} (anchor parent : Fin n → Finset ℕ) (j : Fin n) (u : ℕ) :
    belowSelection (assemble anchor parent j u) j=belowSelection anchor j := by
  funext k
  by_cases hk : k<j
  · simp [belowSelection,assemble,hk,not_lt_of_ge hk.le,ne_of_lt hk]
  · simp [belowSelection,hk]
end NumberTheoryLean.AssembleAtBin



namespace NumberTheoryLean.BinCutGapMovement
open FinitePathGeometry PrimeHistories ErdosCofactorChoices ErdosSubsetWord BinCutSelections
open SafeSubsetBoxGeometry RepresentativeAdmission SourceStopPredicate
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinEndpoints LogarithmicBinMaps

theorem above_total_le {n : ℕ} (m : Fin n → ℕ) (j : Fin n) :
    (∑ k,aboveMultiplicity m j k) ≤ ∑ k,m k := by
  apply Finset.sum_le_sum
  intro k _
  unfold aboveMultiplicity
  split_ifs <;> omega

theorem above_word_length_le {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (j : Fin (binCount w top xi)) :
    (descendingWord (aboveSelection f j)).length ≤ ∑ k,m k := by
  rw [global_word_length hw htop hxi _ _ (above_selection_mem _ m f hf j)]
  exact above_total_le m j

theorem above_gap_movement {w top xi B C : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (hC : 0 ≤ C) (hcomp : Real.log B ≤ 2*Real.log w) (z : Node)
    (m : Fin (binCount w top xi) → ℕ) (hlen : ((∑ k,m k : ℕ):ℝ) ≤ C*Real.log B)
    (f g : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (hg : g ∈ selections (globalBins w top xi) m)
    (j : Fin (binCount w top xi)) :
    |(terminal w z (descendingWord (aboveSelection f j))).gap-
      (terminal w z (descendingWord (aboveSelection g j))).gap| ≤ 2*C*xi := by
  have hfA := above_selection_mem _ m f hf j
  have hgA := above_selection_mem _ m g hg j
  have hlF : ((descendingWord (aboveSelection f j)).length:ℝ) ≤ C*Real.log B :=
    (Nat.cast_le.mpr (above_word_length_le hw htop hxi m f hf j)).trans hlen
  have hlG : ((descendingWord (aboveSelection g j)).length:ℝ) ≤ C*Real.log B :=
    (Nat.cast_le.mpr (above_word_length_le hw htop hxi m g hg j)).trans hlen
  have hF := source_prefix_movement hw htop hxi hC hcomp z _ (word_source_membership hw htop hxi _ _ hfA) hlF
  have hG := source_prefix_movement hw htop hxi hC hcomp z _ (word_source_membership hw htop hxi _ _ hgA) hlG
  have he := selection_representatives_eq hw htop hxi _ _ _ hfA hgA
  have hrep : representativeGap (representative w (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi)) z.gap (descendingWord (aboveSelection f j))=
    representativeGap (representative w (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi)) z.gap (descendingWord (aboveSelection g j)) := by
    unfold representativeGap
    rw [he]
  rw [hrep] at hF
  exact abs_le.mpr ⟨by linarith [hF.1,hG.2],by linarith [hF.2,hG.1]⟩
end NumberTheoryLean.BinCutGapMovement


end Erdos970

end OAI
