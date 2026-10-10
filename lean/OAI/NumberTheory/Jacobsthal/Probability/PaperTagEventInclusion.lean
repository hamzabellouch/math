import OAI.NumberTheory.Jacobsthal.Partitions.ActualPatternCoordinates

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosTagEvent
open NumberTheoryLean ActualSourceTags ActualBinOwners FiniteFirstTag
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels
open PrimeChoiceBoxMass WrongOwnerBinMass ErdosInversePrimeBin ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

theorem pattern_bad_tag_inclusion {m : ℕ} {Y w top Cs eta xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (pattern : Fin m → Fin (binCount w top xi)) (f : Fin m → ℕ) (a : ℕ → ℤ) (q : ℚ)
    (hf : f ∈ choices (patternBins w top xi pattern))
    (howner : ∀ i ∈ searchPositions w top xi pattern,
      nearFull eta (lower w top xi (pattern i)) (width w top xi (pattern i)) a q →
      owner Y w Cs eta (lower w top xi (pattern i)) (width w top xi (pattern i)) a=some q)
    (halign : ∀ i ∈ searchPositions w top xi pattern,aligns a q (f i))
    (hbad : ¬∃ t,sourceTag Y w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) a (List.ofFn f)=some t ∧ t.rational=q) :
    (∀ i ∈ searchPositions w top xi pattern,
      ¬nearFull eta (lower w top xi (pattern i)) (width w top xi (pattern i)) a q) ∨
      ∃ i ∈ searchPositions w top xi pattern,f i ∈
        wrongOwnerPrimes Y w Cs eta (lower w top xi (pattern i)) (width w top xi (pattern i)) a q := by
  by_cases hnone : ∀ i ∈ searchPositions w top xi pattern,
      ¬nearFull eta (lower w top xi (pattern i)) (width w top xi (pattern i)) a q
  · exact Or.inl hnone
  · push Not at hnone
    obtain ⟨i,hi,hnear⟩ := hnone
    have ho := howner i hi hnear
    have hl := actual_choice_label hw htop hxi pattern f hf i
    have hp := actual_choice_coordinate pattern f hf i
    have hs := (Finset.mem_filter.mp hi).2
    have hc : tagCandidate Y w Cs eta (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a (f i)=some (pattern i,q) := by
      have hh := candidate_of_witness Y w Cs eta (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a (f i) q
        (by rw [hl]; exact hp) (by rw [hl]; exact hs) (by rw [hl]; exact ho) (halign i hi)
      simpa only [hl] using hh
    obtain ⟨t,ht⟩ := sourceTag_exists_of_candidate Y w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) a (List.ofFn f) (List.mem_ofFn.mpr ⟨i,rfl⟩) hc
    have hne : t.rational ≠ q := fun he => hbad ⟨t,ht,he⟩
    obtain ⟨j,hj,_hbin,hor,har⟩ := first_tag_coordinate hw htop hxi pattern f a hf t ht
    refine Or.inr ⟨j,hj,?_⟩
    exact Finset.mem_filter.mpr ⟨actual_choice_coordinate pattern f hf j,
      halign j hj,t.rational,hor,hne,har⟩

theorem nonnearfull_card_lt (eta R xi : ℝ) (a : ℕ → ℤ) (q : ℚ)
    (hn : ¬nearFull eta R xi a q) :
    (((primeBin R xi).filter (aligns a q)).card:ℝ) < (1-eta)*((primeBin R xi).card:ℝ) :=
  lt_of_not_ge hn

end ErdosTagEvent



namespace ErdosTagEvent
open _root_.Filter NumberTheoryLean ActualSourceTags ActualBinOwners FiniteFirstTag
open JacobsthalSourceScale PaperBinOwners
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels
open PrimeChoiceBoxMass WrongOwnerBinMass ErdosInversePrimeBin ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

theorem paper_bad_tag_inclusion {Cs eta xi : ℝ} (hCs : 0 ≤ Cs) (heta : eta < 1/2)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    ∀ᶠ top : ℝ in atTop,∃ hw : 1 < sourceW (Real.log top),∃ htop : sourceW (Real.log top) < top,
      ∀ (Y : ℕ),Y ≤ ⌊top^2/(Real.log top)^2⌋₊ → ∀ (m : ℕ)
      (pattern : Fin m → Fin (binCount (sourceW (Real.log top)) top xi)) (f : Fin m → ℕ)
      (a : ℕ → ℤ) (q : ℚ),eligible Y (sourceW (Real.log top)) Cs q →
      f ∈ choices (patternBins (sourceW (Real.log top)) top xi pattern) →
      (∀ i ∈ searchPositions (sourceW (Real.log top)) top xi pattern,aligns a q (f i)) →
      (¬∃ t,sourceTag Y (sourceW (Real.log top)) Cs eta
        (lower (sourceW (Real.log top)) top xi) (width (sourceW (Real.log top)) top xi)
        (label (zero_lt_one.trans hw) htop hxi) a (List.ofFn f)=some t ∧ t.rational=q) →
      (∀ i ∈ searchPositions (sourceW (Real.log top)) top xi pattern,
        ¬nearFull eta (lower (sourceW (Real.log top)) top xi (pattern i))
          (width (sourceW (Real.log top)) top xi (pattern i)) a q) ∨
      ∃ i ∈ searchPositions (sourceW (Real.log top)) top xi pattern,f i ∈
        wrongOwnerPrimes Y (sourceW (Real.log top)) Cs eta
          (lower (sourceW (Real.log top)) top xi (pattern i))
          (width (sourceW (Real.log top)) top xi (pattern i)) a q := by
  filter_upwards [paper_bin_span hxi hxi1,paper_owner_identifies hCs heta hxi hxi1] with top hspan hidentify
  have hw : 1 < sourceW (Real.log top) := by linarith [hspan.1]
  refine ⟨hw,hspan.2.1,?_⟩
  intro Y hY m pattern f a q he hf halign hbad
  apply pattern_bad_tag_inclusion hw hspan.2.1 hxi pattern f a q hf _ halign hbad
  intro i hi hnear
  exact hidentify Y hY (pattern i) (Finset.mem_filter.mp hi).2 a q he hnear

theorem bad_aligned_subset_wrong {m : ℕ} {Y w top Cs eta xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (pattern : Fin m → Fin (binCount w top xi)) (a : ℕ → ℤ) (q : ℚ)
    (howner : ∀ i ∈ searchPositions w top xi pattern,
      nearFull eta (lower w top xi (pattern i)) (width w top xi (pattern i)) a q →
      owner Y w Cs eta (lower w top xi (pattern i)) (width w top xi (pattern i)) a=some q)
    (hnear : ∃ i ∈ searchPositions w top xi pattern,
      nearFull eta (lower w top xi (pattern i)) (width w top xi (pattern i)) a q) :
    ((alignedChoices (patternBins w top xi pattern) (searchPositions w top xi pattern) a q).filter
      (fun f => ¬∃ t,sourceTag Y w Cs eta (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a (List.ofFn f)=some t ∧ t.rational=q)) ⊆
      (choices (patternBins w top xi pattern)).filter (fun f =>
        ∃ i ∈ searchPositions w top xi pattern,f i ∈
          wrongOwnerPrimes Y w Cs eta (lower w top xi (pattern i)) (width w top xi (pattern i)) a q) := by
  intro f hf
  obtain ⟨hfa,hbad⟩ := Finset.mem_filter.mp hf
  obtain ⟨hchoice,halign⟩ := Finset.mem_filter.mp hfa
  have h := pattern_bad_tag_inclusion hw htop hxi pattern f a q hchoice howner halign hbad
  rcases h with hnone | hwrong
  · obtain ⟨i,hi,hnear⟩ := hnear
    exact False.elim (hnone i hi hnear)
  · exact Finset.mem_filter.mpr ⟨hchoice,hwrong⟩

end ErdosTagEvent


end Erdos970

end OAI
