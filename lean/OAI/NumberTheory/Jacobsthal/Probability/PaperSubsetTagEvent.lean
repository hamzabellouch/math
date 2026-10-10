import OAI.NumberTheory.Jacobsthal.Paths.FiniteBoxWordMass

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosSubsetWord
open ErdosCofactorChoices ErdosTagEvent
open NumberTheoryLean ActualSourceTags ActualBinOwners FiniteFirstTag WrongOwnerBinMass
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels
open ErdosInversePrimeBin ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

theorem subset_bad_tag_inclusion {Y w top Cs eta xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (a : ℕ → ℤ) (q : ℚ) (hf : f ∈ selections (globalBins w top xi) mult)
    (howner : ∀ b ∈ occupiedSearch w top xi mult,
      nearFull eta (lower w top xi b) (width w top xi b) a q →
      owner Y w Cs eta (lower w top xi b) (width w top xi b) a=some q)
    (halign : ∀ b ∈ occupiedSearch w top xi mult,∀ p ∈ f b,aligns a q p)
    (hbad : ¬∃ t,sourceTag Y w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) a (descendingWord f)=some t ∧ t.rational=q) :
    (∀ b ∈ occupiedSearch w top xi mult,¬nearFull eta (lower w top xi b) (width w top xi b) a q) ∨
      ∃ b ∈ occupiedSearch w top xi mult,∃ p ∈ f b,
        p ∈ wrongOwnerPrimes Y w Cs eta (lower w top xi b) (width w top xi b) a q := by
  have hmem := (mem_selections _ mult f).mp hf
  by_cases hn : ∀ b ∈ occupiedSearch w top xi mult,
      ¬nearFull eta (lower w top xi b) (width w top xi b) a q
  · exact Or.inl hn
  · push Not at hn
    obtain ⟨b,hb,hnear⟩ := hn
    have hpos : 0 < (f b).card := by rw [(hmem b).2]; exact (Finset.mem_filter.mp hb).2.2
    obtain ⟨p,hp⟩ := Finset.card_pos.mp hpos
    have hl := selected_prime_label hw htop hxi mult f hf b hp
    have ho := howner b hb hnear
    have hs := (Finset.mem_filter.mp hb).2.1
    have hbin := (hmem b).1 hp
    have hc : tagCandidate Y w Cs eta (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a p=some (b,q) := by
      have hh := candidate_of_witness Y w Cs eta (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a p q
        (by rw [hl]; exact hbin) (by rw [hl]; exact hs) (by rw [hl]; exact ho) (halign b hb p hp)
      simpa only [hl] using hh
    obtain ⟨t,ht⟩ := sourceTag_exists_of_candidate Y w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) a (descendingWord f) ((mem_descendingWord f p).mpr ⟨b,hp⟩) hc
    have hne : t.rational ≠ q := fun he => hbad ⟨t,ht,he⟩
    obtain ⟨pre,p',tail,heq,_hindex,_hbin,hp',hsearch,hor,har,_hbefore⟩ :=
      sourceTag_witness Y w Cs eta (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a (descendingWord f) ht
    have hin : p' ∈ descendingWord f := by rw [heq]; simp
    obtain ⟨b',hin⟩ := (mem_descendingWord f p').mp hin
    have hl' := selected_prime_label hw htop hxi mult f hf b' hin
    rw [hl'] at hsearch hor hp'
    have hbpos : 0 < mult b' := by
      rw [← (hmem b').2]
      exact Finset.card_pos.mpr ⟨p',hin⟩
    have hb' : b' ∈ occupiedSearch w top xi mult := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsearch,hbpos⟩
    exact Or.inr ⟨b',hb',p',hin,Finset.mem_filter.mpr ⟨hp',halign b' hb' p' hin,t.rational,hor,hne,har⟩⟩

end ErdosSubsetWord



namespace ErdosSubsetWord
open _root_.Filter ErdosCofactorChoices ErdosTagEvent
open NumberTheoryLean ActualSourceTags ActualBinOwners FiniteFirstTag WrongOwnerBinMass
open JacobsthalSourceScale PaperBinOwners
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels
open ErdosInversePrimeBin ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

theorem source_globalBins (top xi : ℝ) :
    globalBins (sourceW (Real.log top)) top xi=actualBins top xi := rfl

theorem paper_subset_bad_tag_inclusion {Cs eta xi : ℝ} (hCs : 0 ≤ Cs) (heta : eta < 1/2)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    ∀ᶠ top : ℝ in atTop,∃ hw : 1 < sourceW (Real.log top),∃ htop : sourceW (Real.log top) < top,
      ∀ (Y : ℕ),Y ≤ ⌊top^2/(Real.log top)^2⌋₊ →
      ∀ (mult : Fin (binCount (sourceW (Real.log top)) top xi) → ℕ)
      (f : Fin (binCount (sourceW (Real.log top)) top xi) → Finset ℕ) (a : ℕ → ℤ) (q : ℚ),
      eligible Y (sourceW (Real.log top)) Cs q → f ∈ selections (actualBins top xi) mult →
      (∀ b ∈ occupiedSearch (sourceW (Real.log top)) top xi mult,∀ p ∈ f b,aligns a q p) →
      (¬∃ t,sourceTag Y (sourceW (Real.log top)) Cs eta
        (lower (sourceW (Real.log top)) top xi) (width (sourceW (Real.log top)) top xi)
        (label (zero_lt_one.trans hw) htop hxi) a (descendingWord f)=some t ∧ t.rational=q) →
      (∀ b ∈ occupiedSearch (sourceW (Real.log top)) top xi mult,
        ¬nearFull eta (lower (sourceW (Real.log top)) top xi b)
          (width (sourceW (Real.log top)) top xi b) a q) ∨
      ∃ b ∈ occupiedSearch (sourceW (Real.log top)) top xi mult,∃ p ∈ f b,
        p ∈ wrongOwnerPrimes Y (sourceW (Real.log top)) Cs eta
          (lower (sourceW (Real.log top)) top xi b) (width (sourceW (Real.log top)) top xi b) a q := by
  filter_upwards [paper_bin_span hxi hxi1,paper_owner_identifies hCs heta hxi hxi1] with top hspan hidentify
  have hw : 1 < sourceW (Real.log top) := by linarith [hspan.1]
  refine ⟨hw,hspan.2.1,?_⟩
  intro Y hY mult f a q he hf halign hbad
  apply subset_bad_tag_inclusion hw hspan.2.1 hxi mult f a q hf _ halign hbad
  intro b hb hnear
  exact hidentify Y hY b (Finset.mem_filter.mp hb).2.1 a q he hnear

end ErdosSubsetWord


end Erdos970

end OAI
