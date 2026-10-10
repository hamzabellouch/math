import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceForwardRBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceForwardR
open Construction HistorySignedDecode HistorySignedSupportReduction
open HistorySignedResidueFactorization HistoryFrequencyResidues HistorySupportReduction
open HistoryBulkSupportConverse HistoryBulkFrequencyTransport HistoryBulkDiagramParameters

theorem decoded_independent_indicator_eq_one
    (K : ℕ) (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (a a' : State) (c c' : HistoryChoices sources seed V l)
    (outside : List ℕ)
    (hs : (decodeHistory sources seed V l a c).Supported V outside)
    (hs' : (decodeHistory sources seed V l a' c').Supported V outside)
    (ha : Template.Matches (Template.current seed l) a.small)
    (ha' : Template.Matches (Template.current seed l) a'.small)
    (hroot : ∀q∈a.small,sourceMass sources q≠0)
    (hroot' : ∀q∈a'.small,sourceMass sources q≠0)
    (hc : choicesMass sources seed V l c≠0)
    (hc' : choicesMass sources seed V l c'≠0)
    (hfreq : ∀j≤l,∀origin,(sources origin).AboveFrequency (V j))
    (hgp : a'.giantPlus=a.giantPlus) (hgm : a'.giantMinus=a.giantMinus)
    (hle : l≤K) :
    independentFrequencyResidueIndicator K (decodeHistory sources seed V l a c)
      (decodeHistory sources seed V l a' c') (a.giantPlus,a.giantMinus)=1 := by
  let H := decodeHistory sources seed V l a c
  let H' := decodeHistory sources seed V l a' c'
  let R := pairedFrequencyProduct H H'
  let : NeZero R := ⟨pairedFrequencyProduct_ne_zero hs hs'⟩
  have hu := decoded_frequencyUnits sources seed V outside l H H' hs hs' a c ha hroot hc hfreq
  have hu' := decoded_frequencyUnits sources seed V outside l H H' hs hs' a' c' ha' hroot' hc' hfreq
  have hl := decoded_largePrimes sources seed V l a c ha hroot hc hfreq
  have hl' := decoded_largePrimes sources seed V l a' c' ha' hroot' hc' hfreq
  have he := decoded_single_finite_of_supported K R sources seed V l a c outside hs ha hl hu
    (fun _ hv=>FrequencyPrecision.frequency_dvd_product (List.mem_append_left _ hv)) hle
  have he' := decoded_single_finite_of_supported K R sources seed V l a' c' outside hs' ha' hl' hu'
    (fun _ hv=>FrequencyPrecision.frequency_dvd_product (List.mem_append_right _ hv)) hle
  rw [hgp,hgm] at he'
  have hu0 : independentFiniteFrequencyUnits K H H' (a.giantPlus,a.giantMinus) := ⟨he.1,he'.1⟩
  have he0 : independentFiniteLeafAdmissible K H H' (a.giantPlus,a.giantMinus) := ⟨he.2,he'.2⟩
  change guardIndicator (independentFiniteFrequencyUnits K H H' (a.giantPlus,a.giantMinus) ∧
    independentFiniteLeafAdmissible K H H' (a.giantPlus,a.giantMinus))=1
  exact ite_eq_left ⟨hu0,he0⟩

theorem decoded_independent_reference_eq_one
    (K : ℕ) (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (a a' old old' : State)
    (c c' : HistoryChoices sources seed V l) (outside : List ℕ)
    (hs : (decodeHistory sources seed V l a c).Supported V outside)
    (hs' : (decodeHistory sources seed V l a' c').Supported V outside)
    (ha : Template.Matches (Template.current seed l) a.small)
    (ha' : Template.Matches (Template.current seed l) a'.small)
    (hroot : ∀q∈a.small,sourceMass sources q≠0)
    (hroot' : ∀q∈a'.small,sourceMass sources q≠0)
    (hc : choicesMass sources seed V l c≠0)
    (hc' : choicesMass sources seed V l c'≠0)
    (hfreq : ∀j≤l,∀origin,(sources origin).AboveFrequency (V j))
    (hgp : a'.giantPlus=a.giantPlus) (hgm : a'.giantMinus=a.giantMinus)
    (hf : a.frequency=old.frequency) (hf' : a'.frequency=old'.frequency)
    (hfixed : a.small.map eraseBulkValue=old.small.map eraseBulkValue)
    (hfixed' : a'.small.map eraseBulkValue=old'.small.map eraseBulkValue)
    (hle : l≤K) :
    independentReferenceIndicator K
      (decodeHistory sources seed V l old c) (decodeHistory sources seed V l old' c')
      (decodeHistory sources seed V l a c) (decodeHistory sources seed V l a' c')
      (a.giantPlus,a.giantMinus)=1 := by
  have ha0 := sameFrequencyData_decode sources seed V l a old c hf hfixed
  have hb0 := sameFrequencyData_decode sources seed V l a' old' c' hf' hfixed'
  have ht := independentIndicator_eq_reference_intCast ha0 hb0 K a.giantPlus a.giantMinus
  simp only [Int.cast_natCast] at ht
  rw [←ht]
  exact decoded_independent_indicator_eq_one K sources seed V l a a' c c' outside
    hs hs' ha ha' hroot hroot' hc hc' hfreq hgp hgm hle

end Ostmann.Arithmetic.HistoryBulkReferenceForwardR

end

end OAI
