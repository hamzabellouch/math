import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseReferenceEvent
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseSpectatorDecoded
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyRealizationLeaves
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightSourceXi

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConverse
open Construction Construction.CanonicalOccurrenceTransport
open HistorySignedDecode HistorySignedNumerators HistoryOccurrenceVariables
open HistorySignedSupportReduction HistorySignedResidueFactorization
open HistorySymbolicEncoding HistoryBulkSupportConversePlan HistorySupportReduction
open HistoryBulkFrequencyTransport HistoryBulkDiagramParameters HistoryFrequencyResidues
open HistoryPairedFrequencyAverage HistorySignedSpectatorCRT

theorem pair_supported_of_reference_and_raw_tests
    (bSize s : ℕ) (X tb td G : ℝ) (sources : SourceFamily) (m k : ℕ)
    (V : ℕ→ℕ) (outside : List ℕ) (l K : ℕ) (hle : l≤K)
    (a a' b b' : State)
    (c e : HistoryChoices sources (Template.initial m k) V l)
    (ha : Template.Matches (Template.current (Template.initial m k) l) a.small)
    (ha' : Template.Matches (Template.current (Template.initial m k) l) a'.small)
    (hb : Template.Matches (Template.current (Template.initial m k) l) b.small)
    (hb' : Template.Matches (Template.current (Template.initial m k) l) b'.small)
    (hf : a.frequency=b.frequency) (hf' : a'.frequency=b'.frequency)
    (hs : (decodeHistory sources (Template.initial m k) V l a c).Supported V outside)
    (hs' : (decodeHistory sources (Template.initial m k) V l a' e).Supported V outside)
    (hsmall : b.small=b'.small) (hGp : b.giantPlus=b'.giantPlus) (hGm : b.giantMinus=b'.giantMinus)
    (herase : b.small.map eraseBulkValue=a.small.map eraseBulkValue)
    (herase' : b'.small.map eraseBulkValue=a'.small.map eraseBulkValue)
    (hrootmass : ∀q∈b.small,sourceMass sources q≠0)
    (hc : choicesMass sources (Template.initial m k) V l c≠0)
    (he : choicesMass sources (Template.initial m k) V l e≠0)
    (hfreq : ∀j≤l,∀origin,(sources origin).AboveFrequency (V j))
    (hp : 0<b.giantPlus) (hm : 0<b.giantMinus) (hroot : b.Coprime outside)
    (hx : ReferenceAncestorUnits sources (Template.initial m k) V l b c hb b.giantPlus b.giantMinus)
    (hx' : ReferenceAncestorUnits sources (Template.initial m k) V l b' e hb' b.giantPlus b.giantMinus)
    (hlines : ∀i,((historyDraws sources (Template.initial m k) V l c i).val:ℤ) ∣
      referenceLine sources (Template.initial m k) V outside l a b c ha hb hs b.giantPlus b.giantMinus i)
    (hlines' : ∀i,((historyDraws sources (Template.initial m k) V l e i).val:ℤ) ∣
      referenceLine sources (Template.initial m k) V outside l a' b' e ha' hb' hs' b.giantPlus b.giantMinus i)
    (hsquares : ∀i,¬((historyDraws sources (Template.initial m k) V l c i).val:ℤ)^2 ∣
      referenceLine sources (Template.initial m k) V outside l a b c ha hb hs b.giantPlus b.giantMinus i)
    (hsquares' : ∀i,¬((historyDraws sources (Template.initial m k) V l e i).val:ℤ)^2 ∣
      referenceLine sources (Template.initial m k) V outside l a' b' e ha' hb' hs' b.giantPlus b.giantMinus i)
    (hR : let g := decodeHistory sources (Template.initial m k) V l a c
          let g' := decodeHistory sources (Template.initial m k) V l a' e
          let h := decodeHistory sources (Template.initial m k) V l b c
          leafIndicator K (pairedFrequencyProduct g g') (frequencySchedule g g')
            (fixedFactorSchedule g g') g g' []
            (l,initialResidueGiants K (pairedFrequencyProduct g g') (b.giantPlus,b.giantMinus),
              initialResidueGiants K (pairedFrequencyProduct g g') (b.giantPlus,b.giantMinus))
            (frequencyLeaves ((pairedFrequencyProduct g g')^(K+2)) h)≠0)
    (g : (q:ℕ)→ZMod q→ℂ) (hprime : ∀q∈outside,q.Prime)
    (hg : ∀q∈outside,g q 0=0) (houtfreq : ∀q∈outside,∀j≤l,V j<q)
    (hD : residuePairSpectator g outside outside.prod
      (decodeHistory sources (Template.initial m k) V l b c)
      (decodeHistory sources (Template.initial m k) V l b' e) (b.giantPlus,b.giantMinus)≠0)
    (hz : actualRealHistoryScalar bSize s X tb td G outside
      (decodeHistory sources (Template.initial m k) V l a c) hs
      (fun q => (newSourceSample sources (Template.initial m k) V l b c hb b.giantPlus b.giantMinus
        ((decodedCoordinateEquiv sources (Template.initial m k) V l a c ha).symm q):ℝ))≠0)
    (hz' : actualRealHistoryScalar bSize s X tb td G outside
      (decodeHistory sources (Template.initial m k) V l a' e) hs'
      (fun q => (newSourceSample sources (Template.initial m k) V l b' e hb' b.giantPlus b.giantMinus
        ((decodedCoordinateEquiv sources (Template.initial m k) V l a' e ha').symm q):ℝ))≠0) :
    (decodeHistory sources (Template.initial m k) V l b c).Supported V outside ∧
      (decodeHistory sources (Template.initial m k) V l b' e).Supported V outside := by
  have hrootmass' : ∀q∈b'.small,sourceMass sources q≠0 := by simpa only [←hsmall] using hrootmass
  have hbprime : b.PrimeSmall := fun q hq => sourceMass_value_prime (hrootmass q hq)
  have hbprime' : b'.PrimeSmall := fun q hq => sourceMass_value_prime (hrootmass' q hq)
  have hst := staticSkeleton_decode_redraw sources _ V l a b c ha hb hs hf hbprime
  have hst' := staticSkeleton_decode_redraw sources _ V l a' b' e ha' hb' hs' hf' hbprime'
  have hlarge := decoded_largePrimes sources _ V l b c hb hrootmass hc hfreq
  have hlarge' := decoded_largePrimes sources _ V l b' e hb' hrootmass' he hfreq
  have hu := decoded_frequencyUnits_static sources _ V l _ _ hst hst' b c hb hrootmass hc hfreq
  have hu' := decoded_frequencyUnits_static sources _ V l _ _ hst hst' b' e hb' hrootmass' he hfreq
  have hown := guardedOwn_of_referenceLines sources _ V outside l a b c ha hb hf hs _ _ hc hfreq hx hlines
  have hown' := guardedOwn_of_referenceLines sources _ V outside l a' b' e ha' hb' hf' hs' _ _ he hfreq hx' hlines'
  have hfd := sameFrequencyData_decode sources _ V l b a c hf.symm herase
  have hfd' := sameFrequencyData_decode sources _ V l b' a' e hf'.symm herase'
  have hind := pairedIndicator_eq_reference_intCast hfd hfd' K b.giantPlus b.giantMinus
  simp only [Int.cast_natCast] at hind
  have hine : pairedFrequencyResidueIndicator K
      (decodeHistory sources (Template.initial m k) V l b c)
      (decodeHistory sources (Template.initial m k) V l b' e) (b.giantPlus,b.giantMinus)≠0 := by
    rw [hind]
    exact hR
  have hleaves := decodeHistory_frequencyLeaves_eq_of_small_eq
    (Q := (pairedFrequencyProduct (decodeHistory sources (Template.initial m k) V l b c)
      (decodeHistory sources (Template.initial m k) V l b' e))^(K+2)) sources m k V l b b' c e hb hsmall
  obtain ⟨hi,hfg,hfg'⟩ := pair_integral_and_frequency_of_indicator K _ _ hst hst'
    hlarge hlarge' hu hu' hle b.giantPlus b.giantMinus hown hown' hleaves (by simpa only [Int.cast_natCast] using hine)
  obtain ⟨ho,ho'⟩ := residuePairSpectator_nonzero_pivotOutsideCoprime_decode_redraw
    sources _ V outside l a a' b b' c e ha ha' hb hb' hs hs' hf hf' hbprime hbprime'
    g hprime hg houtfreq b.giantPlus b.giantMinus hi.1 hi.2
    (by simpa only [Int.cast_natCast] using hD)
  have hsq := squareExclusions_of_referenceLines sources _ V outside l a b c ha hb hf hs _ _
    hc hfreq hx hi.1 hsquares
  have hsq' := squareExclusions_of_referenceLines sources _ V outside l a' b' e ha' hb' hf' hs' _ _
    he hfreq hx' hi.2 hsquares'
  constructor
  · exact supported_decode_of_reconstructed_guards bSize s X tb td G sources _ V outside l a b c
      ha hb hf hs hbprime hp hm hroot hlarge hi.1 hfg hsq ho hz
  · apply supported_decode_of_reconstructed_guards bSize s X tb td G sources _ V outside l a' b' e
      ha' hb' hf' hs' hbprime'
    · simpa only [←hGp] using hp
    · simpa only [←hGm] using hm
    · simpa only [State.Coprime,State.values,←hGp,←hGm,←hsmall] using hroot
    · exact hlarge'
    · simpa only [←hGp,←hGm] using hi.2
    · simpa only [←hGp,←hGm] using hfg'
    · simpa only [←hGp,←hGm] using hsq'
    · simpa only [←hGp,←hGm] using ho'
    · simpa only [←hGp,←hGm] using hz'

end Ostmann.Arithmetic.HistoryBulkSupportConverse

end

end OAI
