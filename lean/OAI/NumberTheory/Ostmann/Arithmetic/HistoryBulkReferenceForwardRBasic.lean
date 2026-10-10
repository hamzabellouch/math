import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceTestsFrequencySource
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSupportReductionResidue
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySupportReductionSources

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceForwardR
open Construction HistorySignedDecode HistorySignedSupportReduction
open HistorySignedResidueFactorization HistoryFrequencyResidues HistorySupportReduction

theorem frequencyGiantCoprime_of_arithmeticGuards
    {V : ℕ → ℕ} {outside : List ℕ} {l : ℕ} {h : SignedHistory l}
    (ha : ArithmeticGuards V outside h) : FrequencyGiantCoprime h := by
  induction h with
  | leaf a =>
    rw [ArithmeticGuards] at ha
    exact ha.1.2.2.2.2
  | node a p u hp hm left right ihl ihr =>
    rw [ArithmeticGuards] at ha
    exact ⟨ha.1.2.2.2.2,ihl ha.2.2.1,ihr ha.2.2.2⟩

theorem decoded_single_finite_of_supported
    (K R : ℕ) [NeZero R] (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (a : State) (c : HistoryChoices sources seed V l)
    (outside : List ℕ)
    (hs : (decodeHistory sources seed V l a c).Supported V outside)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hlarge : LargePrimes V (decodeHistory sources seed V l a c))
    (hu : FrequencyUnits R (decodeHistory sources seed V l a c))
    (hF : ∀v∈(decodeHistory sources seed V l a c).frequencies,v.natAbs∣R)
    (hle : l≤K) :
    singleFiniteFrequencyUnits K R (decodeHistory sources seed V l a c) hF
      (a.giantPlus,a.giantMinus) ∧
    singleFiniteLeafAdmissible K R (decodeHistory sources seed V l a c) hF
      (a.giantPlus,a.giantMinus) := by
  have hh := (supported_iff_positiveIntegral_arithmetic sources seed V l
    (SignedState.ofState a) c outside ha (by simpa only [SignedState.toState_ofState] using hlarge)).mp
    (by simpa only [SignedState.toState_ofState] using hs)
  have hi : (rebuild (decodeHistory sources seed V l a c) a.giantPlus a.giantMinus).IntegralGuard := by
    rw [rebuild_decodeHistory]
    exact hh.1.integralGuard
  have hf : FrequencyGiantCoprime
      (rebuild (decodeHistory sources seed V l a c) a.giantPlus a.giantMinus) := by
    rw [rebuild_decodeHistory]
    exact frequencyGiantCoprime_of_arithmeticGuards hh.2.2.2
  have he := (single_integral_frequency_iff_finite K R _ hs hlarge hu hF hle
    a.giantPlus a.giantMinus).mp ⟨hi,hf⟩
  simpa only [Int.cast_natCast] using And.intro he.1 he.2.1

end Ostmann.Arithmetic.HistoryBulkReferenceForwardR

end

end OAI
