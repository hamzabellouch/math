import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseCanonical
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseOutside
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConversePlanPositiveCanonical
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseSkeletonDecode
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSupportReductionResidue

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConverse
open Construction Construction.CanonicalOccurrenceTransport
open HistorySignedDecode HistorySignedNumerators HistoryOccurrenceVariables
open HistorySignedSupportReduction HistorySignedResidueFactorization
open HistorySymbolicEncoding HistoryBulkSupportConversePlan HistorySupportReduction

theorem supported_decode_of_reconstructed_guards
    (bSize s : ℕ) (X tb td G : ℝ)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (outside : List ℕ)
    (l : ℕ) (a b : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hab : a.frequency=b.frequency)
    (hs : (decodeHistory sources seed V l a c).Supported V outside)
    (hbprime : b.PrimeSmall) (hp : 0<b.giantPlus) (hm : 0<b.giantMinus)
    (hroot : b.Coprime outside)
    (hlarge : LargePrimes V (decodeHistory sources seed V l b c))
    (hi : (rebuild (decodeHistory sources seed V l b c) b.giantPlus b.giantMinus).IntegralGuard)
    (hf : FrequencyGiantCoprime
      (rebuild (decodeHistory sources seed V l b c) b.giantPlus b.giantMinus))
    (hsq : ∀i : InternalKey (decodeHistory sources seed V l b c),
      ¬((internalSlot _ i).value:ℤ)^2 ∣ actual _ b.giantPlus b.giantMinus i)
    (ho : PivotOutsideCoprime outside
      (rebuild (decodeHistory sources seed V l b c) b.giantPlus b.giantMinus))
    (hz : actualRealHistoryScalar bSize s X tb td G outside
      (decodeHistory sources seed V l a c) hs
      (fun q => (newSourceSample sources seed V l b c hb b.giantPlus b.giantMinus
        ((decodedCoordinateEquiv sources seed V l a c ha).symm q):ℝ))≠0) :
    (decodeHistory sources seed V l b c).Supported V outside := by
  let z : SignedState := ⟨b.frequency,b.giantPlus,b.giantMinus,b.small⟩
  have hzstate : z.toState=b := by cases b; rfl
  have hpi := referenceScalar_ne_zero_new_positiveIntegral bSize s X tb td G
    sources seed V outside l a b c ha hb hab hs _ _
    (by exact_mod_cast hp) (by exact_mod_cast hm) hi hz
  have hstatic := staticSkeleton_decode_redraw sources seed V l a b c ha hb hs hab hbprime
  have har := (arithmeticGuards_rebuild_iff_static _ hstatic
    (internal_outside_coprime_decode_redraw sources seed V l a b c hs)
    b.giantPlus b.giantMinus).mpr ⟨hf,hsq,ho⟩
  have hrc : RootCoprime outside z := by
    simpa only [RootCoprime,State.Coprime,State.values,z,Int.natAbs_natCast] using hroot
  have he := supported_iff_positiveIntegral_arithmetic sources seed V l z c outside hb
    (by simpa only [hzstate] using hlarge)
  rw [hzstate] at he
  apply he.mpr
  rw [rebuild_decodeHistory] at hpi hi har
  exact ⟨hpi,by simpa only [signedDecode_root] using hrc,hi,har⟩

end Ostmann.Arithmetic.HistoryBulkSupportConverse

end

end OAI
