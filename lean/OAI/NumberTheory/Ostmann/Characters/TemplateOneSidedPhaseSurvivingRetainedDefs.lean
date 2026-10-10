import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSurvivingPrior
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSurvivingSamplePair

namespace OAI

open Erdos970

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Characters.Template.OneSidedPhase
open Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
attribute [local instance] Classical.propDecidable

def RetainedSquarePhase (k j : ℕ) (hj : j<k) (width : Role→ℕ) {Q : ℕ}
    (σ ρ : Equiv.Perm (CopiedConstituent (schedule k j) j width))
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (ζ : PrimeUnitData (schedule k j) width Q)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (P : ℕ+) (s : ℤ) (t u : HistoryReconstruction.Tree j)
    (L S : SurvivingPrimeIndex k j width) : Prop :=
  let p := fun i=>(Sum.elim h y i).val
  let χr := finiteSurvivingCharacters k j hj width χ
  let ζr := finiteSurvivingUnits k j hj width ζ
  let σr := copiedSurvivingPermutation k j width σ
  let ρr := copiedSurvivingPermutation k j width ρ
  let D := survivingDifferenceGraph k j hj width σr ρr
  let ν := pairedSurvivingUnary k j hj width χr ζr σr ρr P s t u
  ∃positive : Bool,
    unitRetainedPhase k j hj width ζ χ a (fun i=>h (σ.symm i)) y P s t *
      conj (unitRetainedPhase k j hj width ζ χ a (fun i=>h (ρ.symm i)) y P s u) =
      indexedLongUnary D p χr ν L S (p L) * indexedShortUnary D p χr ν L S (p S) *
        exposedCharacter (χr S (p S)) positive (p L) ∧
    ‖indexedLongUnary D p χr ν L S (p L)‖≤1 ∧
    ‖indexedShortUnary D p χr ν L S (p S)‖≤1 ∧
    exposedCharacter (χr S (p S)) positive≠1

theorem source_retainedSquarePhase_iff {k Q : ℕ}
    (cfg : SourceConfiguration k) (m j : ℕ) (hj : j<k)
    (ζ : PrimeUnitData (schedule k j) (sourceWidth cfg m) Q)
    (χ : (q:ℕ)→MulChar (ZMod q) ℂ) (a : (q:ℕ)→ZMod q)
    (σ ρ : Equiv.Perm (CopiedConstituent (schedule k j) j (sourceWidth cfg m)))
    (h : CopiedConstituent (schedule k j) j (sourceWidth cfg m) → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j (sourceWidth cfg m) → PrimeUpTo Q)
    (hc : Pairwise (fun i z=>(Sum.elim h y i).val.Coprime (Sum.elim h y z).val))
    (P : ℕ+) (s : ℤ) (t u : HistoryReconstruction.Tree j)
    (L S : SurvivingPrimeIndex k j (sourceWidth cfg m)) :
    let χd := scheduledCharacterData k (sourceWidth cfg m) (sourceCharacterData cfg m (fun _=>χ)) j
    let ad := scheduledTranslationData k (sourceWidth cfg m) (sourceTranslationData cfg m (fun _=>a)) j
    letI : ∀i : SurvivingPrimeIndex k j (sourceWidth cfg m),Fact (Sum.elim h y i).val.Prime :=
      fun i=>⟨primeUpTo_prime (Sum.elim h y i)⟩
    RetainedSquarePhase k j hj (sourceWidth cfg m) σ ρ χd ad ζ h y P s t u L S ↔
      SurvivingSquarePhase k j hj (sourceWidth cfg m)
        (copiedSurvivingPermutation k j (sourceWidth cfg m) σ)
        (copiedSurvivingPermutation k j (sourceWidth cfg m) ρ) (fun i=>(Sum.elim h y i).val)
        (finiteSurvivingCharacters k j hj (sourceWidth cfg m) χd)
        (finiteSurvivingTranslations k j hj (sourceWidth cfg m) ad)
        (finiteSurvivingUnits k j hj (sourceWidth cfg m) ζ) P s t u L S := by
  dsimp only
  unfold RetainedSquarePhase SurvivingSquarePhase
  dsimp only
  rw [source_unitRetainedPhase_pair cfg m j hj ζ χ a σ ρ h y hc P s t u]

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
