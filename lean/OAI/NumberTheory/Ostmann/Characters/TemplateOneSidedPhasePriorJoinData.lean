import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinActual
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinRows

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
attribute [local instance] Classical.propDecidable

def sourceSliceCharacters {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) (hj : j<k)
    (A : ℕ) (χ : (q:ℕ)→MulChar (ZMod q) ℂ) :=
  finiteSurvivingCharacters k j hj (sourceWidth cfg m)
    (scheduledCharacterData k (sourceWidth cfg m) (sourceCharacterData (Q:=A) cfg m (fun _=>χ)) j)

def sourceLongFactor {k A : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) (hj : j<k)
    (σ ρ : Equiv.Perm (CopiedConstituent (schedule k j) j (sourceWidth cfg m)))
    (χ : (q:ℕ)→MulChar (ZMod q) ℂ)
    (ζ : PrimeUnitData (schedule k j) (sourceWidth cfg m) A)
    (masks : SurvivingPrimeIndex k j (sourceWidth cfg m)→ℕ→ℂ)
    (p : SurvivingPrimeIndex k j (sourceWidth cfg m)→PrimeUpTo A)
    (L S : SurvivingPrimeIndex k j (sourceWidth cfg m))
    (P : ℕ+) (s : ℤ) (t u : HistoryReconstruction.Tree j) (q : ℕ) : ℂ :=
  let χr := sourceSliceCharacters cfg m j hj A χ
  let ζr := finiteSurvivingUnits k j hj (sourceWidth cfg m) ζ
  let σr := copiedSurvivingPermutation k j (sourceWidth cfg m) σ
  let ρr := copiedSurvivingPermutation k j (sourceWidth cfg m) ρ
  priorJoinLongUnary (survivingDifferenceGraph k j hj (sourceWidth cfg m) σr ρr)
    (fun i=>(p i).val) χr (pairedSurvivingUnary k j hj (sourceWidth cfg m) χr ζr σr ρr P s t u)
    masks L S q

def sourceShortFactor {k A : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) (hj : j<k)
    (σ ρ : Equiv.Perm (CopiedConstituent (schedule k j) j (sourceWidth cfg m)))
    (χ : (q:ℕ)→MulChar (ZMod q) ℂ)
    (ζ : PrimeUnitData (schedule k j) (sourceWidth cfg m) A)
    (masks : SurvivingPrimeIndex k j (sourceWidth cfg m)→ℕ→ℂ)
    (p : SurvivingPrimeIndex k j (sourceWidth cfg m)→PrimeUpTo A)
    (L S : SurvivingPrimeIndex k j (sourceWidth cfg m))
    (P : ℕ+) (s : ℤ) (t u : HistoryReconstruction.Tree j) (r : ℕ) : ℂ :=
  let χr := sourceSliceCharacters cfg m j hj A χ
  let ζr := finiteSurvivingUnits k j hj (sourceWidth cfg m) ζ
  let σr := copiedSurvivingPermutation k j (sourceWidth cfg m) σ
  let ρr := copiedSurvivingPermutation k j (sourceWidth cfg m) ρ
  priorJoinShortUnary (survivingDifferenceGraph k j hj (sourceWidth cfg m) σr ρr)
    (fun i=>(p i).val) χr (pairedSurvivingUnary k j hj (sourceWidth cfg m) χr ζr σr ρr P s t u)
    masks L S r

theorem sourceSlice_exposedCharacter_ne_one {k A : ℕ} (cfg : SourceConfiguration k)
    (m j : ℕ) (hj : j<k) (χ : (q:ℕ)→MulChar (ZMod q) ℂ)
    (S : SurvivingPrimeIndex k j (sourceWidth cfg m)) (r : PrimeUpTo A)
    (hχ : 2<orderOf (χ r.val)) (positive : Bool) :
    exposedCharacter (sourceSliceCharacters cfg m j hj A χ S r.val) positive≠1 := by
  apply exposedCharacter_ne_one _ _ positive
  rw [sourceSliceCharacters,finiteSurvivingCharacters,extendCharacterData_prime,
    scheduled_sourceCharacterData_order]
  exact hχ

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
