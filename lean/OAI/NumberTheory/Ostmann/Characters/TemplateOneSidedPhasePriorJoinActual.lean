import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinSample

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.OneSidedPhase
open Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
attribute [local instance] Classical.propDecidable

def sourceMaskedRetainedPairAt {k A : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) (hj : j<k)
    (σ ρ : Equiv.Perm (CopiedConstituent (schedule k j) j (sourceWidth cfg m)))
    (χ : (q:ℕ)→MulChar (ZMod q) ℂ) (a : (q:ℕ)→ZMod q)
    (ζ : PrimeUnitData (schedule k j) (sourceWidth cfg m) A)
    (masks : SurvivingPrimeIndex k j (sourceWidth cfg m)→ℕ→ℂ)
    (p : SurvivingPrimeIndex k j (sourceWidth cfg m)→PrimeUpTo A)
    (L S : SurvivingPrimeIndex k j (sourceWidth cfg m)) (q r : PrimeUpTo A)
    (P : ℕ+) (s : ℤ) (t u : HistoryReconstruction.Tree j) : ℂ :=
  if Pairwise (fun i v=>(twoPrimeSample p L S q r i).val.Coprime (twoPrimeSample p L S q r v).val) then
    (∏i,masks i (twoPrimeSample p L S q r i).val)*sourceRetainedPairAt cfg m j hj σ ρ χ a ζ p L S q r P s t u
  else 0

theorem sourceMaskedRetainedPairAt_eq {k A : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) (hj : j<k)
    (σ ρ : Equiv.Perm (CopiedConstituent (schedule k j) j (sourceWidth cfg m)))
    (χ : (q:ℕ)→MulChar (ZMod q) ℂ) (a : (q:ℕ)→ZMod q)
    (ζ : PrimeUnitData (schedule k j) (sourceWidth cfg m) A)
    (masks : SurvivingPrimeIndex k j (sourceWidth cfg m)→ℕ→ℂ)
    (p : SurvivingPrimeIndex k j (sourceWidth cfg m)→PrimeUpTo A)
    (L S : SurvivingPrimeIndex k j (sourceWidth cfg m)) (hLS : L≠S) (q r : PrimeUpTo A)
    (hqr : q.val.Coprime r.val) (P : ℕ+) (s : ℤ) (t u : HistoryReconstruction.Tree j)
    (positive : Bool)
    (hforward : survivingDifferenceGraph k j hj (sourceWidth cfg m)
      (copiedSurvivingPermutation k j (sourceWidth cfg m) σ)
      (copiedSurvivingPermutation k j (sourceWidth cfg m) ρ) S L=if positive then 2 else -2)
    (hrev : survivingDifferenceGraph k j hj (sourceWidth cfg m)
      (copiedSurvivingPermutation k j (sourceWidth cfg m) σ)
      (copiedSurvivingPermutation k j (sourceWidth cfg m) ρ) L S=0) :
    let χd := scheduledCharacterData k (sourceWidth cfg m) (sourceCharacterData (Q:=A) cfg m (fun _=>χ)) j
    let χr := finiteSurvivingCharacters k j hj (sourceWidth cfg m) χd
    let ζr := finiteSurvivingUnits k j hj (sourceWidth cfg m) ζ
    let σr := copiedSurvivingPermutation k j (sourceWidth cfg m) σ
    let ρr := copiedSurvivingPermutation k j (sourceWidth cfg m) ρ
    let D := survivingDifferenceGraph k j hj (sourceWidth cfg m) σr ρr
    let ν := pairedSurvivingUnary k j hj (sourceWidth cfg m) χr ζr σr ρr P s t u
    sourceMaskedRetainedPairAt cfg m j hj σ ρ χ a ζ masks p L S q r P s t u =
      priorJoinLongUnary D (fun i=>(p i).val) χr ν masks L S q.val *
      priorJoinShortUnary D (fun i=>(p i).val) χr ν masks L S r.val *
      exposedCharacter (χr S r.val) positive q.val := by
  let : ∀i,Fact (twoPrimeAssignment (fun i=>(p i).val) L S q.val r.val i).Prime :=
    fun i=>⟨twoPrimeSample_prime p L S q r i⟩
  dsimp only
  have hh := masked_survivingPhasePair_twoPrimeAssignment k j hj (sourceWidth cfg m)
    (copiedSurvivingPermutation k j (sourceWidth cfg m) σ)
    (copiedSurvivingPermutation k j (sourceWidth cfg m) ρ)
    (fun i=>(p i).val) L S hLS q.val r.val hqr
    (finiteSurvivingCharacters k j hj (sourceWidth cfg m)
      (scheduledCharacterData k (sourceWidth cfg m) (sourceCharacterData (Q:=A) cfg m (fun _=>χ)) j))
    (finiteSurvivingTranslations k j hj (sourceWidth cfg m)
      (scheduledTranslationData k (sourceWidth cfg m) (sourceTranslationData (Q:=A) cfg m (fun _=>a)) j))
    (finiteSurvivingUnits k j hj (sourceWidth cfg m) ζ) masks P s t u positive hforward hrev
  rw [←hh]
  unfold sourceMaskedRetainedPairAt
  simp only [twoPrimeSample_val]
  split_ifs with hc
  · rw [sourceRetainedPairAt_eq cfg m j hj σ ρ χ a ζ p L S q r hc P s t u]
  · rfl

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
