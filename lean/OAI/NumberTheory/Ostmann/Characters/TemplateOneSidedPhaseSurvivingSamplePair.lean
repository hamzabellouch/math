import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSurvivingSample

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template.OneSidedPhase
open Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
attribute [local instance] Classical.propDecidable

theorem source_unitRetainedPhase_pair {k Q : ℕ}
    (cfg : SourceConfiguration k) (m j : ℕ) (hj : j<k)
    (ζ : PrimeUnitData (schedule k j) (sourceWidth cfg m) Q)
    (χ : (q:ℕ)→MulChar (ZMod q) ℂ) (a : (q:ℕ)→ZMod q)
    (σ ρ : Equiv.Perm (CopiedConstituent (schedule k j) j (sourceWidth cfg m)))
    (h : CopiedConstituent (schedule k j) j (sourceWidth cfg m) → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j (sourceWidth cfg m) → PrimeUpTo Q)
    (hc : Pairwise (fun i z => (Sum.elim h y i).val.Coprime (Sum.elim h y z).val))
    (P : ℕ+) (s : ℤ) (t u : HistoryReconstruction.Tree j) :
    let χd := scheduledCharacterData k (sourceWidth cfg m) (sourceCharacterData cfg m (fun _=>χ)) j
    let ad := scheduledTranslationData k (sourceWidth cfg m) (sourceTranslationData cfg m (fun _=>a)) j
    letI : ∀i,Fact (Sum.elim h y i).val.Prime := fun i => ⟨primeUpTo_prime (Sum.elim h y i)⟩
    unitRetainedPhase k j hj (sourceWidth cfg m) ζ χd ad (fun i=>h (σ.symm i)) y P s t *
      conj (unitRetainedPhase k j hj (sourceWidth cfg m) ζ χd ad (fun i=>h (ρ.symm i)) y P s u) =
      survivingPhasePair k j hj (sourceWidth cfg m)
        (copiedSurvivingPermutation k j (sourceWidth cfg m) σ)
        (copiedSurvivingPermutation k j (sourceWidth cfg m) ρ)
        (fun i => (Sum.elim h y i).val)
        (finiteSurvivingCharacters k j hj (sourceWidth cfg m) χd)
        (finiteSurvivingTranslations k j hj (sourceWidth cfg m) ad)
        (finiteSurvivingUnits k j hj (sourceWidth cfg m) ζ) P s t u := by
  dsimp only
  rw [source_unitRetainedPhase_copied_permutation cfg m j hj ζ χ a σ h y hc P s t,
    source_unitRetainedPhase_copied_permutation cfg m j hj ζ χ a ρ h y hc P s u]
  rfl

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
