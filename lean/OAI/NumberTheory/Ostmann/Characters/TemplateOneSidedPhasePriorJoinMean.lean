import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinData

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
attribute [local instance] Classical.propDecidable

theorem sourceRetainedPair_cmean_eq_oneSidedMean {k A : ℕ}
    (cfg : SourceConfiguration k) (m j : ℕ) (hj : j<k)
    (σ ρ : Equiv.Perm (CopiedConstituent (schedule k j) j (sourceWidth cfg m)))
    (χ : (q:ℕ)→MulChar (ZMod q) ℂ) (a : (q:ℕ)→ZMod q)
    (ζ : PrimeUnitData (schedule k j) (sourceWidth cfg m) A)
    (masks : SurvivingPrimeIndex k j (sourceWidth cfg m)→ℕ→ℂ)
    (p : SurvivingPrimeIndex k j (sourceWidth cfg m)→PrimeUpTo A)
    (L S : SurvivingPrimeIndex k j (sourceWidth cfg m)) (hLS : L≠S)
    (Elong Eshort : Finset (PrimeUpTo A))
    (hElong : 0<primeShellMass Elong) (hEshort : 0<primeShellMass Eshort)
    (hsep : ∀q∈Elong,∀r∈Eshort,q.val.Coprime r.val)
    (P : ℕ+) (s : ℤ) (t u : HistoryReconstruction.Tree j) (positive : Bool)
    (hforward : survivingDifferenceGraph k j hj (sourceWidth cfg m)
      (copiedSurvivingPermutation k j (sourceWidth cfg m) σ)
      (copiedSurvivingPermutation k j (sourceWidth cfg m) ρ) S L=if positive then 2 else -2)
    (hrev : survivingDifferenceGraph k j hj (sourceWidth cfg m)
      (copiedSurvivingPermutation k j (sourceWidth cfg m) σ)
      (copiedSurvivingPermutation k j (sourceWidth cfg m) ρ) L S=0)
    (F : PrimeUpTo A→PrimeUpTo A→ℂ) :
    (primeShellPrior Elong hElong).cmean (fun q=>(primeShellPrior Eshort hEshort).cmean
      (fun r=>sourceMaskedRetainedPairAt cfg m j hj σ ρ χ a ζ masks p L S q r P s t u * F q r)) =
      oneSidedMean (primeShellPrior Elong hElong).mass (sourceShortMass Eshort hEshort)
        (fun q=>sourceLongFactor cfg m j hj σ ρ χ ζ masks p L S P s t u q.val)
        (fun r:↥Eshort=>sourceShortFactor cfg m j hj σ ρ χ ζ masks p L S P s t u r.val.val)
        (fun q r=>exposedCharacter (sourceSliceCharacters cfg m j hj A χ S r.val.val) positive q.val * F q r.val) := by
  simp_rw [primeShellPrior_cmean_eq_subtype Eshort hEshort]
  unfold FinitePrior.cmean oneSidedMean
  apply Finset.sum_congr rfl
  intro q hqall
  by_cases hq : q∈Elong
  · simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hrall
    have he : sourceMaskedRetainedPairAt cfg m j hj σ ρ χ a ζ masks p L S q r.val P s t u =
        sourceLongFactor cfg m j hj σ ρ χ ζ masks p L S P s t u q.val *
        sourceShortFactor cfg m j hj σ ρ χ ζ masks p L S P s t u r.val.val *
        exposedCharacter (sourceSliceCharacters cfg m j hj A χ S r.val.val) positive q.val :=
      sourceMaskedRetainedPairAt_eq cfg m j hj σ ρ χ a ζ masks p L S hLS q r.val
        (hsep q hq r.val r.property) P s t u positive hforward hrev
    rw [he]
    unfold sourceShortMass
    ring
  · have hz : (primeShellPrior Elong hElong).mass q=0 := by
      simp only [primeShellPrior_mass,ite_eq_right hq,zero_div]
    simp only [hz,Complex.ofReal_zero,zero_mul]

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
