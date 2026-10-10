import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinMean
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinRowsExtension

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
open TemplateOneSidedPrior PrimeDyadicCover
attribute [local instance] Classical.propDecidable

theorem sourceRetainedPair_cmean_eq_rows {k A : ℕ}
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
    (F : PrimeUpTo A→PrimeUpTo A→ℂ)
    (Q : ℕ) (hQ : 0<Q)
    (H : ℕ) (hmin : ∀q∈Elong,Q≤q.val) (hmax : ∀q∈Elong,q.val≤H) :
    (primeShellPrior Elong hElong).cmean (fun q=>(primeShellPrior Eshort hEshort).cmean
      (fun r=>sourceMaskedRetainedPairAt cfg m j hj σ ρ χ a ζ masks p L S q r P s t u * F q r)) =
      ∑i:Index H,
        oneSidedMean (sourceRowMass Q H Elong i) (sourceShortMass Eshort hEshort)
          (fun x=>sourceTest
            (fun q:PrimeUpTo A=>sourceLongFactor cfg m j hj σ ρ χ ζ masks p L S P s t u q.val)
            (rowValue Q (2*lower Q H i+1) x))
          (fun r:↥Eshort=>sourceShortFactor cfg m j hj σ ρ χ ζ masks p L S P s t u r.val.val)
          (rowCharacterKernel (fun r:↥Eshort=>r.val.val)
            (fun r=>exposedCharacter (sourceSliceCharacters cfg m j hj A χ S r.val.val) positive)
            Q (2*lower Q H i+1) (fun r:Fin Q=>r.val)
            (sourceRowAmplitude Q (fun q (r:↥Eshort)=>F q r.val))) := by
  rw [sourceRetainedPair_cmean_eq_oneSidedMean cfg m j hj σ ρ χ a ζ masks p L S hLS
    Elong Eshort hElong hEshort hsep P s t u positive hforward hrev F]
  simpa only [oneSidedMean,FinitePrior.cmean,sourceShortMass,mul_assoc] using
    source_prime_bilinear_cmean_eq_rows Q H hQ Elong Eshort hElong hEshort hmin hmax
      (fun r=>exposedCharacter (sourceSliceCharacters cfg m j hj A χ S r.val.val) positive)
      (fun q:PrimeUpTo A=>sourceLongFactor cfg m j hj σ ρ χ ζ masks p L S P s t u q.val)
      (fun r:↥Eshort=>sourceShortFactor cfg m j hj σ ρ χ ζ masks p L S P s t u r.val.val)
      (fun q (r:↥Eshort)=>F q r.val)

theorem sourceRetainedPair_cmean_eq_rows_of_log {k A : ℕ}
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
    (F : PrimeUpTo A→PrimeUpTo A→ℂ)
    (Q : ℕ) (hQ : 0<Q)
    {β ℓ : ℝ} (hmin : ∀q∈Elong,Q≤q.val)
    (hmax : ∀q∈Elong,Real.log q.val≤Real.exp (β*ℓ)) :
    (primeShellPrior Elong hElong).cmean (fun q=>(primeShellPrior Eshort hEshort).cmean
      (fun r=>sourceMaskedRetainedPairAt cfg m j hj σ ρ χ a ζ masks p L S q r P s t u * F q r)) =
      ∑i:Index (sourceUpper β ℓ),
        oneSidedMean (sourceRowMass Q (sourceUpper β ℓ) Elong i) (sourceShortMass Eshort hEshort)
          (fun x=>sourceTest
            (fun q:PrimeUpTo A=>sourceLongFactor cfg m j hj σ ρ χ ζ masks p L S P s t u q.val)
            (rowValue Q (2*lower Q (sourceUpper β ℓ) i+1) x))
          (fun r:↥Eshort=>sourceShortFactor cfg m j hj σ ρ χ ζ masks p L S P s t u r.val.val)
          (rowCharacterKernel (fun r:↥Eshort=>r.val.val)
            (fun r=>exposedCharacter (sourceSliceCharacters cfg m j hj A χ S r.val.val) positive)
            Q (2*lower Q (sourceUpper β ℓ) i+1) (fun r:Fin Q=>r.val)
            (sourceRowAmplitude Q (fun q (r:↥Eshort)=>F q r.val))) := by
  rw [sourceRetainedPair_cmean_eq_oneSidedMean cfg m j hj σ ρ χ a ζ masks p L S hLS
    Elong Eshort hElong hEshort hsep P s t u positive hforward hrev F]
  simpa only [oneSidedMean,FinitePrior.cmean,sourceShortMass,mul_assoc] using
    source_prime_bilinear_cmean_eq_rows_of_log Q hQ Elong Eshort hElong hEshort hmin hmax
      (fun r=>exposedCharacter (sourceSliceCharacters cfg m j hj A χ S r.val.val) positive)
      (fun q:PrimeUpTo A=>sourceLongFactor cfg m j hj σ ρ χ ζ masks p L S P s t u q.val)
      (fun r:↥Eshort=>sourceShortFactor cfg m j hj σ ρ χ ζ masks p L S P s t u r.val.val)
      (fun q (r:↥Eshort)=>F q r.val)

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
