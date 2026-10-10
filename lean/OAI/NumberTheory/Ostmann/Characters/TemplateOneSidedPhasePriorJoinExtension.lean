import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinRowsExtension
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinSourceRows

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
open TemplateOneSidedPrior PrimeDyadicCover
attribute [local instance] Classical.propDecidable

theorem sourceRetainedPair_cmean_eq_rows_extension {k A : ℕ}
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
    (hmax : ∀q∈Elong,Real.log q.val≤Real.exp (β*ℓ))
    (W : Fin Q→ℕ→↥Eshort→ℂ)
    (hW : ∀q∈Elong,∀r:Fin Q,∀n:ℕ,Q*n+r.val=q.val→∀v:↥Eshort,W r n v=F q v.val) :
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
            W) := by
  rw [sourceRetainedPair_cmean_eq_rows_of_log cfg m j hj σ ρ χ a ζ masks p L S hLS
    Elong Eshort hElong hEshort hsep P s t u positive hforward hrev F Q hQ hmin hmax]
  apply Finset.sum_congr rfl
  intro i hi
  exact source_oneSidedMean_eq_extension_on_source Q (sourceUpper β ℓ) Elong i
    (fun r:↥Eshort=>r.val.val)
    (fun r=>exposedCharacter (sourceSliceCharacters cfg m j hj A χ S r.val.val) positive)
    (sourceShortMass Eshort hEshort) _ _ (fun q (r:↥Eshort)=>F q r.val) W hW

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
