import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSourceNormalizedData
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSourcePairActual
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSurvivingExpressionsSource
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTelescopingPairWeight

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateSupportRemoval TemplateOneSidedBudget
open HistoryFrequencyLabels HistoryFrequencyBudget HigherBiasSource.SourceTemplate
open TemplateOneSidedSupportTelescoping
attribute [local instance] Classical.propDecidable

def survivingIntegerState (k j : ℕ) (width : Role → ℕ) (P : ℤ)
    (σ : Equiv.Perm (CopiedConstituent (schedule k j) j width))
    (x : SurvivingPrimeIndex k j width → ℤ) : State k j :=
  sourceState k j P
    (fun i=>∏a : Fin (width ((schedule k j).role i.val)),x (.inl (σ ⟨i,a⟩)))
    (fun i=>∏a : Fin (width ((schedule k j).role i.val)),x (.inr ⟨i,a⟩))

def survivingCorePairAmplitude (k j : ℕ) (width : Role → ℕ)
    (B V : ℕ → ℤ) (T : ℕ → ℝ) (J : ℤ) (P s v : ℤ)
    (σ ρ : Equiv.Perm (CopiedConstituent (schedule k j) j width))
    (t u : HistoryReconstruction.Tree j) (gate : Bool) (X Δ Wp Wl Tc Wc : ℝ)
    (x : SurvivingPrimeIndex k j width → ℤ) : ℂ :=
  copiedWindowRatio Tc Wc (∏i,x (.inl i)) *
    (if gate then
      coreHistoryWeight k (fun l _=>B l) (fun l _=>V l)
        (canonicalHistoryExtra k (fun l=>pivotWindow (T l) Wp))
        (canonicalHistoryMask k (sourceRangeLeafMask k J X Δ Wl))
        X Δ Wl j s (survivingIntegerState k j width P σ x) t *
      conj (coreHistoryWeight k (fun l _=>B l) (fun l _=>V l)
        (canonicalHistoryExtra k (fun l=>pivotWindow (T l) Wp))
        (canonicalHistoryMask k (sourceRangeLeafMask k J X Δ Wl))
        X Δ Wl j v (survivingIntegerState k j width P ρ x) u)
    else 0)

theorem survivingCorePairAmplitude_eq_data {a m H : ℝ} (ha : 0 ≤ a) (hm : 1 ≤ m)
    (k j : ℕ) (width : Role → ℕ) (B : ℕ → ℤ) (T : ℕ → ℝ) (J : ℤ)
    (P s v : ℤ) (σ ρ : Equiv.Perm (CopiedConstituent (schedule k j) j width))
    (t u : HistoryReconstruction.Tree j)
    (ht : RangeSupported (ranges a m j) j [] s t)
    (hu : RangeSupported (ranges a m j) j [] v u)
    (i : SurvivingPrimeIndex k j width) (x : Other i → ℤ) (gate : Bool) (r n : ℕ)
    {X Δ Wp Wl Tc Wc : ℝ} (hX : 1 ≤ X) (hH : Real.log 2 ≤ H)
    (hfreq : linearEnvelope a j*m ≤ H) (hP : |(P:ℝ)| ≤ Real.exp H)
    (M : ℕ) (hw : ∀q,width q ≤ M)
    (hvars : ∀z,|((insertCoordinate i x
      ((historyPairResidueModulus k j s (survivingSampledExpressions k j width P σ) t
        v (survivingSampledExpressions k j width P ρ) u*n+r:ℕ):ℤ) z : ℤ) : ℝ)| ≤ Real.exp H) :
    let e := survivingSampledExpressions k j width P σ
    let f := survivingSampledExpressions k j width P ρ
    let Q := historyPairResidueModulus k j s e t v f u
    let D := obstructionSizeFactor k j*(2*(M+1)+1)
    (canonicalSourceNormalizedData k B (fun l=>(bound a m l:ℤ)) T J j false true s v e f t u
      i x (r:ℤ) gate X Δ Wp Wl H D (survivingCopiedProductExpression k j width) Tc Wc).weight
      (𝓕 SchwartzCutoff.psi) ((Q*n+r:ℕ):ℝ) =
      survivingCorePairAmplitude k j width B (fun l=>(bound a m l:ℤ)) T J P s v σ ρ t u gate
        X Δ Wp Wl Tc Wc (insertCoordinate i x ((Q*n+r:ℕ):ℤ)) := by
  dsimp only
  have hH0 : 0 ≤ H := (Real.log_nonneg (by norm_num : (1:ℝ)≤2)).trans hH
  have he := survivingSampledExpressions_good k j width P σ
  have hf := survivingSampledExpressions_good k j width P ρ
  have hef := survivingSampledExpressions_fixedLogBound k j width P σ hH0 hP
  have hff := survivingSampledExpressions_fixedLogBound k j width P ρ hH0 hP
  have hpair := canonicalSourcePairData_weight_actual ha hm k j B T J false true s v
    (survivingSampledExpressions k j width P σ) (survivingSampledExpressions k j width P ρ)
    t u ht hu i x gate r n he hf (Δ:=Δ) (Wp:=Wp) (Wl:=Wl) hX hH hfreq (2*(M+1))
    (survivingSampledExpressions_syntaxSize k j width P σ M hw)
    (survivingSampledExpressions_syntaxSize k j width P ρ M hw) hef hff hvars
  dsimp only at hpair
  let q := historyPairResidueModulus k j s (survivingSampledExpressions k j width P σ) t
    v (survivingSampledExpressions k j width P ρ) u*n+r
  have hr := canonicalSourceNormalizedData_weight k B (fun l=>(bound a m l:ℤ)) T J j false true
    s v (survivingSampledExpressions k j width P σ) (survivingSampledExpressions k j width P ρ)
    t u i x (r:ℤ) gate X Δ Wp Wl H (obstructionSizeFactor k j*(2*(M+1)+1))
    (survivingCopiedProductExpression k j width) Tc Wc (q:ℤ)
    (survivingCopiedProductExpression_good k j width _) (𝓕 SchwartzCutoff.psi)
  simp only [Int.cast_natCast] at hr
  rw [hr,hpair]
  simp only [survivingCorePairAmplitude,survivingIntegerState,
    survivingSampledExpressions_eval,survivingCopiedProductExpression_eval,
    copiedWindowRatio,conjugateBy,Bool.false_eq_true,ite_false,ite_true]
  simp only [Real.exp_sub,Real.exp_add,Real.exp_neg,div_eq_mul_inv]
  rfl

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
