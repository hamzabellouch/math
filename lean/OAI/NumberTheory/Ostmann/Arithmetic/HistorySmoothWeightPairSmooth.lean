import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightRootCounterpart
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightSmooth
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightSourceXi

namespace OAI

noncomputable section
open scoped ContDiff FourierTransform
namespace Ostmann.Arithmetic.HistorySymbolicEncoding
open Construction HistoryOccurrenceVariables

theorem actualRealXi_log_contDiff (b s : ℕ) (X tb td G : ℝ)
    (hX : 0 < X) (outside : List ℕ) (houtside : ∀ q ∈ outside, 0 < q)
    {l : ℕ} {V : ℕ → ℕ} (h₁ h₂ : History l)
    (hs₁ : h₁.Supported V outside) (hs₂ : h₂.Supported V outside) :
    ContDiff ℝ ∞ (fun y : (Key h₁ → ℝ) × (Key h₂ → ℝ) =>
      actualRealXi b s X tb td G outside h₁ h₂ hs₁ hs₂
        (fun i => Real.exp (y.1 i)) (fun i => Real.exp (y.2 i))) := by
  exact ((actualRealHistoryScalar_log_contDiff b s X tb td G hX outside houtside h₁ hs₁).comp
    contDiff_fst).mul (Complex.conjCLE.contDiff.comp
      ((actualRealHistoryScalar_log_contDiff b s X tb td G hX outside houtside h₂ hs₂).comp contDiff_snd))

theorem actualRealXi_sum_log_contDiff (b s : ℕ) (X tb td G : ℝ)
    (hX : 0 < X) (outside : List ℕ) (houtside : ∀ q ∈ outside, 0 < q)
    {l : ℕ} {V : ℕ → ℕ} (h₁ h₂ : History l)
    (hs₁ : h₁.Supported V outside) (hs₂ : h₂.Supported V outside) :
    ContDiff ℝ ∞ (fun y : Key h₁ ⊕ Key h₂ → ℝ =>
      actualRealXi b s X tb td G outside h₁ h₂ hs₁ hs₂
        (fun i => Real.exp (y (Sum.inl i))) (fun i => Real.exp (y (Sum.inr i)))) := by
  exact (actualRealXi_log_contDiff b s X tb td G hX outside houtside h₁ h₂ hs₁ hs₂).comp
    (show ContDiff ℝ ∞ (fun y : Key h₁ ⊕ Key h₂ → ℝ =>
      ((fun i => y (Sum.inl i)),(fun i => y (Sum.inr i)))) by fun_prop)

theorem actualRealXi_rootCounterpart_log_contDiff {ι : Type}
    (b s : ℕ) (X tb td G : ℝ) (hX : 0 < X)
    (outside : List ℕ) (houtside : ∀ q ∈ outside, 0 < q)
    {l : ℕ} {V : ℕ → ℕ} (h₁ h₂ : History l)
    (hs₁ : h₁.Supported V outside) (hs₂ : h₂.Supported V outside)
    (T U : ℝ) (Hkeys Ukeys : List (Key h₁ ⊕ Key h₂)) (S : Finset ι)
    (center : ι → ℝ) (cellKey : ι → Key h₁ ⊕ Key h₂) :
    ContDiff ℝ ∞ (fun y : Key h₁ ⊕ Key h₂ → ℝ =>
      (rootCounterpart T U Hkeys Ukeys S center cellKey (fun i => Real.exp (y i)) : ℂ) *
      actualRealXi b s X tb td G outside h₁ h₂ hs₁ hs₂
        (fun i => Real.exp (y (Sum.inl i))) (fun i => Real.exp (y (Sum.inr i)))) := by
  exact (Complex.ofRealCLM.contDiff.comp
    (rootCounterpart_contDiff_exp T U Hkeys Ukeys S center cellKey)).mul
      (actualRealXi_sum_log_contDiff b s X tb td G hX outside houtside h₁ h₂ hs₁ hs₂)

theorem actualRealXi_integer_sample (b s : ℕ) (X tb td G : ℝ) (outside : List ℕ)
    {l : ℕ} {V : ℕ → ℕ} (h₁ h₂ : History l)
    (hs₁ : h₁.Supported V outside) (hs₂ : h₂.Supported V outside) :
    actualRealXi b s X tb td G outside h₁ h₂ hs₁ hs₂
      (fun i => (integerSample h₁ i : ℝ)) (fun i => (integerSample h₂ i : ℝ)) =
    smoothHistoryScalar X (fun t => (𝓕 SchwartzCutoff.psi) t) (sourceStateBins b s tb td)
      outside smoothPartition G h₁ *
    star (smoothHistoryScalar X (fun t => (𝓕 SchwartzCutoff.psi) t) (sourceStateBins b s tb td)
      outside smoothPartition G h₂) := by
  have h₁' := actualRealHistoryScalar_integer_sample b s X tb td G outside h₁ hs₁
  have h₂' := actualRealHistoryScalar_integer_sample b s X tb td G outside h₂ hs₂
  simp only [rationalSample,Rat.cast_intCast] at h₁' h₂'
  exact congrArg₂ (fun a b : ℂ => a * star b) h₁' h₂'

end Ostmann.Arithmetic.HistorySymbolicEncoding

end

end OAI
