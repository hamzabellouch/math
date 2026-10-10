import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralResolventAnalytic

namespace OAI

/-! Holomorphic forcing gives the actual bounded spectral correction, with its equation and estimate. -/

open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)
local notation "End₄" => CircularTailSpace →L[ℂ] CircularTailSpace

noncomputable def circularResolvedCorrection (κ : ℝ) (hκ : 0 < κ)
    (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m) (q : ℝ →ᵇ ℂ)
    (r : ℂ → CircularTailSpace) (lam : ℂ) : CircularTailSpace :=
  circularCorrectionResolvent κ hκ νp νm η m hm q lam (circularTailCLM κ hκ (r lam))

theorem circularResolvedCorrection_analyticAt (κ : ℝ) (hκ : 0 < κ)
    (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m) (q : ℝ →ᵇ ℂ)
    (r : ℂ → CircularTailSpace) (z : ℂ) (hr : AnalyticAt ℂ r z)
    (hgap : circularFieldBound (νp-2*z) (νm-2*z) η m ‖q‖ < κ) :
    AnalyticAt ℂ (circularResolvedCorrection κ hκ νp νm η m hm q r) z := by
  have hi := circularCorrectionResolvent_analyticAt κ hκ νp νm η m hm q z hgap
  have ht : AnalyticAt ℂ (fun lam => circularTailCLM κ hκ (r lam)) z := by
    convert! ((circularTailCLM κ hκ).analyticAt (r z)).comp hr
  have ha : AnalyticAt ℂ (fun p : End₄ × CircularTailSpace => p.1 p.2)
      (circularCorrectionResolvent κ hκ νp νm η m hm q z,circularTailCLM κ hκ (r z)) := by
    convert! ((ContinuousLinearMap.apply ℂ CircularTailSpace).flip).analyticAt_bilinear
      (circularCorrectionResolvent κ hκ νp νm η m hm q z,circularTailCLM κ hκ (r z))
  exact ha.comp₂ hi ht

theorem circularResolvedCorrection_norm (κ : ℝ) (hκ : 0 < κ)
    (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m) (q : ℝ →ᵇ ℂ)
    (r : ℂ → CircularTailSpace) (lam : ℂ)
    (hgap : circularFieldBound (νp-2*lam) (νm-2*lam) η m ‖q‖ < κ) :
    ‖circularResolvedCorrection κ hκ νp νm η m hm q r lam‖ ≤
      ‖r lam‖/(κ-circularFieldBound (νp-2*lam) (νm-2*lam) η m ‖q‖) := by
  let v := circularResolvedCorrection κ hκ νp νm η m hm q r lam
  let B := circularFieldOperator (νp-2*lam) (νm-2*lam) η m hm q
  have hv : v=circularTailCLM κ hκ (B v+r lam) :=
    circularCorrectionResolvent_solve κ hκ νp νm η m hm q lam hgap (r lam)
  have hBv : ‖B v‖ ≤ circularFieldBound (νp-2*lam) (νm-2*lam) η m ‖q‖*‖v‖ := by
    change ‖circularFieldBounded (νp-2*lam) (νm-2*lam) η m hm q v‖ ≤ _
    exact circularFieldBounded_norm (νp-2*lam) (νm-2*lam) η m hm q v
  have hadd : ‖B v+r lam‖ ≤ ‖B v‖+‖r lam‖ := norm_add_le _ _
  have hb : ‖B v+r lam‖ ≤
      circularFieldBound (νp-2*lam) (νm-2*lam) η m ‖q‖*‖v‖+‖r lam‖ :=
    hadd.trans (add_le_add hBv le_rfl)
  have he : ‖v‖ ≤ (circularFieldBound (νp-2*lam) (νm-2*lam) η m ‖q‖*‖v‖+‖r lam‖)/κ := by
    calc
      _ = ‖circularTailCLM κ hκ (B v+r lam)‖ := congrArg norm hv
      _ ≤ ‖B v+r lam‖/κ := circularTail_norm κ hκ _
      _ ≤ _ := div_le_div_of_nonneg_right hb hκ.le
  apply (le_div_iff₀ (sub_pos.mpr hgap)).mpr
  have he' := (le_div_iff₀ hκ).mp he
  nlinarith

theorem circularResolvedCorrection_hasDerivAt (κ : ℝ) (hκ : 0 < κ)
    (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m) (q : ℝ →ᵇ ℂ)
    (r : ℂ → CircularTailSpace) (lam : ℂ)
    (hgap : circularFieldBound (νp-2*lam) (νm-2*lam) η m ‖q‖ < κ) (t : ℝ) :
    let v := circularResolvedCorrection κ hκ νp νm η m hm q r lam
    HasDerivAt (circularTailEvaluation v)
      (κ • circularTailEvaluation v t+circularLeadingField t (circularTailEvaluation v t)+
        circularBoundedField (νp-2*lam) (νm-2*lam) η m (q t) (circularTailEvaluation v t)+
        circularTailEvaluation (r lam) t) t := by
  intro v
  let B := circularFieldOperator (νp-2*lam) (νm-2*lam) η m hm q
  have hv : circularTail κ hκ (B v+r lam)=v :=
    (circularCorrectionResolvent_solve κ hκ νp νm η m hm q lam hgap (r lam)).symm
  have hd := circularTail_hasDerivAt κ hκ (B v+r lam) t
  dsimp only at hd
  rw [hv] at hd
  apply hd.congr_deriv
  have he := circularFieldOperator_evaluation (νp-2*lam) (νm-2*lam) η m hm q v t
  change circularTailEvaluation (B v) t=_ at he
  rw [← he]
  apply Prod.ext <;> apply Prod.ext
  all_goals
    simp only [circularTailEvaluation,circularLeadingField,Prod.fst_add,Prod.snd_add,
      Prod.smul_fst,Prod.smul_snd,BoundedContinuousFunction.add_apply]
    abel

end DefocusingNLS

end OAI
