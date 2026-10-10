import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFieldAnalytic
import Mathlib.Analysis.Normed.Operator.Banach

namespace OAI

/-! The weighted spectral correction resolvent is holomorphic wherever the tail contracts. -/

open scoped BoundedContinuousFunction
namespace DefocusingNLS

noncomputable def circularCorrectionResolvent (κ : ℝ) (hκ : 0 < κ)
    (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m) (q : ℝ →ᵇ ℂ) (lam : ℂ) :
    CircularTailSpace →L[ℂ] CircularTailSpace :=
  Ring.inverse (1-circularTailCLM κ hκ*
    circularFieldOperator (νp-2*lam) (νm-2*lam) η m hm q)

theorem circularCorrection_isUnit (κ : ℝ) (hκ : 0 < κ) (νp νm η : ℂ)
    (m : ℕ) (hm : 1 ≤ m) (q : ℝ →ᵇ ℂ)
    (hgap : circularFieldBound νp νm η m ‖q‖ < κ) :
    IsUnit (1-circularTailCLM κ hκ*circularFieldOperator νp νm η m hm q) := by
  have hn : ‖circularTailCLM κ hκ*circularFieldOperator νp νm η m hm q‖ < 1 := by
    calc
      _ ≤ ‖circularTailCLM κ hκ‖*‖circularFieldOperator νp νm η m hm q‖ :=
        (circularTailCLM κ hκ).opNorm_comp_le (circularFieldOperator νp νm η m hm q)
      _ ≤ (1/κ)*circularFieldBound νp νm η m ‖q‖ :=
        mul_le_mul (circularTailCLM_norm κ hκ) (circularFieldOperator_norm νp νm η m hm q)
          (ContinuousLinearMap.opNorm_nonneg _) (by positivity)
      _ < 1 := by rw [one_div_mul_eq_div]; exact (div_lt_one hκ).mpr hgap
  convert! (isUnit_one_sub_of_norm_lt_one
    (R := CircularTailSpace →L[ℂ] CircularTailSpace)
    (x := circularTailCLM κ hκ*circularFieldOperator νp νm η m hm q) (by convert! hn))

theorem circularCorrectionResolvent_analyticAt (κ : ℝ) (hκ : 0 < κ)
    (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m) (q : ℝ →ᵇ ℂ) (z : ℂ)
    (hgap : circularFieldBound (νp-2*z) (νm-2*z) η m ‖q‖ < κ) :
    AnalyticAt ℂ (circularCorrectionResolvent κ hκ νp νm η m hm q) z := by
  let D := fun lam => 1-circularTailCLM κ hκ*
    circularFieldOperator (νp-2*lam) (νm-2*lam) η m hm q
  have hp : AnalyticAt ℂ (fun lam => circularTailCLM κ hκ*
      circularFieldOperator (νp-2*lam) (νm-2*lam) η m hm q) z := by
    convert! (AnalyticAt.mul (𝕜 := ℂ) (A := CircularTailSpace →L[ℂ] CircularTailSpace) (z := z)
      (f := fun _ : ℂ => circularTailCLM κ hκ)
      (g := fun lam => circularFieldOperator (νp-2*lam) (νm-2*lam) η m hm q)
      (by exact analyticAt_const)
      (by convert! circularFieldOperator_analyticAt νp νm η m hm q z))
  have hD : AnalyticAt ℂ D z := by
    convert! (analyticAt_const (v := (1 : CircularTailSpace →L[ℂ] CircularTailSpace))).sub
      hp
  have hu : IsUnit (D z) := circularCorrection_isUnit κ hκ _ _ η m hm q hgap
  have hi : AnalyticAt ℂ Ring.inverse (D z) := by
    have hi := analyticAt_inverse (𝕜 := ℂ)
      (A := CircularTailSpace →L[ℂ] CircularTailSpace)
      (by convert! hu.unit)
    convert! hi using 1
  exact hi.comp hD

theorem circularCorrectionResolvent_solve (κ : ℝ) (hκ : 0 < κ)
    (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m) (q : ℝ →ᵇ ℂ) (lam : ℂ)
    (hgap : circularFieldBound (νp-2*lam) (νm-2*lam) η m ‖q‖ < κ)
    (r : CircularTailSpace) :
    let v := circularCorrectionResolvent κ hκ νp νm η m hm q lam (circularTailCLM κ hκ r)
    v=circularTailCLM κ hκ (circularFieldOperator (νp-2*lam) (νm-2*lam) η m hm q v+r) := by
  intro v
  have hu := circularCorrection_isUnit κ hκ (νp-2*lam) (νm-2*lam) η m hm q hgap
  have he := congrArg (fun A : CircularTailSpace →L[ℂ] CircularTailSpace =>
    A (circularTailCLM κ hκ r)) (Ring.mul_inverse_cancel _ hu)
  change v-circularTailCLM κ hκ
    (circularFieldOperator (νp-2*lam) (νm-2*lam) η m hm q v)=circularTailCLM κ hκ r at he
  rw [map_add]
  simpa only [add_comm] using sub_eq_iff_eq_add.mp he

end DefocusingNLS

end OAI
