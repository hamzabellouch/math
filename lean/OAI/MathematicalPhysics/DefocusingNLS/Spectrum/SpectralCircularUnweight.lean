import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularCorrection

namespace OAI

/-! Removing the exponential weight from the coupled spectral correction. -/

open Filter
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def circularUnweight (κ : ℝ) (v : CircularTailSpace) (t : ℝ) : E₄ :=
  Real.exp (-κ*t) • circularTailEvaluation v t

theorem circularUnweight_hasDerivAt (κ t : ℝ) (νp νm η : ℂ) (m : ℕ)
    (q : ℂ) (v : CircularTailSpace) (R : E₄)
    (hv : HasDerivAt (circularTailEvaluation v)
      (κ • circularTailEvaluation v t+circularLeadingField t (circularTailEvaluation v t)+
        circularBoundedField νp νm η m q (circularTailEvaluation v t)+R) t) :
    HasDerivAt (circularUnweight κ v)
      (circularLeadingField t (circularUnweight κ v t)+
        circularBoundedField νp νm η m q (circularUnweight κ v t)+Real.exp (-κ*t) • R) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-κ*s)) (-κ*Real.exp (-κ*t)) t := by
    convert ((hasDerivAt_id t).const_mul (-κ)).exp using 1 <;> simp [mul_comm]
  apply (he.smul hv).congr_deriv
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [circularUnweight,circularLeadingField,circularBoundedField,
      Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,Complex.real_smul]
  all_goals push_cast; ring

theorem circularUnweight_norm (κ t : ℝ) (v : CircularTailSpace) :
    ‖circularUnweight κ v t‖ ≤ Real.exp (-κ*t)*‖v‖ := by
  rw [circularUnweight,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (circularTailEvaluation_norm v t) (Real.exp_nonneg _)

theorem circularUnweight_tendsto (κ : ℝ) (hκ : 0 < κ) (v : CircularTailSpace) :
    Tendsto (circularUnweight κ v) atTop (nhds 0) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-κ*t)) atTop (nhds 0) := by
    simpa only [Function.comp_def,neg_mul,id_eq] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hκ)
  apply squeeze_zero_norm (fun t => circularUnweight_norm κ t v)
  simpa only [zero_mul] using he.mul_const ‖v‖

end DefocusingNLS

end OAI
