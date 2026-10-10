import OAI.Analysis.KadisonKastler.ModularStrongLimit
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

namespace OAI

/-! # The scalar logarithmic phase on the resolvent spectrum -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

def modularSpectralPhase (t s : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((t : ℂ) * ((Real.log (1 - s) - Real.log s : ℝ) : ℂ)))

theorem modularSpectralPhase_norm (t s : ℝ) : ‖modularSpectralPhase t s‖ = 1 := by
  rw [modularSpectralPhase, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

theorem modularPhaseScalar_norm (t ε : ℝ) (z : ℂ) : ‖modularPhaseScalar t ε z‖ = 1 := by
  rw [modularPhaseScalar, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

theorem modularSpectralPhase_measurable (t : ℝ) : Measurable (modularSpectralPhase t) := by
  apply Complex.continuous_exp.measurable.comp
  apply measurable_const.mul
  apply measurable_const.mul
  exact Complex.continuous_ofReal.measurable.comp
    ((Real.measurable_log.comp (measurable_const.sub measurable_id)).sub Real.measurable_log)

theorem regularizedLogScalar_tendsto {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    Tendsto (fun n => regularizedLogScalar (modularRegularizationScale n) s) atTop
      (𝓝 (Real.log (1 - s) - Real.log s)) := by
  have hp : Tendsto (fun n => s + modularRegularizationScale n) atTop (𝓝 s) := by
    simpa only [add_zero] using tendsto_const_nhds.add modularRegularizationScale_tendsto
  have hm : Tendsto (fun n => 1 - s + modularRegularizationScale n) atTop (𝓝 (1 - s)) := by
    simpa only [add_zero] using tendsto_const_nhds.add modularRegularizationScale_tendsto
  exact ((Real.continuousAt_log (sub_pos.mpr hs1).ne').tendsto.comp hm).sub
    ((Real.continuousAt_log hs.ne').tendsto.comp hp)

theorem modularPhaseScalar_tendsto (t : ℝ) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    Tendsto (fun n => modularPhaseScalar t (modularRegularizationScale n) (s : ℂ)) atTop
      (𝓝 (modularSpectralPhase t s)) := by
  have hl := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (regularizedLogScalar_tendsto hs hs1)
  have hp := (hl.const_mul (t : ℂ)).const_mul Complex.I
  have he := Complex.continuous_exp.continuousAt.tendsto.comp hp
  simpa only [Function.comp_def, modularPhaseScalar, modularSpectralPhase, Complex.ofReal_re] using he

end

end KadisonKastler

end OAI
