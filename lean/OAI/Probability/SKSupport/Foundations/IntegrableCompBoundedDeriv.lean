import Mathlib
import OAI.Probability.SKSupport.Model

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma integrable_comp_of_bounded_deriv [IsFiniteMeasure P] {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (C : ℝ≥0) (hC : ∀ x, |deriv f x| ≤ C) {Y : Ω → ℝ} (hY : Integrable Y P) :
    Integrable (fun ω => f (Y ω)) P := by
  have hl : LipschitzWith C f := lipschitzWith_of_nnnorm_deriv_le hf
    (fun x => show ‖deriv f x‖₊ ≤ C from by exact_mod_cast hC x)
  apply ((integrable_const ‖f 0‖).add (hY.norm.const_mul (C:ℝ))).mono'
    (hf.continuous.comp_aestronglyMeasurable hY.aestronglyMeasurable)
  filter_upwards [] with ω
  have h := hl.norm_sub_le (Y ω) 0
  simp only [sub_zero] at h
  have htri := norm_add_le (f (Y ω)-f 0) (f 0)
  rw [sub_add_cancel] at htri
  dsimp
  simp only [Real.norm_eq_abs] at h htri
  linarith

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI
