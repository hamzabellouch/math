import Mathlib
import OAI.Analysis.HardSphere.Bridges.BridgeHighMoment

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

def scaleMoment (p : ℕ) (t r : ℝ) (s w : Time) : ℝ :=
  (3^p*3*2^(p+1))*(Real.sqrt (2*t*(1-(s:ℝ))*(w:ℝ))/r)^p*normPowerMean p
lemma scaleMoment_nonneg (p : ℕ) {t r : ℝ} (hr : 0≤ r) (s w : Time) : 0≤ scaleMoment p t r s w := by
  unfold scaleMoment
  exact mul_nonneg
    (mul_nonneg (by positivity) (pow_nonneg (div_nonneg (Real.sqrt_nonneg _) hr) p))
    (normPowerMean_nonneg p)
lemma incrementFluctuation_scale_mean {t r : ℝ} (ht : 0≤ t) (hr : 0< r)
    (s w : Time) (p : ℕ) (hp : p≠0) :
    ∫β,(incrementFluctuation t r s w β)^p ∂law≤ scaleMoment p t r s w := by
  simp only [incrementFluctuation,mul_pow,integral_const_mul]
  calc
    _ ≤ (Real.sqrt (2*t)/r)^p*((3^p*3*2^(p+1))*(Real.sqrt ((1-(s:ℝ))*(w:ℝ)))^p*normPowerMean p) :=
      mul_le_mul_of_nonneg_left (incrementSize_power_mean s w p hp) (by positivity)
    _ = _ := by
      unfold scaleMoment
      rw [show 2*t*(1-(s:ℝ))*(w:ℝ)=(2*t)*((1-(s:ℝ))*(w:ℝ)) by ring,Real.sqrt_mul (show 0≤2*t by positivity)]
      simp only [mul_pow,div_pow]
      ring

lemma incrementFluctuation_scale_tail {t r R : ℝ} (ht : 0≤ t) (hr : 0< r) (hR : 0< R)
    (s w : Time) (p : ℕ) (hp : p≠0) :
    law {β | R≤ incrementFluctuation t r s w β}≤ ENNReal.ofReal (scaleMoment p t r s w)/(ENNReal.ofReal R)^p := by
  have hi : Integrable (fun β ↦ (incrementFluctuation t r s w β)^p) law := by
    unfold incrementFluctuation
    simp only [mul_pow]
    have h := (incrementSize_memLp_power s w p).integrable_norm_pow hp
    simp only [Real.norm_eq_abs,abs_of_nonneg (incrementSize_nonneg s w _)] at h
    exact h.const_mul _
  have hm := ((incrementFluctuation_continuous t r s w).pow p).measurable.ennreal_ofReal
  have h := meas_ge_le_lintegral_div (μ:=law) hm.aemeasurable
    (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hR p))) ENNReal.ofReal_ne_top
  apply (measure_mono (show {β | R≤ incrementFluctuation t r s w β}⊆
      {β | ENNReal.ofReal (R^p)≤ ENNReal.ofReal ((incrementFluctuation t r s w β)^p)} from
    fun β hβ ↦ ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hR.le hβ p))).trans
  apply h.trans
  rw [ENNReal.ofReal_pow hR.le]
  apply ENNReal.div_le_div_right
  change (∫⁻β,ENNReal.ofReal ((incrementFluctuation t r s w β)^p) ∂law)≤ _
  rw [←ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun β ↦ pow_nonneg (incrementFluctuation_nonneg hr.le s w β) p))]
  exact ENNReal.ofReal_le_ofReal (incrementFluctuation_scale_mean ht hr s w p hp)

end HardSphere.Bridge

end
end

end

end OAI
