import OAI.NumberTheory.CubicMoment.Estimates.CubicWhittakerEnergy
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Continuity of the squared Mellin mass at the exponent needed in the
Rankin integral. The two endpoint powers give an integrable majorant. -/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CubicFirstMoment

lemma cubicWhittakerEnergy_domination {σ v : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hv : 0 < v) :
    ‖v^(2*σ-1)*‖cubicThetaWhittaker v‖^2‖ ≤
      v^(2*(0:ℝ)-1)*‖cubicThetaWhittaker v‖^2 +
      v^(2*(1:ℝ)-1)*‖cubicThetaWhittaker v‖^2 := by
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hv.le _) (sq_nonneg _))]
  by_cases hv1 : v ≤ 1
  · have hp : v^(2*σ-1) ≤ v^(2*(0:ℝ)-1) :=
      Real.rpow_le_rpow_of_exponent_ge hv hv1 (by linarith)
    exact (mul_le_mul_of_nonneg_right hp (sq_nonneg _)).trans
      (le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hv.le _) (sq_nonneg _)))
  · have hp : v^(2*σ-1) ≤ v^(2*(1:ℝ)-1) :=
      Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hv1) (by linarith)
    exact (mul_le_mul_of_nonneg_right hp (sq_nonneg _)).trans
      (le_add_of_nonneg_left (mul_nonneg (Real.rpow_nonneg hv.le _) (sq_nonneg _)))

theorem cubicWhittakerEnergyMass_tendsto_zero :
    Tendsto cubicWhittakerEnergyMass (𝓝[>] 0) (𝓝 (cubicWhittakerEnergyMass 0)) := by
  let bound (v : ℝ) := v^(2*(0:ℝ)-1)*‖cubicThetaWhittaker v‖^2 +
      v^(2*(1:ℝ)-1)*‖cubicThetaWhittaker v‖^2
  have hb : IntegrableOn bound (Ioi 0) :=
    (cubicWhittakerEnergy_integrable (by norm_num : (0:ℝ) ≤ 0)).add
      (cubicWhittakerEnergy_integrable (by norm_num : (0:ℝ) ≤ 1))
  apply tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hb ?_
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (cubicWhittakerEnergy_integrable (le_of_lt hσ)).aestronglyMeasurable
  · have hs0 : ∀ᶠ σ : ℝ in 𝓝 0, σ < 1 := Iio_mem_nhds (by norm_num : (0:ℝ) < 1)
    have hs : ∀ᶠ σ : ℝ in 𝓝[>] 0, σ < 1 := hs0.filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hs] with σ hσ hσ1
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact cubicWhittakerEnergy_domination hσ.le hσ1.le hv
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hp : ContinuousAt (fun σ : ℝ => v^(2*σ-1)) 0 :=
      (Real.continuousAt_const_rpow (ne_of_gt hv)).comp (f := fun σ : ℝ => 2*σ-1) (by fun_prop)
    exact (hp.mul continuousAt_const).tendsto.mono_left nhdsWithin_le_nhds

end CubicFirstMoment

end

end OAI
