import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarHeatKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace OAI

/-! The Gaussian change of scale and the actual time-zero limit of the heat
average. The bound by the normalized time-one Gaussian permits dominated
convergence even though the Gaussian has noncompact support. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem planarHeatKernel_sqrt_scale {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    planarHeatKernel t (Real.sqrt t • r) = t⁻¹ * planarHeatKernel 1 r := by
  have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  rw [planarHeatKernel, planarHeatKernel, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, hs]
  have he : -(t * ‖r‖ ^ 2) / (4 * t) = -‖r‖ ^ 2 / (4 * 1) := by
    field_simp
  rw [he]
  ring

theorem planarHeatAverage_scaled {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    planarHeatAverage t r = ∫ b, planarHeatKernel 1 b * planarForcing (r - Real.sqrt t • b) := by
  have hi := Measure.integral_comp_smul_of_nonneg (volume : Measure PlanarPosition)
    (fun b => planarHeatKernel t b * planarForcing (r - b)) (Real.sqrt t)
    (hR := Real.sqrt_nonneg t)
  simp only [finrank_euclideanSpace_fin, Real.sq_sqrt ht.le, smul_eq_mul,
    planarHeatKernel_sqrt_scale ht] at hi
  simp_rw [mul_assoc] at hi
  rw [integral_const_mul] at hi
  exact (mul_left_cancel₀ (inv_ne_zero ht.ne') hi).symm

theorem planarScaledHeatIntegrand_measurable (t : ℝ) (r : PlanarPosition) :
    AEStronglyMeasurable (fun b => planarHeatKernel 1 b *
      planarForcing (r - Real.sqrt t • b)) := by
  have hc : Continuous (fun b : PlanarPosition => r - Real.sqrt t • b) := by fun_prop
  exact ((planarHeatKernel_continuous 1).mul
    (planarForcing_C7.continuous.comp hc)).aestronglyMeasurable

theorem planarScaledHeatIntegrand_bound (t : ℝ) (r b : PlanarPosition) :
    ‖planarHeatKernel 1 b * planarForcing (r - Real.sqrt t • b)‖ ≤ planarHeatKernel 1 b := by
  have hk : 0 < planarHeatKernel 1 b := planarHeatKernel_positive (by norm_num) b
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk.le (planarForcing_nonnegative _))]
  exact mul_le_of_le_one_right hk.le (planarForcing_le_one _)

theorem planarScaledHeatIntegrand_tendsto (r b : PlanarPosition) :
    Tendsto (fun t : ℝ => planarHeatKernel 1 b * planarForcing (r - Real.sqrt t • b))
      (𝓝[>] (0 : ℝ)) (𝓝 (planarHeatKernel 1 b * planarForcing r)) := by
  have hs : Tendsto (fun t : ℝ => Real.sqrt t • b) (𝓝[>] 0) (𝓝 (0 : PlanarPosition)) := by
    have hs0 : Tendsto Real.sqrt (𝓝 (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt.tendsto
    simpa only [Real.sqrt_zero, zero_smul] using
      (hs0.mono_left nhdsWithin_le_nhds).smul_const b
  have hr : Tendsto (fun t : ℝ => r - Real.sqrt t • b) (𝓝[>] 0) (𝓝 r) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hs
  exact tendsto_const_nhds.mul (planarForcing_C7.continuous.continuousAt.tendsto.comp hr)

theorem planarHeatAverage_tendsto_zero (r : PlanarPosition) :
    Tendsto (fun t => planarHeatAverage t r) (𝓝[>] (0 : ℝ)) (𝓝 (planarForcing r)) := by
  have hconv : Tendsto
      (fun t : ℝ => ∫ b, planarHeatKernel 1 b * planarForcing (r - Real.sqrt t • b))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ b, planarHeatKernel 1 b * planarForcing r)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (F := fun t b => planarHeatKernel 1 b * planarForcing (r - Real.sqrt t • b))
      (f := fun b => planarHeatKernel 1 b * planarForcing r)
      (bound := planarHeatKernel 1)
    · exact Eventually.of_forall (fun t => planarScaledHeatIntegrand_measurable t r)
    · exact Eventually.of_forall (fun t => Eventually.of_forall (fun b =>
        planarScaledHeatIntegrand_bound t r b))
    · exact planarHeatKernel_integrable (by norm_num)
    · exact Eventually.of_forall (planarScaledHeatIntegrand_tendsto r)
  have hv : (∫ b, planarHeatKernel 1 b * planarForcing r) = planarForcing r := by
    rw [integral_mul_const, planarHeatKernel_integral (by norm_num), one_mul]
  rw [hv] at hconv
  apply hconv.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (planarHeatAverage_scaled ht r).symm

end ContinuumCoulomb

end

end OAI
