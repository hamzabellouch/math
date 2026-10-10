import OAI.Probability.InvariantIsing.Spectral.SpectralEnergy

namespace OAI

/-! The temperature primitive of the finite-spectrum interaction energy. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem integral_finiteSpectralSlope_temperature (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    (∫ u in 0..t, finiteSpectralSlope ρ eig hρ hρsum (u * x)) =
      t * finiteR ρ eig hρ hρsum (t * x) := by
  have hc : Continuous (finiteThermalScalar ρ eig hρ hρsum x) :=
    continuous_id.mul ((continuous_finiteR ρ eig hρ hρsum).comp
      (continuous_const.mul continuous_id))
  have hd : ∀ u ∈ Ioo (0 : ℝ) t,
      HasDerivWithinAt (finiteThermalScalar ρ eig hρ hρsum x)
        (finiteSpectralSlope ρ eig hρ hρsum (u * x)) (Ioi u) u := by
    intro u hu
    have h := hasDerivWithinAt_finiteThermalScalar ρ eig hρ hρsum hx hu.1.le
    rw [mul_comm x u] at h
    exact h.mono fun y hy => (lt_trans hu.1 (show u < y from hy)).le
  have hint : IntervalIntegrable (fun u => finiteSpectralSlope ρ eig hρ hρsum (u * x))
      volume 0 t :=
    ((continuous_finiteSpectralSlope ρ eig hρ hρsum).comp
      (continuous_id.mul continuous_const)).intervalIntegrable 0 t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht hc.continuousOn hd hint
  simpa only [finiteThermalScalar, zero_mul, sub_zero, mul_comm x t] using hFTC

/-- Equation `up:primitive`, for the actual finite atomic spectral transform. -/
theorem integral_finiteInteractionEnergy (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {t : ℝ} (ht : 0 ≤ t) (p : OverlapPath) :
    (∫ u in 0..t, finiteInteractionEnergy ρ eig hρ hρsum u p) =
      spectralFunctional (fun x => t * finiteR ρ eig hρ hρsum (t * x)) p := by
  let K := ∑ a, |eig a|
  have heig : ∀ a, |eig a| ≤ K := by
    intro a
    exact Finset.single_le_sum (f := fun a => |eig a|)
      (fun a _ => abs_nonneg (eig a)) (Finset.mem_univ a)
  have hS : ∀ x, |finiteSpectralSlope ρ eig hρ hρsum x| ≤ K := by
    intro x
    exact abs_le.mpr (finiteSpectralSlope_bounds ρ eig hρ hρsum
      (fun a => (abs_le.mp (heig a)).1) (fun a => (abs_le.mp (heig a)).2) x)
  let f : ℝ → ℝ → ℝ := fun u r => finiteSpectralSlope ρ eig hρ hρsum (u * deficit p r)
  let : IsFiniteMeasure (volume.restrict (uIoc 0 t)) := by
    change IsFiniteMeasure (volume.restrict (Ioc (min 0 t) (max 0 t)))
    infer_instance
  have hm : Measurable (Function.uncurry f) :=
    (continuous_finiteSpectralSlope ρ eig hρ hρsum).measurable.comp
      (measurable_fst.mul ((continuous_deficit p).measurable.comp measurable_snd))
  have hi : Integrable (Function.uncurry f) ((volume.restrict (uIoc 0 t)).prod pathMeasure) := by
    apply (integrable_const K).mono' hm.aestronglyMeasurable
    exact ae_of_all _ fun z => by
      change ‖finiteSpectralSlope ρ eig hρ hρsum (z.1 * deficit p z.2)‖ ≤ K
      simpa only [Real.norm_eq_abs] using hS (z.1 * deficit p z.2)
  have hswap := intervalIntegral_integral_swap hi
  unfold finiteInteractionEnergy spectralFunctional
  rw [intervalIntegral.integral_const_mul]
  change (1 / 2 : ℝ) * (∫ u in 0..t, ∫ r, f u r ∂pathMeasure) =
    (1 / 2 : ℝ) * ∫ r, t * finiteR ρ eig hρ hρsum (t * deficit p r) ∂pathMeasure
  rw [hswap]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  exact integral_finiteSpectralSlope_temperature ρ eig hρ hρsum ht (deficit_nonneg p hr.2.le)

end InvariantIsing

end

end OAI
