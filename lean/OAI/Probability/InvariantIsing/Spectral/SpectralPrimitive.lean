import OAI.Probability.InvariantIsing.Spectral.SpectralDeficitDerivative
import OAI.Probability.InvariantIsing.Spectral.SpectralOverlapPaths
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

namespace OAI

/-! The scalar primitive identity in the reconstructed spectral-group symbols. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem pathCDF_monotone (p : OverlapPath) :
    Monotone (fun r => pathMeasure.real {s | p s ≤ r}) := by
  intro r u hru
  exact measureReal_mono (fun s hs => hs.trans hru)

theorem hasDerivWithinAt_projectedResolvent_nonneg
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (a : ι)
    {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt (projectedResolvent ρ eig hρ hρsum a)
      (projectedResolventDerivative ρ eig hρ hρsum a x) (Ici 0) x := by
  rcases hx.eq_or_lt with h | h
  · subst x
    simpa only [projectedResolventDerivative, lt_self_iff_false, ite_false] using
      (hasDerivWithinAt_projectedResolvent_zero ρ eig hρ hρsum a).Ici_of_Ioi
  · exact (hasStrictDerivAt_projectedResolvent ρ eig hρ hρsum a h).hasDerivAt.hasDerivWithinAt

theorem continuousOn_projectedResolvent
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (a : ι) {c : ℝ} :
    ContinuousOn (projectedResolvent ρ eig hρ hρsum a) (Icc 0 c) := by
  intro x hx
  exact (hasDerivWithinAt_projectedResolvent_nonneg ρ eig hρ hρsum a hx.1).continuousWithinAt.mono
    (fun _ hy => hy.1)

/-- The FTC step in `rot:function-path`, valid even when the overlap law has atoms. -/
theorem integral_spectralDensity_mul_CDF (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) {q : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) :
    (∫ r in q..1, spectralPathDensity ρ eig hρ hρsum p a r *
      pathMeasure.real {s | p s ≤ r}) =
      projectedResolvent ρ eig hρ hρsum a (deficit p q) := by
  let E : Set ℝ := {r | 0 < pathMeasure {s | p s = r}}
  have hE : E.Countable := Measure.countable_meas_level_set_pos p.measurable
  have hcf : ContinuousOn (fun r => projectedResolvent ρ eig hρ hρsum a (deficit p r))
      (Icc 0 1) :=
    (continuousOn_projectedResolvent ρ eig hρ hρsum a).comp
      (continuous_deficit p).continuousOn (fun _ hr => deficit_mem_unit p hr)
  have hcd := (spectralPathDensity_continuousOn ρ eig hρ hρsum p a).mono
    (Icc_subset_Icc hq.1 le_rfl)
  have hint : IntervalIntegrable (fun r => spectralPathDensity ρ eig hρ hρsum p a r *
      pathMeasure.real {s | p s ≤ r}) volume q 1 :=
    (pathCDF_monotone p).intervalIntegrable.continuousOn_mul
      ((uIcc_of_le hq.2).symm ▸ hcd)
  have hderiv : ∀ r ∈ Ioo q 1 \ E,
      HasDerivAt (fun r => projectedResolvent ρ eig hρ hρsum a (deficit p r))
        (-(spectralPathDensity ρ eig hρ hρsum p a r *
          pathMeasure.real {s | p s ≤ r})) r := by
    intro r hr
    have hzero : pathMeasure {s | p s = r} = 0 := le_antisymm (le_of_not_gt hr.2) bot_le
    have hdD := hasDerivAt_deficit_of_nonatom p r hzero
    have hdf := hasDerivWithinAt_projectedResolvent_nonneg ρ eig hρ hρsum a
      (deficit_nonneg p hr.1.2.le)
    have ht : ∀ᶠ u in 𝓝 r, deficit p u ∈ Ici 0 := by
      filter_upwards [Iio_mem_nhds hr.1.2] with u hu
      exact deficit_nonneg p hu.le
    convert hdf.comp_hasDerivAt r hdD ht using 1
    · rfl
    · dsimp [spectralPathDensity]
      ring
  have hFTC := integral_eq_of_hasDerivAt_off_countable_of_le
    (fun r => projectedResolvent ρ eig hρ hρsum a (deficit p r))
    (fun r => -(spectralPathDensity ρ eig hρ hρsum p a r *
      pathMeasure.real {s | p s ≤ r})) hq.2 hE
    (hcf.mono (Icc_subset_Icc hq.1 le_rfl)) hderiv hint.neg
  rw [intervalIntegral.integral_neg, deficit_one] at hFTC
  have hz : projectedResolvent ρ eig hρ hρsum a 0 = 0 := by
    simp only [projectedResolvent, lt_self_iff_false, ite_false]
  rw [hz] at hFTC
  linarith

end InvariantIsing

end

end OAI
