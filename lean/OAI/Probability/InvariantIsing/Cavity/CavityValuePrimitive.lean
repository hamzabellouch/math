import OAI.Probability.InvariantIsing.Cavity.CavityValueFubini
import OAI.Probability.InvariantIsing.Cavity.CavityRRightDerivative

namespace OAI

/-! Integration by parts for the cavity spectral contribution. Only the
one-sided spectral derivative is used at the zero deficit. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem cavity_spectral_integration_by_parts (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (p : OverlapPath) :
    (∫ r in 0..1, finiteR rho lam hrho hsum (deficit p r)) -
      (∫ r in 0..1, r * cavityFieldDensity rho lam hrho hsum p r *
        pathMeasure.real {s | p s ≤ r}) = finiteR rho lam hrho hsum 0 := by
  let R := finiteR rho lam hrho hsum
  let f := cavityFieldDensity rho lam hrho hsum p
  let F := fun r => pathMeasure.real {s | p s ≤ r}
  let E : Set ℝ := {r | 0 < pathMeasure {s | p s = r}}
  have hE : E.Countable := Measure.countable_meas_level_set_pos p.measurable
  have hcR : Continuous (fun r => R (deficit p r)) :=
    (continuous_finiteR rho lam hrho hsum).comp (continuous_deficit p)
  have hcf : Continuous f := continuous_cavityFieldDensity rho lam hrho hsum p
  have hiF : IntervalIntegrable (fun r => r * f r * F r) volume 0 1 :=
    (pathCDF_monotone p).intervalIntegrable.continuousOn_mul
      (continuous_id.mul hcf).continuousOn
  have hi : IntervalIntegrable (fun r => R (deficit p r) - r * f r * F r) volume 0 1 :=
    (hcR.intervalIntegrable 0 1).sub hiF
  have hd : ∀ r ∈ Ioo (0 : ℝ) 1 \ E,
      HasDerivAt (fun r => r * R (deficit p r)) (R (deficit p r) - r * f r * F r) r := by
    intro r hr
    have hn : pathMeasure {s | p s = r} = 0 := le_antisymm (le_of_not_gt hr.2) bot_le
    have hD := hasDerivAt_deficit_of_nonatom p r hn
    have hR := hasDerivWithinAt_cavityR_nonneg rho lam hrho hsum
      (deficit_nonneg p hr.1.2.le)
    have hmem : ∀ᶠ x in 𝓝 r, deficit p x ∈ Ici 0 := by
      filter_upwards [Iio_mem_nhds hr.1.2] with x hx
      exact deficit_nonneg p hx.le
    have hcomp := hR.comp_hasDerivAt r hD hmem
    convert! (hasDerivAt_id r).mul hcomp using 1
    dsimp only [R, f, F, cavityFieldDensity, Function.comp_apply, id_eq]
    ring
  have ht := integral_eq_of_hasDerivAt_off_countable_of_le
    (fun r => r * R (deficit p r)) (fun r => R (deficit p r) - r * f r * F r)
    (by norm_num : (0 : ℝ) ≤ 1) hE (continuous_id.mul hcR).continuousOn hd hi
  rw [intervalIntegral.integral_sub (hcR.intervalIntegrable 0 1) hiF] at ht
  simpa only [R, f, F, deficit_one, one_mul, zero_mul, sub_zero] using ht

end InvariantIsing

end

end OAI
