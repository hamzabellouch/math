import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! Measurable bounded scalar data are integrable on every finite interval. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem intervalIntegrable_of_measurable_bound {g : ℝ → ℝ}
    (hg : Measurable g) {a b C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ x ∈ uIcc a b, |g x| ≤ C) : IntervalIntegrable g volume a b := by
  apply (intervalIntegrable_iff' (by finiteness)).mpr
  have hi : IntegrableOn (fun _ : ℝ => C) (uIcc a b) volume :=
    integrableOn_const measure_Icc_lt_top.ne
  apply hi.mono' hg.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIcc] with x hx
  simpa only [Real.norm_eq_abs] using hb x hx

end CircleDomainRigidity

end

end OAI
