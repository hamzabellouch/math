import OAI.Geometry.RCD.Metric.ProbabilityDominationL1
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

namespace OAI

/-! # Strong L² limits tested against probabilities with bounded compression -/

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MeasurableSpace X]

theorem integral_abs_le_l2_of_domination (μ ν : Measure X) [IsProbabilityMeasure ν]
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (hν : ν ≤ C • μ)
    (f : X → ℝ) (hf : MemLp f 2 μ) :
    (∫ x, |f x| ∂ν) ≤ (C ^ (1/2 : ℝ)).toReal * (eLpNorm f 2 μ).toReal := by
  have hv := hf.of_measure_le_smul hC hν
  have hnorm : (∫ x, |f x| ∂ν) = (eLpNorm f 1 ν).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm hv.aestronglyMeasurable]
    simpa only [Real.norm_eq_abs] using integral_norm_eq_lintegral_enorm hv.aestronglyMeasurable
  rw [hnorm, ← ENNReal.toReal_mul]
  apply ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hC) hf.eLpNorm_ne_top)
  apply (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1:ℝ≥0∞) ≤ 2)).trans
  simpa using (eLpNorm_le_of_measure_le_smul (f := f) (p := 2) hν)

theorem uniform_l2_probability_pairing (μ : Measure X)
    (ν : Y → Measure X) [∀ y, IsProbabilityMeasure (ν y)]
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (hν : ∀ y, ν y ≤ C • μ)
    (F : ℕ → Lp ℝ 2 μ) (f : Lp ℝ 2 μ) (hF : Tendsto F atTop (𝓝 f)) :
    TendstoUniformly (fun k y => ∫ x, F k x ∂ν y) (fun y => ∫ x, f x ∂ν y) atTop := by
  have hn : Tendsto (fun k => (C ^ (1/2:ℝ)).toReal * ‖F k-f‖) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero,mul_zero] using (hF.sub (tendsto_const_nhds (x := f))).norm.const_mul
      (C ^ (1/2:ℝ)).toReal
  apply Metric.tendstoUniformly_iff.mpr
  intro e he
  filter_upwards [(tendsto_order.mp hn).2 e he] with k hk y
  have hv (g : Lp ℝ 2 μ) : Integrable g (ν y) :=
    (((Lp.memLp g).of_measure_le_smul hC (hν y)).mono_exponent
      (by norm_num : (1:ℝ≥0∞) ≤ 2)).integrable (by norm_num)
  have hbound := integral_abs_le_l2_of_domination μ (ν y) hC (hν y)
    (fun x => (F k-f : Lp ℝ 2 μ) x) (Lp.memLp (F k-f))
  have hae : F k-f =ᵐ[ν y] fun x => F k x-f x :=
    (Measure.absolutelyContinuous_of_le_smul (hν y)).ae_eq (Lp.coeFn_sub (F k) f)
  have heq : (∫ x, |(F k-f : Lp ℝ 2 μ) x| ∂ν y) = ∫ x, |F k x-f x| ∂ν y :=
    integral_congr_ae (by filter_upwards [hae] with x hx; rw [hx])
  rw [heq] at hbound
  change (∫ x, |F k x-f x| ∂ν y) ≤ (C ^ (1/2:ℝ)).toReal * ‖F k-f‖ at hbound
  have hi := abs_integral_le_integral_abs (f := fun x => F k x-f x) (μ := ν y)
  rw [integral_sub (hv (F k)) (hv f)] at hi
  rw [Real.dist_eq,abs_sub_comm]
  exact (hi.trans hbound).trans_lt hk

end RegularPointCoordinates

end

end OAI
