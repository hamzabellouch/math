import OAI.Geometry.RCD.Metric.ProbabilityDominationL1

namespace OAI

/-! # Uniform local L¹ limits pair with all laws of a fixed compression bound -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MeasurableSpace X] (μ : Measure X)

theorem uniform_local_L1_pairing {S : Set X}
    (ν : Y → Measure X) {C : ℝ≥0∞} (hC : C ≠ ⊤) (hν : ∀ y, ν y ≤ C • μ)
    (J : ℕ → Y → Lp ℝ 1 (μ.restrict S))
    (hJ : TendstoUniformly (fun k y => ∫ x in S, |J k y x| ∂μ) (fun _ => 0) atTop) :
    TendstoUniformly (fun k y => ∫ x in S, J k y x ∂ν y) (fun _ => 0) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro e he
  have he' : 0 < e/(C.toReal+1) := div_pos he (by positivity)
  filter_upwards [(Metric.tendstoUniformly_iff.mp hJ) (e/(C.toReal+1)) he'] with k hk y
  have hνS : (ν y).restrict S ≤ C • μ.restrict S := by
    simpa only [Measure.restrict_smul] using Measure.restrict_mono (subset_refl S) (hν y)
  have hb := integral_difference_le_of_domination (μ.restrict S) ((ν y).restrict S) hC hνS
    (memLp_one_iff_integrable.mp (Lp.memLp (J k y))) (integrable_zero X ℝ _)
  have hsmall : (∫ x in S, |J k y x| ∂μ) < e/(C.toReal+1) := by
    have hh := hk y
    simpa only [dist_zero_left,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun x => abs_nonneg _)] using hh
  simp only [Pi.zero_apply,sub_zero,integral_zero] at hb
  have hce : C.toReal*(e/(C.toReal+1)) < e := by
    have hden : 0 < C.toReal+1 := by positivity
    have heq : (e/(C.toReal+1))*(C.toReal+1)=e := div_mul_cancel₀ e (ne_of_gt hden)
    nlinarith [mul_pos he' zero_lt_one]
  have hb' := hb.trans_lt ((mul_le_mul_of_nonneg_left hsmall.le ENNReal.toReal_nonneg).trans_lt hce)
  simpa only [dist_zero_right,dist_zero_left] using hb'

end RegularPointCoordinates

end

end OAI
