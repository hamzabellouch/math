import OAI.Geometry.RCD.Harmonic.UniformLocalL1Pairing

namespace OAI

/-! # Uniform local L1 differences pair with compressed laws -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MeasurableSpace X]

theorem uniform_local_difference_pairing (μ : Measure X) {S : Set X}
    (ν : Y → Measure X) {C : ℝ≥0∞} (hC : C ≠ ⊤) (hν : ∀ y, ν y ≤ C • μ)
    (F : ℕ → Y → X → ℝ) (g : Y → X → ℝ)
    (hF : ∀ k y, Integrable (F k y) (μ.restrict S))
    (hg : ∀ y, Integrable (g y) (μ.restrict S))
    (he : TendstoUniformly (fun k y => ∫ x in S, |F k y x-g y x| ∂μ)
      (fun _ => 0) atTop) :
    TendstoUniformly (fun k y => (∫ x in S, F k y x ∂ν y)-(∫ x in S, g y x ∂ν y))
      (fun _ => 0) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro e hepos
  have he' : 0 < e/(C.toReal+1) := div_pos hepos (by positivity)
  filter_upwards [(Metric.tendstoUniformly_iff.mp he) (e/(C.toReal+1)) he'] with k hk y
  have hνS : (ν y).restrict S ≤ C • μ.restrict S := by
    simpa only [Measure.restrict_smul] using Measure.restrict_mono (subset_refl S) (hν y)
  have hb := integral_difference_le_of_domination (μ.restrict S) ((ν y).restrict S)
    hC hνS (hF k y) (hg y)
  have hsmall : (∫ x in S, |F k y x-g y x| ∂μ) < e/(C.toReal+1) := by
    have hh := hk y
    simpa only [dist_zero_left,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun x => abs_nonneg _)] using hh
  have hce : C.toReal*(e/(C.toReal+1)) < e := by
    have heq : (e/(C.toReal+1))*(C.toReal+1)=e := div_mul_cancel₀ e (by positivity)
    nlinarith [ENNReal.toReal_nonneg (a := C)]
  have hb' := hb.trans_lt ((mul_le_mul_of_nonneg_left hsmall.le ENNReal.toReal_nonneg).trans_lt hce)
  simpa only [dist_zero_left,Real.dist_eq,Real.norm_eq_abs] using hb'

end RegularPointCoordinates

end

end OAI
