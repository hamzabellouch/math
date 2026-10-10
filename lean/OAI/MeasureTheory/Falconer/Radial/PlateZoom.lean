import OAI.MeasureTheory.Falconer.Radial.RadialZoomBounds
import OAI.MeasureTheory.Falconer.Measures.StartingMeasures

namespace OAI

/-! # Exact affine normalization of the heavy-plate inputs -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radialZoom_full_frostman (μ : Measure (Space d))
    {a s C : ℝ} (ha : 0 < a) (c : Space d) (hfrost : FrostmanBallBound μ s C) :
    FrostmanBallBound (Measure.map (radialZoom a ha.ne' c) μ) s (C*a^(-s)) := by
  intro x r hr
  rw [radialZoom_ball_apply μ ha]
  have he : C*(r/a)^s = (C*a^(-s))*r^s := by
    rw [Real.div_rpow hr.le ha.le,Real.rpow_neg ha.le]
    ring
  rw [← he]
  exact hfrost _ _ (div_pos hr ha)

theorem radialZoom_zero_slab (μ : Measure (Space d))
    {a : ℝ} (ha : 0 < a) (w : Space d) (t r : ℝ) :
    Measure.map (radialZoom a ha.ne' (0:Space d)) μ
      {y | |inner ℝ w y-a*t| ≤ a*r} = μ {x | |inner ℝ w x-t| ≤ r} := by
  rw [Measure.map_apply (radialZoom a ha.ne' (0:Space d)).measurable
    (measurableSet_le (by fun_prop) measurable_const)]
  congr 1
  ext x
  simp only [mem_preimage,mem_ofPred_eq,radialZoom_apply,sub_zero,inner_smul_right]
  rw [show a*inner ℝ w x-a*t = a*(inner ℝ w x-t) by ring,abs_mul,abs_of_pos ha]
  exact mul_le_mul_iff_right₀ ha

theorem pullback_affine_slab {a R t : ℝ} (ha : 0 < a) (w x : Space d)
    (h : |inner ℝ w (a • x)-t| ≤ R) : |inner ℝ w x-t/a| ≤ R/a := by
  have he : inner ℝ w x-t/a = (inner ℝ w (a • x)-t)/a := by
    rw [inner_smul_right]
    field_simp
  rw [he,abs_div,abs_of_pos ha]
  exact div_le_div_of_nonneg_right h ha.le

end Falconer

end OAI
