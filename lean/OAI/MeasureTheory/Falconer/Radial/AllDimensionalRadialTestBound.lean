import OAI.MeasureTheory.Falconer.Geometry.SurfaceTestNorm
import OAI.MeasureTheory.Falconer.Radial.EuclideanRadialDensity

namespace OAI

/-! Bounding the exact ambient radial test norm by its smooth density moment. -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem surfaceTestNorm_radial_density_rpow_le {n : ℕ}
    (a : Space (n+1) → ℝ≥0∞) (ha : Measurable a) {p q : ℝ}
    (hpq : p.HolderConjugate q) (x : Space (n+1)) :
    (surfaceTestNorm q ((volume.withDensity a).map (radialDirection x)))^p ≤
      ∫⁻ w : Sphere (n+1), (euclideanRadialDensity a x w)^p ∂sphereMeasure (n+1) := by
  have hρ : Measurable (euclideanRadialDensity a x) :=
    (euclideanRadialDensity_joint_measurable a ha).comp (measurable_const.prodMk measurable_id)
  have hb : surfaceTestNorm q ((volume.withDensity a).map (radialDirection x)) ≤
      (∫⁻ w : Sphere (n+1), (euclideanRadialDensity a x w)^p ∂sphereMeasure (n+1))^(1/p) := by
    apply iSup_le
    intro F
    apply iSup_le
    intro hF
    have hq : (∫⁻ w : Sphere (n+1), ‖F (w : Space (n+1))‖ₑ^q
        ∂sphereMeasure (n+1))^(1/q) ≤ 1 := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hpq.symm.pos).ne'
        ENNReal.ofReal_ne_top F.continuous.aestronglyMeasurable,
        ENNReal.toReal_ofReal hpq.symm.nonneg, surfaceMeasure,
        lintegral_map (by fun_prop) measurable_subtype_coe] at hF
      exact hF
    have hFm : Measurable (fun w : Sphere (n+1) => ‖F (w : Space (n+1))‖ₑ) :=
      (F.continuous.measurable.comp measurable_subtype_coe).enorm
    have hi := enorm_integral_le_lintegral_enorm
      (μ := (volume.withDensity a).map (radialDirection x)) (fun w => F w)
    rw [← ofReal_norm, radialDirection_withDensity a ha x,
      lintegral_map (by fun_prop) measurable_subtype_coe,
      lintegral_withDensity_eq_lintegral_mul _ hρ hFm] at hi
    have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (sphereMeasure (n+1)) hpq
      hρ.aemeasurable (show AEMeasurable (fun w : Sphere (n+1) => ‖F (w : Space (n+1))‖ₑ)
        (sphereMeasure (n+1)) by fun_prop)
    rw [radialDirection_withDensity a ha x]
    exact hi.trans (hh.trans ((mul_le_mul_right hq _).trans_eq (mul_one _)))
  have h := ENNReal.rpow_le_rpow hb hpq.nonneg
  rwa [← ENNReal.rpow_mul, one_div_mul_cancel hpq.pos.ne', ENNReal.rpow_one] at h

end Falconer

end OAI
