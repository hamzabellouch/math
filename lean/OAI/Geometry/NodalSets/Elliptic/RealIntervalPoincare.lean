import OAI.Geometry.NodalSets.Elliptic.RealIntervalDerivativeControl

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_interval_poincare (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hab : a < b) :
    (∫ x in Icc a b, (f x-(∫ y in Icc a b, f y)/(b-a))^2) ≤
      (b-a)^2*(∫ x in Icc a b, (deriv f x)^2) := by
  let L := b-a
  let c := (∫ y in Icc a b, f y)/L
  let D := ∫ x in Icc a b, (deriv f x)^2
  have hL : 0 < L := sub_pos.mpr hab
  have hm : (volume.restrict (Icc a b)).real univ=L := by
    simp [hab.le,L]
  have hpt (x : ℝ) (hx : x ∈ Icc a b) : (f x-c)^2 ≤ L*D := by
    have hdiff : (∫ y in Icc a b, f x-f y) = L*(f x-c) := by
      rw [integral_sub (integrable_const _) hf.continuous.continuousOn.integrableOn_Icc,integral_const]
      change (volume.restrict (Icc a b)).real univ*f x-(∫ y in Icc a b, f y) = L*(f x-c)
      rw [hm]
      dsimp [c]
      field_simp
    have hcs := real_interval_integral_square_le (fun y ↦ f x-f y) (continuous_const.sub hf.continuous) hab
    rw [hdiff] at hcs
    have hbound := setIntegral_mono_on (μ := volume)
      ((continuous_const.sub hf.continuous).pow 2).continuousOn.integrableOn_Icc
      (integrable_const (L*D)) measurableSet_Icc
      (fun y hy ↦ real_interval_derivative_control f hf hab x y hx hy)
    rw [integral_const] at hbound
    change (∫ y in Icc a b, (f x-f y)^2) ≤ (volume.restrict (Icc a b)).real univ*(L*D) at hbound
    rw [hm] at hbound
    have hh := hcs.trans (mul_le_mul_of_nonneg_left hbound hL.le)
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hL)).mp
    nlinarith [hh]
  have hfinal := setIntegral_mono_on (μ := volume) ((hf.continuous.sub continuous_const).pow 2).continuousOn.integrableOn_Icc
    (integrable_const (L*D)) measurableSet_Icc hpt
  rw [integral_const] at hfinal
  change (∫ x in Icc a b, (f x-c)^2) ≤ (volume.restrict (Icc a b)).real univ*(L*D) at hfinal
  rw [hm] at hfinal
  change (∫ x in Icc a b, (f x-c)^2) ≤ L^2*D
  nlinarith [hfinal]

end
end Yau.Geometry

end OAI
