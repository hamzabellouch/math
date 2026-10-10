import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace OAI

/-! Integrating the nonnegative boundary error over physical space and
one finite translation interval. Integrability follows from the proved
pointwise average bound, rather than being assumed on the product. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert
variable {X : Type*} [MeasurableSpace X]

theorem nonnegative_translation_average_integral_le
    (μ : Measure X) [SFinite μ] (R : ℝ) (hR : 0 < R)
    (f : ℝ×X → ℝ) (hf : Measurable f) (hf0 : ∀ z, 0 ≤ f z)
    (hfi : ∀ᵐ x ∂μ, IntervalIntegrable (fun origin => f (origin,x)) volume 0 R)
    (G : X → ℝ) (hG : Integrable G μ)
    (hbound : ∀ᵐ x ∂μ, (∫ origin in (0:ℝ)..R, f (origin,x))/R ≤ G x) :
    Integrable f ((volume.restrict (Ioc 0 R)).prod μ) ∧
      IntervalIntegrable (fun origin => ∫ x, f (origin,x) ∂μ) volume 0 R ∧
      (∫ origin in (0:ℝ)..R, ∫ x, f (origin,x) ∂μ)/R ≤ ∫ x, G x ∂μ := by
  let ν := volume.restrict (Ioc 0 R)
  let H := fun x => ∫ origin, ‖f (origin,x)‖ ∂ν
  have hHeq (x : X) : H x = ∫ origin in (0:ℝ)..R, f (origin,x) := by
    dsimp only [H,ν]
    simp_rw [Real.norm_eq_abs,abs_of_nonneg (hf0 _)]
    rw [intervalIntegral.integral_of_le hR.le]
  have hHm : StronglyMeasurable H := hf.stronglyMeasurable.norm.integral_prod_left'
  have hHi : Integrable H μ := by
    apply (hG.const_mul R).mono' hHm.aestronglyMeasurable
    filter_upwards [hbound] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun origin => norm_nonneg (f (origin,x))))]
    change H x ≤ R*G x
    rw [hHeq]
    exact (div_le_iff₀ hR).mp hx |>.trans_eq (mul_comm _ _)
  have hprod : Integrable f (ν.prod μ) := by
    apply (integrable_prod_iff' hf.aestronglyMeasurable).mpr
    refine ⟨?_,hHi⟩
    filter_upwards [hfi] with x hx
    exact hx.1
  have hint : IntervalIntegrable (fun origin => ∫ x, f (origin,x) ∂μ) volume 0 R := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).mpr
    exact hprod.integral_prod_left
  refine ⟨hprod,hint,?_⟩
  have havg : Integrable (fun x => (∫ origin in (0:ℝ)..R, f (origin,x))/R) μ := by
    simp_rw [intervalIntegral.integral_of_le hR.le]
    exact hprod.integral_prod_right.div_const R
  have hswap := intervalIntegral_integral_swap
    (show Integrable (Function.uncurry (fun origin x => f (origin,x)))
      ((volume.restrict (uIoc 0 R)).prod μ) by
        rw [uIoc_of_le hR.le]
        apply hprod.congr
        filter_upwards [] with z
        rfl)
  rw [hswap,← integral_div]
  exact integral_mono_ae havg hG hbound

end LipschitzHilbert

end

end OAI
