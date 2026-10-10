import OAI.Geometry.RCD.Transport.RelativeEntropyRemainder

namespace OAI

/-! # Integral control of the entropy remainder and its tangent -/

open Set Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates

theorem relative_entropy_tangent_bound {r v B : ℝ} (hr : 0≤r)
    (hv : |v|≤B*r) : |(1+Real.log r)*v|≤B*(r+|r*Real.log r|) := by
  rw [abs_mul]
  calc
    _ ≤ (1+|Real.log r|)*(B*r) :=
      mul_le_mul (by simpa only [abs_one] using abs_add_le (1:ℝ) (Real.log r)) hv
        (abs_nonneg _) (by positivity)
    _ = _ := by rw [abs_mul,abs_of_nonneg hr]; ring

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem relative_entropy_tangent_integrable {r v : X → ℝ} {B : ℝ}
    (hr : Measurable r) (hv : Measurable v) (hr0 : ∀ᵐ x ∂μ, 0≤r x)
    (hri : Integrable r μ) (hent : Integrable (fun x => r x*Real.log (r x)) μ)
    (hb : ∀ᵐ x ∂μ, |v x|≤B*r x) :
    Integrable (fun x => (1+Real.log (r x))*v x) μ := by
  apply ((hri.add hent.abs).const_mul B).mono' ((measurable_const.add hr.log).mul hv).aestronglyMeasurable
  filter_upwards [hr0,hb] with x hx hb
  simpa only [Pi.add_apply,Pi.mul_apply,Real.norm_eq_abs] using relative_entropy_tangent_bound hx hb

theorem relative_entropy_integral_remainder {r v f : X → ℝ} {ε δ B C t : ℝ}
    (hr : Measurable r) (hv : Measurable v) (hr0 : ∀ᵐ x ∂μ, 0≤r x)
    (hf0 : ∀ᵐ x ∂μ, 0≤f x) (hε : 0≤ε)
    (hri : Integrable r μ) (hent : Integrable (fun x => r x*Real.log (r x)) μ)
    (hfi : Integrable (fun x => f x*Real.log (f x)) μ)
    (hb : ∀ᵐ x ∂μ, |v x|≤B*r x)
    (he : ∀ᵐ x ∂μ, |f x-r x-t*v x|≤C*t^2*r x)
    (hunit : ∀ y : ℝ, |y-1|<δ → |y*Real.log y-(y-1)|≤ε*|y-1|)
    (ht : B*|t|+C*t^2<δ) :
    |(∫ x, f x*Real.log (f x) ∂μ)-(∫ x, r x*Real.log (r x) ∂μ)-
      t*(∫ x, (1+Real.log (r x))*v x ∂μ)| ≤
      (ε*(B*|t|+C*t^2)+C*t^2)*(∫ x, r x ∂μ)+
        C*t^2*(∫ x, |r x*Real.log (r x)| ∂μ) := by
  have hvi := relative_entropy_tangent_integrable μ hr hv hr0 hri hent hb
  have hbound : ∀ᵐ x ∂μ,
      |f x*Real.log (f x)-r x*Real.log (r x)-t*((1+Real.log (r x))*v x)|≤
      (ε*(B*|t|+C*t^2)+C*t^2)*r x+C*t^2*|r x*Real.log (r x)| := by
    filter_upwards [hr0,hf0,hb,he] with x hx hf hb he
    rcases eq_or_lt_of_le hx with hz | hp
    · have hv0 : v x=0 := by
        rw [←hz,mul_zero] at hb
        exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
      have hf0 : f x=0 := by
        rw [←hz,hv0,mul_zero,sub_zero,sub_zero,mul_zero] at he
        exact abs_eq_zero.mp (le_antisymm he (abs_nonneg _))
      simp only [←hz,hv0,hf0,zero_mul,mul_zero,sub_zero,abs_zero,add_zero]
      exact le_rfl
    · exact relative_entropy_remainder hε hp hf hunit hb he ht
  have hAi : Integrable (fun x => f x*Real.log (f x)-r x*Real.log (r x)) μ := hfi.sub hent
  have hBi : Integrable (fun x => t*((1+Real.log (r x))*v x)) μ := hvi.const_mul t
  have hrem : Integrable (fun x => f x*Real.log (f x)-r x*Real.log (r x)-
      t*((1+Real.log (r x))*v x)) μ := hAi.sub hBi
  calc
    _ = |∫ x, f x*Real.log (f x)-r x*Real.log (r x)-t*((1+Real.log (r x))*v x) ∂μ| := by
      rw [integral_sub hAi hBi,integral_sub hfi hent,integral_const_mul]
    _ ≤ ∫ x, |f x*Real.log (f x)-r x*Real.log (r x)-t*((1+Real.log (r x))*v x)| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, (ε*(B*|t|+C*t^2)+C*t^2)*r x+C*t^2*|r x*Real.log (r x)| ∂μ :=
      integral_mono_ae hrem.abs ((hri.const_mul _).add (hent.abs.const_mul _)) hbound
    _ = _ := by rw [integral_add (hri.const_mul _) (hent.abs.const_mul _),integral_const_mul,integral_const_mul]

end RegularPointCoordinates

end

end OAI
