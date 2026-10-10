import OAI.Geometry.RCD.Sobolev.PositiveEnergyExcess

namespace OAI

/-! # A bounded L1 error controls the positive L2 tail -/

open Set MeasureTheory
noncomputable section
namespace RegularPointCoordinates

theorem bounded_positive_tail_pointwise {a B : ℝ} (hB : 0 ≤ B) (ha : a ≤ B) :
    (max (a-1) 0)^2 ≤ B*|a-1| := by
  by_cases h : a ≤ 1
  · rw [max_eq_right (by linarith)]
    simpa using mul_nonneg hB (abs_nonneg (a-1))
  · rw [max_eq_left (by linarith), abs_of_nonneg (by linarith)]
    nlinarith

theorem bounded_positive_tail_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Set X) {f : X → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hf : AEStronglyMeasurable f (μ.restrict S))
    (hi : IntegrableOn (fun x => |f x-1|) S μ)
    (hb : ∀ᵐ x ∂μ.restrict S, f x ≤ B) :
    (∫ x in S, (max (f x-1) 0)^2 ∂μ) ≤ B*(∫ x in S, |f x-1| ∂μ) := by
  have hmeas : AEStronglyMeasurable (fun x => (max (f x-1) 0)^2) (μ.restrict S) := by
    exact (((hf.sub aestronglyMeasurable_const).sup aestronglyMeasurable_const).pow 2)
  have hdom := hb.mono fun x hx => bounded_positive_tail_pointwise hB hx
  have hint : IntegrableOn (fun x => (max (f x-1) 0)^2) S μ :=
    (hi.const_mul B).mono' hmeas (hdom.mono fun x hx => by
      simpa only [Real.norm_eq_abs, abs_sq] using hx)
  calc
    _ ≤ ∫ x in S, B*|f x-1| ∂μ := integral_mono_ae hint (hi.const_mul B) hdom
    _ = _ := integral_const_mul _ _

end RegularPointCoordinates

end

end OAI
