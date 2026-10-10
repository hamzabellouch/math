import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-! # A tail moment controls the total quadratic moment -/

open Set Filter MeasureTheory Metric
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} {f : X → ℝ}

theorem weighted_moment_le_of_tail (p : X) (R : ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (hf : Integrable f μ)
    (hw : Integrable (fun x => f x*(1+(dist x p)^2)) μ)
    (ht : (∫ x in (ball p R)ᶜ, f x*(dist x p)^2 ∂μ) ≤ 1) :
    (∫ x, f x*(1+(dist x p)^2) ∂μ) ≤ (1+R^2)*(∫ x, f x ∂μ)+1 := by
  have hsq : Integrable (fun x => f x*(dist x p)^2) μ := by
    have hm : AEStronglyMeasurable (fun x => f x*(dist x p)^2) μ :=
      (hw.aestronglyMeasurable.sub hf.aestronglyMeasurable).congr
        (Eventually.of_forall (fun x => by dsimp only [Pi.sub_apply,Pi.add_apply]; ring))
    apply hw.mono' hm
    apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hf0 x) (sq_nonneg _))]
    nlinarith [hf0 x]
  have hind := hsq.indicator (s := (ball p R)ᶜ) measurableSet_ball.compl
  have hpoint (x : X) : f x*(dist x p)^2 ≤ R^2*f x+
      (ball p R)ᶜ.indicator (fun y => f y*(dist y p)^2) x := by
    by_cases hx : x ∈ ball p R
    · rw [indicator_of_notMem (show x ∉ (ball p R)ᶜ by simpa using hx)]
      have hd : dist x p < R := mem_ball.mp hx
      have hh : (dist x p)^2 ≤ R^2 := pow_le_pow_left₀ dist_nonneg hd.le 2
      nlinarith [mul_le_mul_of_nonneg_left hh (hf0 x)]
    · rw [indicator_of_mem hx]
      nlinarith [mul_nonneg (sq_nonneg R) (hf0 x)]
  have hb := integral_mono hsq ((hf.const_mul (R^2)).add hind) hpoint
  simp only [Pi.add_apply] at hb
  rw [integral_add (hf.const_mul (R^2)) hind,integral_const_mul,
    integral_indicator measurableSet_ball.compl] at hb
  have he : (∫ x, f x*(1+(dist x p)^2) ∂μ) =
      (∫ x, f x ∂μ)+(∫ x, f x*(dist x p)^2 ∂μ) := by
    rw [← integral_add hf hsq]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by dsimp only [Pi.sub_apply,Pi.add_apply]; ring)
  rw [he]
  nlinarith

end RegularPointCoordinates

end

end OAI
