import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-! # Quantitative integral bounds used by backward recurrence -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter

/-- Cauchy--Schwarz against the constant function, proved directly by the
nonnegativity of variance. The measure need only have positive finite mass. -/
theorem sq_integral_le_mass_mul_integral_sq
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (hM : 0 < μ.real univ) (f : X → ℝ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ μ.real univ * ∫ x, f x ^ 2 ∂μ := by
  let M := μ.real univ
  let I := ∫ x, f x ∂μ
  let a := I / M
  have ha : a * M = I := div_mul_cancel₀ I hM.ne'
  have hi : Integrable (fun x => f x ^ 2 - (2 * a) * f x) μ :=
    hf2.sub (hf.const_mul _)
  have heq : (∫ x, (f x - a) ^ 2 ∂μ) =
      (∫ x, f x ^ 2 ∂μ) - (2 * a) * I + a ^ 2 * M := by
    calc
      _ = ∫ x, (f x ^ 2 - (2 * a) * f x) + a ^ 2 ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => by ring)
      _ = _ := by
        rw [integral_add hi (integrable_const _), integral_sub hf2 (hf.const_mul _),
          integral_const_mul, integral_const]
        simp only [smul_eq_mul, M, I]
        ring
  have hpos : 0 ≤ (∫ x, f x ^ 2 ∂μ) - (2 * a) * I + a ^ 2 * M := by
    rw [← heq]
    exact integral_nonneg (fun x => sq_nonneg (f x - a))
  have halg : M * ((∫ x, f x ^ 2 ∂μ) - (2 * a) * I + a ^ 2 * M) =
      M * (∫ x, f x ^ 2 ∂μ) - I ^ 2 := by
    calc
      _ = M * (∫ x, f x ^ 2 ∂μ) - 2 * (a * M) * I + (a * M) ^ 2 := by ring
      _ = _ := by rw [ha]; ring
  have hnonneg := mul_nonneg hM.le hpos
  rw [halg] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- A bounded transition function can carry a large integral only if its
superlevel set has large measure. -/
theorem integral_le_superlevel_mass_add
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, f x ∂μ) ≤ μ.real {x | t ≤ f x} + t * μ.real univ := by
  let S := {x | t ≤ f x}
  have hS : MeasurableSet S := measurableSet_le measurable_const hf
  have hfi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable 1
    (Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hbound x).1]
      exact (hbound x).2))
  have hI : Integrable (S.indicator (fun _ : X => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hS
  have hle : (∫ x, f x ∂μ) ≤ ∫ x, S.indicator (fun _ => (1 : ℝ)) x + t ∂μ := by
    apply integral_mono hfi (hI.add (integrable_const t))
    intro x
    change f x ≤ S.indicator (fun _ => (1 : ℝ)) x + t
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      linarith [(hbound x).2]
    · rw [indicator_of_notMem hx]
      have hn : ¬ t ≤ f x := hx
      simpa only [zero_add] using (lt_of_not_ge hn).le
  rw [integral_add hI (integrable_const t), integral_indicator_const (1 : ℝ) hS,
    integral_const] at hle
  simpa only [smul_eq_mul, mul_one, mul_comm _ t] using hle

end PolycyclicRecognition

end

end OAI
