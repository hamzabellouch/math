import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real

namespace OAI

/-! # Positive mass on quantitatively large sections

This is the finite-measure Fubini estimate used to iterate one-dimensional
polynomial bounds. It concerns an arbitrary measurable set in a product.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem exists_large_sections (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha : 0 < (μ univ).toReal) (hb : 0 < (ν univ).toReal)
    (S : Set (X × Y)) (hS : MeasurableSet S)
    (hm : 0 < (μ.prod ν S).toReal) :
    ∃ A : Set X, MeasurableSet A ∧
      (μ.prod ν S).toReal / (2 * (ν univ).toReal) ≤ (μ A).toReal ∧
      ∀ x ∈ A,
        (μ.prod ν S).toReal / (2 * (μ univ).toReal) ≤
          (ν (Prod.mk x ⁻¹' S)).toReal := by
  let m := (μ.prod ν S).toReal
  let a := (μ univ).toReal
  let b := (ν univ).toReal
  let c := m / (2 * a)
  let f : X → ℝ := fun x => (ν (Prod.mk x ⁻¹' S)).toReal
  have hc : 0 < c := div_pos hm (mul_pos (by norm_num) ha)
  have hfm : Measurable f := (measurable_measure_prodMk_left hS).ennreal_toReal
  have hf0 (x : X) : 0 ≤ f x := ENNReal.toReal_nonneg
  have hfb (x : X) : f x ≤ b :=
    ENNReal.toReal_mono (measure_ne_top ν univ) (measure_mono (subset_univ _))
  have hfi : Integrable f μ := (integrable_const b).mono' hfm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 x)] using hfb x))
  have hint : ∫ x, f x ∂μ = m := by
    change (∫ x, (ν (Prod.mk x ⁻¹' S)).toReal ∂μ) = (μ.prod ν S).toReal
    rw [Measure.prod_apply hS]
    exact integral_toReal (measurable_measure_prodMk_left hS).aemeasurable
      (Filter.Eventually.of_forall (fun x => measure_lt_top ν _))
  let A := {x | c ≤ f x}
  have hA : MeasurableSet A := measurableSet_le measurable_const hfm
  have hgi : Integrable (fun x => c + A.indicator (fun _ => b) x) μ :=
    (integrable_const c).add ((integrable_const b).indicator hA)
  have hbound (x : X) : f x ≤ c + A.indicator (fun _ => b) x := by
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx]
      linarith [hfb x]
    · rw [indicator_of_notMem hx, add_zero]
      exact (lt_of_not_ge hx).le
  have hi := integral_mono hfi hgi hbound
  rw [hint, integral_add (integrable_const c) ((integrable_const b).indicator hA),
    integral_const, integral_indicator hA, setIntegral_const] at hi
  simp only [smul_eq_mul, measureReal_def] at hi
  have hca : c * a = m / 2 := by
    dsimp [c]
    field_simp [show a ≠ 0 from ne_of_gt ha]
  change m ≤ a * c + (μ A).toReal * b at hi
  rw [mul_comm a c, hca] at hi
  refine ⟨A, hA, ?_, fun x hx => hx⟩
  apply (div_le_iff₀ (mul_pos (by norm_num) hb)).2
  nlinarith

end PolycyclicRecognition

end

end OAI
