import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.Basic

namespace OAI

/-! # Measure transport from a unit Jacobian

This is the change-of-variables step used by the nilpotent BCH chart.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem map_eq_self_of_unit_jacobian (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → E) (df : E → E →L[ℝ] E)
    (hdf : ∀ x, HasFDerivAt f (df x) x) (hf : Function.Bijective f)
    (hdet : ∀ x, (df x).det = 1) : Measure.map f μ = μ := by
  have hh := map_withDensity_abs_det_fderiv_eq_addHaar μ
    (s := univ) (MeasurableSet.univ : MeasurableSet (univ : Set E)).nullMeasurableSet
    (fun x _ => (hdf x).hasFDerivWithinAt) hf.injective.injOn
  have hdensity : (fun x => ENNReal.ofReal |(df x).det|) = fun _ => 1 := by
    funext x
    simp only [hdet x, abs_one, ENNReal.ofReal_one]
  rw [hdensity, Measure.restrict_univ, image_univ, hf.surjective.range_eq,
    Measure.restrict_univ] at hh
  have hone : μ.withDensity (fun _ : E => (1 : ℝ≥0∞)) = μ := withDensity_one
  rw [hone] at hh
  exact hh

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A homeomorphism transports additive Haar measure to Haar measure when
the conjugates of left translations preserve it. -/
theorem homeomorph_map_isHaar_of_translations
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    (c : E ≃ₜ G) (μ : Measure E) [μ.IsAddHaarMeasure]
    (htranslations : ∀ g : G,
      Measure.map (fun x => c.symm (g * c x)) μ = μ) :
    (Measure.map c μ).IsHaarMeasure := by
  refine
    { map_mul_left_eq_self := ?_
      toIsFiniteMeasureOnCompacts := Measure.IsFiniteMeasureOnCompacts.map μ c
      toIsOpenPosMeasure := c.continuous.isOpenPosMeasure_map c.surjective }
  intro g
  have hleft : Measurable (fun x : G => g * x) :=
    (continuous_const.mul continuous_id).measurable
  rw [Measure.map_map hleft c.measurable]
  have heq : (fun y : G => g * y) ∘ c = c ∘ (fun x => c.symm (g * c x)) := by
    funext x
    simp only [Function.comp_apply, c.apply_symm_apply]
  have htrans : Measurable (fun x : E => c.symm (g * c x)) :=
    (c.symm.continuous.comp (continuous_const.mul c.continuous)).measurable
  rw [heq, ← Measure.map_map c.measurable htrans, htranslations]

end PolycyclicRecognition

end

end OAI
