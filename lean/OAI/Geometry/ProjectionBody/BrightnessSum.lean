import OAI.Geometry.ProjectionBody.FacetMeasure
import OAI.Geometry.ProjectionBody.Arithmetic
import Mathlib.Basic.ENNReal.BigOperators

namespace OAI

noncomputable section
open Set MeasureTheory

namespace ProjectionCounterexample

variable {ι V W : Type*} [Fintype ι]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [MeasurableSpace W]

/-- Convert the genuine facet-measure sum to the balanced absolute-slope formula.
Every geometric input, including each projected facet measure, remains explicit. -/
theorem real_measure_image_halfspaceBody
    (a : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ) (q : V →ₗ[ℝ] W) (μ : Measure W)
    {u : V} (hqu : q u = 0) (hu : ∃ i, 0 < a i u)
    (hker : LinearMap.ker q = Submodule.span ℝ {u})
    (hmeas : ∀ i, MeasurableSet (q '' boundingFace a b i))
    (hnull : ∀ i j, i ≠ j →
      μ (q '' (boundingFace a b i ∩ boundingFace a b j)) = 0)
    (c : ℝ) (hc : 0 ≤ c) (hbalance : ∑ i, a i u = 0)
    (hfacet : ∀ i, μ (q '' boundingFace a b i) = ENNReal.ofReal (c * |a i u|)) :
    (μ (q '' halfspaceBody a b)).toReal = c * (∑ i, |a i u|) / 2 := by
  classical
  rw [measure_image_halfspaceBody_eq_sum_visible a b q μ hqu hu hker hmeas hnull]
  simp_rw [hfacet]
  rw [ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
  simp_rw [ENNReal.toReal_ofReal (mul_nonneg hc (abs_nonneg _))]
  have hs : (∑ i : {i : ι // 0 < a i u}, |a i.1 u|) =
      (∑ i with 0 < a i u, a i u) := by
    calc
      (∑ i : {i : ι // 0 < a i u}, |a i.1 u|) =
          ∑ i : {i : ι // 0 < a i u}, a i.1 u := by
        apply Finset.sum_congr rfl
        intro i _
        exact abs_of_pos i.2
      _ = _ := (Finset.sum_subtype _ (by simp) (fun i => a i u)).symm
  rw [← Finset.mul_sum, hs, sum_positive_eq_half_sum_abs _ hbalance, mul_div_assoc]

end ProjectionCounterexample

end

end OAI
