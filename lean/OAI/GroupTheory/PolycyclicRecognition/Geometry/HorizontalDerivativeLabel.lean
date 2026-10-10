import OAI.GroupTheory.PolycyclicRecognition.Geometry.ProfileDerivativeLabel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SegmentVolumeDerivative
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SegmentIncrementDerivative

namespace OAI

/-! # The two segment inequalities determine the horizontal derivative label -/

noncomputable section

namespace PolycyclicRecognition

open Set

/-- Once the actual line derivatives define a linear horizontal map, the two
segment inequalities force it to be one finite support-symmetry label after
projection to height. No derivative-level inequalities are assumed. -/
theorem horizontal_derivative_eq_support_symmetry
    {V W I B J : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [Fintype I] [Fintype B] [Nonempty B] [Finite J]
    (D : SupportDatum W I B) (π M : V →ₗ[ℝ] W) (hπ : Function.Surjective π)
    (A : J → linearSupportSymmetryGroup D)
    (curve : V → ℝ → W) (hcurve : ∀ v, Continuous (curve v))
    (hderiv : ∀ v, HasDerivAt (curve v) (M v) 0)
    (T₀ : V → ℝ) (hT₀ : ∀ v, 0 < T₀ v)
    (hinc : ∀ v t, 0 < t → t < T₀ v →
      t⁻¹ • (curve v t - curve v 0) ∈ convexHull ℝ (range fun j => (A j).val (π v)))
    (hvolume : ∀ v t, 0 < t → t < T₀ v →
      t * D.segmentSupport (π v) ≤ D.templateSupport (curve v '' Icc 0 t)) :
    ∃ T : linearSupportSymmetryGroup D, M = T.val.toLinearMap.comp π := by
  apply derivative_eq_support_symmetry D π M hπ A
  · intro v
    apply derivative_mem_of_short_increments (curve v) (M v) (hderiv v)
      (convexHull ℝ (range fun j => (A j).val (π v)))
      ((Set.finite_range (fun j => (A j).val (π v))).isClosed_convexHull (𝕜 := ℝ)) (hT₀ v)
    exact hinc v
  · intro v
    exact D.le_segmentSupport_derivative (curve v) (hcurve v) (M v) (hderiv v)
      (D.segmentSupport (π v)) (hT₀ v) (hvolume v)

/-- The derivative belongs to the original finite family of labels, rather
than just its containing segment-norm isometry group. -/
theorem horizontal_derivative_eq_one_of_labels
    {V W I B J : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [Fintype I] [Fintype B] [Nonempty B] [Finite J]
    (D : SupportDatum W I B) (π M : V →ₗ[ℝ] W) (hπ : Function.Surjective π)
    (A : J → linearSupportSymmetryGroup D)
    (curve : V → ℝ → W) (hcurve : ∀ v, Continuous (curve v))
    (hderiv : ∀ v, HasDerivAt (curve v) (M v) 0)
    (T₀ : V → ℝ) (hT₀ : ∀ v, 0 < T₀ v)
    (hinc : ∀ v t, 0 < t → t < T₀ v →
      t⁻¹ • (curve v t - curve v 0) ∈ convexHull ℝ (range fun j => (A j).val (π v)))
    (hvolume : ∀ v t, 0 < t → t < T₀ v →
      t * D.segmentSupport (π v) ≤ D.templateSupport (curve v '' Icc 0 t)) :
    ∃ j, M = (A j).val.toLinearMap.comp π := by
  apply derivative_eq_one_of_labels D π M hπ A
  · intro v
    exact derivative_mem_of_short_increments (curve v) (M v) (hderiv v)
      (convexHull ℝ (range fun j => (A j).val (π v)))
      ((Set.finite_range (fun j => (A j).val (π v))).isClosed_convexHull (𝕜 := ℝ))
      (hT₀ v) (hinc v)
  · intro v
    exact D.le_segmentSupport_derivative (curve v) (hcurve v) (M v) (hderiv v)
      (D.segmentSupport (π v)) (hT₀ v) (hvolume v)

/-- Specialization to the manuscript's template-preserving labels. -/
theorem horizontal_derivative_eq_one_of_template_labels
    {V W I B J : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [Fintype I] [Fintype B] [Nonempty B] [Finite J]
    (D : SupportDatum W I B) (π M : V →ₗ[ℝ] W) (hπ : Function.Surjective π)
    (A : J → templateSymmetryGroup D)
    (curve : V → ℝ → W) (hcurve : ∀ v, Continuous (curve v))
    (hderiv : ∀ v, HasDerivAt (curve v) (M v) 0)
    (T₀ : V → ℝ) (hT₀ : ∀ v, 0 < T₀ v)
    (hinc : ∀ v t, 0 < t → t < T₀ v →
      t⁻¹ • (curve v t - curve v 0) ∈ convexHull ℝ (range fun j => (A j).val (π v)))
    (hvolume : ∀ v t, 0 < t → t < T₀ v →
      t * D.segmentSupport (π v) ≤ D.templateSupport (curve v '' Icc 0 t)) :
    ∃ j, M = (A j).val.toLinearMap.comp π := by
  exact horizontal_derivative_eq_one_of_labels D π M hπ
    (fun j => ⟨(A j).val, templateSymmetry_mem_linearSupportSymmetry D (A j)⟩)
    curve hcurve hderiv T₀ hT₀ hinc hvolume

end PolycyclicRecognition

end

end OAI
