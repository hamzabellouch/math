import OAI.Geometry.SurfaceImmersion.Geometry.FiniteRegularFibers

namespace OAI

/-! Compact-chart regular-value conditions are open as well as dense.
This permits independent radius parameters in a finite product. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace ClosedSurfaceR4.PublishedInputs

def compactRegularValues (f : Plane → Plane) (K : Set Plane) : Set Plane :=
  {y | ∀ x ∈ K, f x = y → Function.Surjective (fderiv ℝ f x)}

theorem compact_regular_values_open_dense (f : Plane → Plane)
    (hf : ContDiff ℝ ∞ f) {K : Set Plane} (hK : IsCompact K) :
    IsOpen (compactRegularValues f K) ∧ Dense (compactRegularValues f K) := by
  let C : Set Plane := {x | ¬ Function.Surjective (fderiv ℝ f x)}
  have heq : C = {x | (fderiv ℝ f x).det = 0} := by
    ext x
    change (¬ Function.Surjective (fderiv ℝ f x)) ↔
      LinearMap.det (fderiv ℝ f x).toLinearMap = 0
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot, ne_eq, LinearMap.ker_eq_bot]
    exact not_congr LinearMap.injective_iff_surjective.symm
  have hC : IsClosed C := by
    rw [heq]
    exact isClosed_eq (ContinuousLinearMap.continuous_det.comp
      (hf.continuous_fderiv (by simp))) continuous_const
  have hbad : IsCompact (f '' (K ∩ C)) := (hK.inter_right hC).image hf.continuous
  have hvalues : compactRegularValues f K = (f '' (K ∩ C))ᶜ := by
    ext y
    simp only [compactRegularValues,mem_ofPred_eq,mem_compl_iff,mem_image,mem_inter_iff,C]
    constructor
    · intro hy ⟨x,⟨hx,hc⟩,hxy⟩
      exact hc (hy x hx hxy)
    · intro hy x hx hxy
      by_contra hc
      exact hy ⟨x,⟨hx,hc⟩,hxy⟩
  rw [hvalues]
  refine ⟨hbad.isClosed.isOpen_compl,?_⟩
  have hnull : volume (f '' (K ∩ C)) = 0 :=
    measure_mono_null (image_mono inter_subset_right) (sardSurfaceInput f hf)
  apply Measure.dense_of_ae (μ := (volume : Measure Plane))
  simpa only [ae_iff,mem_compl_iff,not_not,Set.ofPred_mem_eq] using hnull

end ClosedSurfaceR4.PublishedInputs

end

end OAI
