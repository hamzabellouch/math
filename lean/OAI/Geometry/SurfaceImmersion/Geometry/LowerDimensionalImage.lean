import OAI.Geometry.SurfaceImmersion.Geometry.FiniteRegularFibers

namespace OAI

/-! The triple-radius exceptional set is null. Extend a map from two to
three coordinates constantly in the final coordinate and apply the proved
fixed-dimensional Jacobian null-image theorem. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace ClosedSurfaceR4.PublishedInputs

local instance tripleVolumeHaar : (volume : Measure (Plane × ℝ)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem smooth_surface_image_volume_zero (f : Plane → Plane × ℝ)
    (hf : ContDiff ℝ ∞ f) : volume (Set.range f) = 0 := by
  let g : Plane × ℝ → Plane × ℝ := fun x => f x.1
  have hg : ContDiff ℝ ∞ g := hf.comp contDiff_fst
  have hdet (x : Plane × ℝ) : LinearMap.det (fderiv ℝ g x).toLinearMap = 0 := by
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot, ne_eq, LinearMap.ker_eq_bot]
    intro hinj
    have hd : fderiv ℝ g x = (fderiv ℝ f x.1).comp (ContinuousLinearMap.fst ℝ Plane ℝ) := by
      change fderiv ℝ (f ∘ (Prod.fst : Plane × ℝ → Plane)) x = _
      rw [fderiv_comp x (hf.differentiable (by simp) x.1) differentiableAt_fst, fderiv_fst]
    have hzero : fderiv ℝ g x (0,1) = fderiv ℝ g x 0 := by
      rw [hd]
      simp
    have he := congrArg Prod.snd (hinj hzero)
    exact one_ne_zero he
  have hnull : volume (g '' (univ : Set (Plane × ℝ))) = 0 := by
    apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun x => fderiv ℝ g x)
    · intro x _
      exact (hg.differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt
    · intro x _
      exact hdet x
  have he : g '' (univ : Set (Plane × ℝ)) = Set.range f := by
    ext y
    constructor
    · rintro ⟨x,_,rfl⟩
      exact ⟨x.1,rfl⟩
    · rintro ⟨x,rfl⟩
      exact ⟨(x,0),mem_univ _,rfl⟩
  rwa [he] at hnull

/-- On a compact chart set, parameters avoiding a triple intersection form
an open dense set. -/
theorem compact_surface_image_open_dense (f : Plane → Plane × ℝ)
    (hf : ContDiff ℝ ∞ f) {K : Set Plane} (hK : IsCompact K) :
    IsOpen (f '' K)ᶜ ∧ Dense (f '' K)ᶜ := by
  refine ⟨(hK.image hf.continuous).isClosed.isOpen_compl,?_⟩
  have hnull : volume (f '' K) = 0 := measure_mono_null (image_subset_range _ _)
    (smooth_surface_image_volume_zero f hf)
  apply Measure.dense_of_ae (μ := (volume : Measure (Plane × ℝ)))
  simpa only [ae_iff,mem_compl_iff,not_not,Set.ofPred_mem_eq] using hnull

end ClosedSurfaceR4.PublishedInputs

end

end OAI
