import OAI.Geometry.SurfaceImmersion.Geometry.ScalarCriticalCurve

namespace OAI

/-! Nonflat critical scalar jets lie on regular level curves of a
first derivative; one-dimensional critical-value nullity applies. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
local instance nonflatFirstNormed : NormedAddCommGroup (Base →L[ℝ] ℝ) := inferInstance
local instance nonflatFirstSpace : NormedSpace ℝ (Base →L[ℝ] ℝ) := inferInstance
local instance nonflatSecondNormed : NormedAddCommGroup (Base →L[ℝ] Base →L[ℝ] ℝ) := inferInstance
local instance nonflatSecondSpace : NormedSpace ℝ (Base →L[ℝ] Base →L[ℝ] ℝ) := inferInstance

theorem scalar_nonflat_critical_image_null {f : Base → ℝ} (hf : ContDiff ℝ ∞ f) :
    volume (f '' {x | fderiv ℝ f x = 0 ∧ fderiv ℝ (fderiv ℝ f) x ≠ 0}) = 0 := by
  apply null_image_of_locally_null
  intro p hp
  have hD := hf.fderiv_right (m := ∞) (by simp)
  obtain ⟨v,hv⟩ := DFunLike.ne_iff.mp hp.2
  obtain ⟨w,hw⟩ := DFunLike.ne_iff.mp (show (fderiv ℝ (fderiv ℝ f) p) v ≠ 0 by simpa using hv)
  let g : Base → ℝ := fun x => fderiv ℝ f x w
  have hg : ContDiff ℝ ∞ g := hD.clm_apply contDiff_const
  have hdg : fderiv ℝ g p ≠ 0 := by
    intro hz
    have hd := ((hD.differentiable (by simp) p).hasFDerivAt.clm_apply
      (hasFDerivAt_const w p)).fderiv
    have he := congrArg (fun L : Base →L[ℝ] ℝ => L v) (hz.symm.trans hd)
    apply hw
    simpa only [add_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply,zero_apply,map_zero,add_zero,zero_add] using he.symm
  obtain ⟨U,hU,hpU,hn⟩ := scalar_critical_curve_local_null hf hg p hdg
  refine ⟨U,hU,hpU,measure_mono_null (image_mono ?_) hn⟩
  rintro x ⟨hx,hxU⟩
  exact ⟨⟨hx.1,by simp [g,hx.1]⟩,hxU⟩

theorem scalar_surface_critical_values_null {f : Base → ℝ} (hf : ContDiff ℝ ∞ f) :
    volume (f '' {x | fderiv ℝ f x = 0}) = 0 := by
  have hsub : {x | fderiv ℝ f x = 0} ⊆ scalarFlatTwo f ∪
      {x | fderiv ℝ f x = 0 ∧ fderiv ℝ (fderiv ℝ f) x ≠ 0} := by
    intro x hx
    by_cases h : fderiv ℝ (fderiv ℝ f) x = 0
    · exact Or.inl ⟨hx,h⟩
    · exact Or.inr ⟨hx,h⟩
  apply measure_mono_null (image_mono hsub)
  rw [image_union]
  exact measure_union_null (scalarFlatTwo_image_volume_zero hf)
    (scalar_nonflat_critical_image_null hf)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
