import OAI.Geometry.SurfaceImmersion.Atlas.RegularCoordinateSard
import OAI.Geometry.SurfaceImmersion.Atlas.TargetCoordinateChoice
import OAI.Geometry.SurfaceImmersion.Geometry.LinearEquivNullImage

namespace OAI

/-! The single dimension-reduction step needed to pass from the proved
scalar surface Sard statement to the three- and four-dimensional pair
charts. All hypotheses of the lower-dimensional statement are explicit. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E H F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
  [MeasureSpace G] [BorelSpace G] [Measure.IsAddHaarMeasure (volume : Measure G)]

theorem sard_dimension_step
    (hdomain : Module.finrank ℝ E = Module.finrank ℝ H + 1)
    (htarget : Module.finrank ℝ F = Module.finrank ℝ G + 1)
    (hsmall : (Module.finrank ℝ E : ℝ≥0∞)/2 < Module.finrank ℝ F)
    (hsard : ∀ (g : H → G) (V : Set H), IsOpen V → ContDiffOn ℝ ∞ g V →
      volume (g '' {x | x ∈ V ∧ ¬ Function.Surjective (fderiv ℝ g x)}) = 0)
    {f : E → F} (hf : ContDiff ℝ ∞ f) :
    volume (f '' {x | ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  let C : Set E := {x | ¬ Function.Surjective (fderiv ℝ f x) ∧ fderiv ℝ f x ≠ 0}
  have hC : volume (f '' C) = 0 := by
    apply null_image_of_locally_null
    intro p hp
    obtain ⟨e,he⟩ := target_coordinate_choice htarget (fderiv ℝ f p) hp.2
    let g : E → ℝ × G := e ∘ f
    have hg : ContDiff ℝ ∞ g := e.contDiff.comp hf
    have hd (x : E) : fderiv ℝ g x = e.toContinuousLinearMap.comp (fderiv ℝ f x) :=
      (e.hasFDerivAt.comp x (hf.differentiable (by simp) x).hasFDerivAt).fderiv
    have hgp : fderiv ℝ (fun x => (g x).1) p ≠ 0 := by
      rw [fderiv.fst (hg.differentiable (by simp) p),hd]
      exact he
    obtain ⟨U,hU,hpU,hnull⟩ := regular_coordinate_critical_local_null hdomain hsard hg p hgp
    have hbad (x : E) (hx : ¬ Function.Surjective (fderiv ℝ f x)) :
        ¬ Function.Surjective (fderiv ℝ g x) := by
      intro hs
      apply hx
      intro y
      obtain ⟨v,hv⟩ := hs (e y)
      rw [hd] at hv
      exact ⟨v,e.injective hv⟩
    have him : volume (e '' (f '' (C ∩ U))) = 0 := by
      apply measure_mono_null _ hnull
      rintro y ⟨z,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨x,⟨hbad x hx.1.1,hx.2⟩,rfl⟩
    refine ⟨U,hU,hpU,?_⟩
    let : Measure.IsAddHaarMeasure (volume : Measure (ℝ × G)) := by
      change Measure.IsAddHaarMeasure ((volume : Measure ℝ).prod (volume : Measure G))
      exact Measure.prod.instIsAddHaarMeasure _ _
    have hh := linear_equiv_null_image e.symm (volume : Measure (ℝ × G)) (volume : Measure F) him
    simpa only [e.symm_image_image] using hh
  have hzero := flat_first_image_null volume hf hsmall
  apply measure_mono_null (image_mono (show {x | ¬ Function.Surjective (fderiv ℝ f x)} ⊆
      {x | fderiv ℝ f x = 0} ∪ C from ?_))
  · rw [image_union]
    exact measure_union_null hzero hC
  · intro x hx
    by_cases h : fderiv ℝ f x = 0
    · exact Or.inl h
    · exact Or.inr ⟨hx,h⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
