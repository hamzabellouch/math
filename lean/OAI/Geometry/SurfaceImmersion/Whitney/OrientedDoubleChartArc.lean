import OAI.Geometry.SurfaceImmersion.Whitney.OrientedChartArc
import OAI.Geometry.SurfaceImmersion.Whitney.SmoothCompactArc

namespace OAI

/-! Actual smooth regular embedded arc pieces in the double locus,
with the image and endpoint order of the original topological arc. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
namespace SmoothDoubleChart
variable {f : M → ProjectionTarget 3}

theorem oriented_arc (c : SmoothDoubleChart f) {γ : ℝ → surfaceDoublePairs f}
    {a b : ℝ} (hab : a < b) (hγ : ContinuousOn γ (Icc a b))
    (hinj : InjOn γ (Icc a b)) (hsource : MapsTo γ (Icc a b) c.coord.source) :
    ∃ (P : SmoothCompactArc (planeModel.prod planeModel) (M × M)) (s : ℝ),
      (s = 1 ∨ s = -1) ∧
      P.curve = (fun t => (c.coord.symm (s*t)).val) ∧
      P.start = s*c.coord (γ a) ∧ P.finish = s*c.coord (γ b) ∧
      P.curve '' Icc P.start P.finish = (fun t => (γ t).val) '' Icc a b ∧
      P.curve P.start = (γ a).val ∧ P.curve P.finish = (γ b).val := by
  obtain ⟨s,hs,hab',htarget,himage,hi,hleft,hright⟩ :=
    oriented_chart_arc c.coord hab hγ hinj hsource
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  let V : Set ℝ := (fun t : ℝ => s*t) ⁻¹' c.coord.target
  have hV : IsOpen V := c.coord.open_target.preimage (continuous_const.mul continuous_id)
  have hVsub : Icc (s*c.coord (γ a)) (s*c.coord (γ b)) ⊆ V := htarget
  have hlin : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun t : ℝ => s*t) :=
    (contDiff_const.mul contDiff_id).contMDiff
  have hA : ContMDiffOn 𝓘(ℝ) planeModel ∞
      (fun t => (c.coord.symm (s*t)).val.1) V :=
    c.inverse_left_smooth.comp hlin.contMDiffOn (fun _ ht => ht)
  have hB : ContMDiffOn 𝓘(ℝ) planeModel ∞
      (fun t => (c.coord.symm (s*t)).val.2) V :=
    c.inverse_right_smooth.comp hlin.contMDiffOn (fun _ ht => ht)
  have hregular : ∀ t ∈ V, Function.Injective
      (mfderiv 𝓘(ℝ) (planeModel.prod planeModel) (fun t => (c.coord.symm (s*t)).val) t) := by
    intro t ht
    have hAt := c.inverse_left_smooth.contMDiffAt (c.coord.open_target.mem_nhds ht)
    have hBt := c.inverse_right_smooth.contMDiffAt (c.coord.open_target.mem_nhds ht)
    have hDt := hlin.mdifferentiable (by simp) t
    let e := Homeomorph.mulLeft₀ s hs0
    have hei : ContDiff ℝ ∞ e.symm := by
      change ContDiff ℝ ∞ (fun t : ℝ => s⁻¹*t)
      exact contDiff_const.mul contDiff_id
    have he : e.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ) 𝓘(ℝ) :=
      ⟨hlin.mdifferentiable (by simp) |>.mdifferentiableOn,
        hei.contMDiff.mdifferentiable (by simp) |>.mdifferentiableOn⟩
    have hD : Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ) (fun t : ℝ => s*t) t) :=
      he.mfderiv_injective (mem_univ t)
    have hdA := (hAt.mdifferentiableAt (by simp)).hasMFDerivAt.comp t hDt.hasMFDerivAt
    have hdB := (hBt.mdifferentiableAt (by simp)).hasMFDerivAt.comp t hDt.hasMFDerivAt
    have hd := (hdA.prodMk hdB).mfderiv
    have hj : Function.Injective
        (((mfderiv 𝓘(ℝ) planeModel (fun t => (c.coord.symm t).val.1) (s*t)).comp
            (mfderiv 𝓘(ℝ) 𝓘(ℝ) (fun t : ℝ => s*t) t)).prod
          ((mfderiv 𝓘(ℝ) planeModel (fun t => (c.coord.symm t).val.2) (s*t)).comp
            (mfderiv 𝓘(ℝ) 𝓘(ℝ) (fun t : ℝ => s*t) t))) := by
      intro x y hxy
      apply hD
      exact c.inverse_regular (s*t) ht hxy
    exact hd.symm ▸ hj
  let P : SmoothCompactArc (planeModel.prod planeModel) (M × M) :=
    ⟨_,s*c.coord (γ a),s*c.coord (γ b),hab',V,hV,hVsub,
      hA.prodMk hB,hregular,fun _ hx _ hy he => hi hx hy (Subtype.val_injective he)⟩
  refine ⟨P,s,hs,rfl,rfl,rfl,?_,?_,?_⟩
  · change (Subtype.val ∘ (fun t => c.coord.symm (s*t))) ''
      Icc (s*c.coord (γ a)) (s*c.coord (γ b)) = (Subtype.val ∘ γ) '' Icc a b
    rw [Set.image_comp,himage,← Set.image_comp]
  · exact congrArg Subtype.val hleft
  · exact congrArg Subtype.val hright

end SmoothDoubleChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
