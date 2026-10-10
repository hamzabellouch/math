import Mathlib
import OAI.Geometry.WeakMTW.Variations.ActionHessian
import OAI.Geometry.WeakMTW.Variations.ParametricTaylor

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem cost_geodesic_first_limit (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) (ξ : TangentSpace (model n) x)
    {z : ℕ → M} (hz : Tendsto z atTop (𝓝 (exp x v)))
    {l : ℕ → ℝ} (hl : Tendsto l atTop (𝓝 0)) (hne : ∀ᶠ j in atTop, l j ≠ 0) :
    Tendsto (fun j => (cost (exp x (l j•ξ)) (z j) - cost x (z j)) / l j)
      atTop (𝓝 (-inner ℝ v ξ)) := by
  let c := chartAt (Model n) x
  let d := chartAt (Model n) (exp x v)
  let f : Model n × Model n → ℝ := fun q => cost (c.symm q.1) (d.symm q.2)
  let a := c x
  let b := d (exp x v)
  have hx : x ∈ c.source := mem_chart_source (Model n) x
  have hy : exp x v ∈ d.source := mem_chart_source (Model n) (exp x v)
  have hf : ContDiffAt ℝ ∞ f (a,b) := cost_coord_smooth_interior x hv
  have hd := (d.continuousAt hy).tendsto.comp hz
  have hexp_eq (t : ℝ) : exp x (t•ξ) = geodesic (⟨x,ξ⟩ : TangentBundle (model n) M) t :=
    exp_mul_eq_geodesic (⟨x,ξ⟩ : TangentBundle (model n) M) t
  let C : ℝ → Model n := fun t => c (geodesic (⟨x,ξ⟩ : TangentBundle (model n) M) t)
  have hCzero : C 0 = a := by simp [C,a,geodesic_zero]
  have hCd : HasDerivAt C (tangentChartLinear x ξ) 0 := by
    have hh := (geodesic_coordinate_equation_zero x
      (⟨x,ξ⟩ : TangentBundle (model n) M) hx).fst
    change HasDerivAt C ((stateChart x (⟨x,ξ⟩ : TangentBundle (model n) M)).2) 0 at hh
    rwa [← tangentChartLinear_eq] at hh
  have hl' : Tendsto l atTop (𝓝[≠] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hl,by simpa only [mem_compl_iff,mem_singleton_iff] using hne⟩
  have hdir : Tendsto (fun j => (l j)⁻¹•(C (l j)-a)) atTop (𝓝 (tangentChartLinear x ξ)) := by
    simpa only [zero_add,hCzero,Function.comp_def] using hCd.tendsto_slope_zero.comp hl'
  have hlim := MovingTaylor.param_first_limit hf (tendsto_const_nhds (x := a))
    hdir hd hl hne
  have hs : (fun q : Model n => f (q,b)) = initialCost x (exp x v) := by
    funext q
    simp only [f,b,d.left_inv hy,initialCost,c]
  have hg : HasFDerivAt f (fderiv ℝ f (a,b)) (a,b) :=
    (hf.differentiableAt (by simp)).hasFDerivAt
  have hpair : HasFDerivAt (fun q : Model n => (q,b))
      ((ContinuousLinearMap.id ℝ (Model n)).prod 0) a :=
    (hasFDerivAt_id a).prodMk (hasFDerivAt_const b a)
  have hg' := hg.comp a hpair
  have hgd := hg'.fderiv
  rw [show (f ∘ fun q => (q,b)) = initialCost x (exp x v) from hs] at hgd
  have hder : fderiv ℝ f (a,b) (tangentChartLinear x ξ,0) = -inner ℝ v ξ := by
    have h := congrArg (fun L : Model n →L[ℝ] ℝ => L (tangentChartLinear x ξ)) hgd
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply,zero_apply] at h
    rw [(initialCost_geometry x hv).2.1] at h
    have hm : metric x (chartAt (Model n) x x) (tangentChartLinear x v) (tangentChartLinear x ξ) = inner ℝ v ξ :=
      metric_chart_pair x x (mem_chart_source (Model n) x) v ξ
    rw [hm] at h
    exact h.symm
  rw [hder] at hlim
  apply hlim.congr'
  have hnear := hz (d.open_source.mem_nhds hy)
  have hexp : Tendsto (fun j => exp x (l j•ξ)) atTop (𝓝 x) := by
    have hh := (geodesic_smooth (⟨x,ξ⟩ : TangentBundle (model n) M)).continuous.continuousAt.tendsto.comp hl
    simpa only [Function.comp_def,geodesic_zero,hexp_eq] using hh
  have hnearx := hexp (c.open_source.mem_nhds hx)
  filter_upwards [hnear,hnearx,hne] with j hj hxj hnj
  have he : a+l j•((l j)⁻¹•(C (l j)-a)) = C (l j) := by
    rw [smul_inv_smul₀ hnj,add_sub_cancel]
  simp only [hexp_eq] at hxj ⊢
  simp only [he,f,C,a,Function.comp_def,c.left_inv hx,c.left_inv hxj,d.left_inv hj]

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
