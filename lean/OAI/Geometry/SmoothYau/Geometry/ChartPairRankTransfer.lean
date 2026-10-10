import Mathlib
import OAI.Geometry.SmoothYau.Estimates.LinearProdSurjectiveMinor
import OAI.Geometry.SmoothYau.SphereMetric.ThreeAnalyticNormedSpace

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff
namespace YauCounterexamples
lemma chart_pair_rank_transfer {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ,E) ∞ M]
    {u v : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v) (p q : M) (hq : q ∈ (chartAt E p).source)
    (hr : Function.Surjective (fderiv ℝ (fun y => (u ((chartAt E q).symm y),v ((chartAt E q).symm y)))
      (chartAt E q q))) :
    Function.Surjective (fderiv ℝ (fun y => (u ((chartAt E p).symm y),v ((chartAt E p).symm y)))
      (chartAt E p q)) := by
  let e := chartAt E p
  let f := chartAt E q
  let T := e ∘ f.symm
  let H := fun y => (u (e.symm y),v (e.symm y))
  have hft : f q ∈ f.target := f.map_source (mem_chart_source E q)
  have hfs : f.symm (f q)=q := f.left_inv (mem_chart_source E q)
  have ht : DifferentiableAt ℝ T (f q) := by
    have h₁ := contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℝ,E)) (n:=∞) p) hq
    have h₂ := contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℝ,E)) (n:=∞) q) hft
    have h₁' : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e (f.symm (f q)) := hfs.symm ▸ h₁
    exact ((h₁'.comp (f q) h₂).contDiffAt).differentiableAt (by simp)
  have hH : DifferentiableAt ℝ H (T (f q)) := by
    have he := e.map_source hq
    have hh := (contDiffAt_inChart hu p he).prodMk (contDiffAt_inChart hv p he)
    simpa only [H,T,Function.comp_apply,hfs] using hh.differentiableAt (by simp)
  have hgerm : H ∘ T =ᶠ[𝓝 (f q)] (fun y => (u (f.symm y),v (f.symm y))) := by
    have hn : ∀ᶠ y in 𝓝 (f q), f.symm y ∈ e.source :=
      (f.continuousAt_symm hft).preimage_mem_nhds (hfs.symm ▸ e.open_source.mem_nhds hq)
    filter_upwards [hn] with y hy
    simp only [H,T,Function.comp_apply,e.left_inv hy]
  have hd := fderiv_comp (f q) hH ht
  rw [hgerm.fderiv_eq] at hd
  rw [hd] at hr
  have hh : Function.Surjective (fderiv ℝ H (T (f q))) := Function.Surjective.of_comp
    (f:=fun z => fderiv ℝ H (T (f q)) z) (g:=fun z => fderiv ℝ T (f q) z) hr
  simpa only [H,T,Function.comp_apply,hfs] using hh
lemma threeCoupled_profile_rank_somewhere {m : ℕ} (hm : 1 ≤ m) :
    ∃ x : ThreeModel, Function.Surjective (fderiv ℝ
      (fun y => (threeCoupled threeCouplingRadius (4*m+1) ((chartAt ThreeModel threeProfileCenter).symm y),
        coordinateGradientPair threeBackgroundMetric (threeCoupled threeCouplingRadius (4*m+1))
          (threeCoupled threeCouplingRadius (4*m+1)) ((chartAt ThreeModel threeProfileCenter).symm y))) x) := by
  obtain ⟨c,hc,hr⟩ := exists_threeCoupled_interior_gradient_rank threeCouplingRadius
    (by norm_num [threeCouplingRadius]) (by norm_num [threeCouplingRadius]) hm
  refine ⟨chartAt ThreeModel threeProfileCenter (threeInteriorMeridian c),?_⟩
  apply chart_pair_rank_transfer (threeCoupled_smooth _ _)
    (contMDiff_coordinateGradientPair (threeCoupled_smooth _ _) (threeCoupled_smooth _ _) _)
    threeProfileCenter (threeInteriorMeridian c) (threeInteriorMeridian_mem_profile_source c)
  simpa only [three_chart_center] using hr
lemma threeCoupled_profile_rank_dense {m : ℕ} (hm : 1 ≤ m)
    {O : Set ThreeModel} (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ x ∈ O, Function.Surjective (fderiv ℝ
      (fun y => (threeCoupled threeCouplingRadius (4*m+1) ((chartAt ThreeModel threeProfileCenter).symm y),
        coordinateGradientPair threeBackgroundMetric (threeCoupled threeCouplingRadius (4*m+1))
          (threeCoupled threeCouplingRadius (4*m+1)) ((chartAt ThreeModel threeProfileCenter).symm y))) x) := by
  obtain ⟨x,hx⟩ := threeCoupled_profile_rank_somewhere hm
  exact analytic_rank_dense _ _ (threeCoupled_chart_analytic _ _ _)
    (threeCoupled_gradient_chart_analytic _ _ (by omega) _) hx hO hne
end YauCounterexamples
end

end OAI
