import OAI.Geometry.NodalSets.Charts.SphereFiniteAtlasSubsequence
import OAI.Geometry.NodalSets.Coefficients.FiniteSphereCoefficientAtlas

namespace OAI

namespace Yau.Target
open Manifold Yau.Analysis Yau.Geometry Set Metric Filter
open scoped Topology ContDiff
noncomputable section

theorem sphere_chart_limit_gluing (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ ball (0 : Yau.Jets.Coord) 1,
      sphereChartCoordMap p z = x)
    (w : ℕ → Base → ℝ)
    (hlim : ∀ p ∈ P, ∃ f : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ f ∧
      ∀ Q : Set Yau.Jets.Coord, IsCompact Q →
        TendstoUniformlyOn (fun j ↦ w j ∘ sphereChartCoordMap p) f atTop Q) :
    ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧
      TendstoUniformly w v atTop ∧
      ∀ p ∈ P, ∀ f : Yau.Jets.Coord → ℝ,
        (∀ x, Tendsto (fun j ↦ w j (sphereChartCoordMap p x)) atTop (𝓝 (f x))) →
        v ∘ sphereChartCoordMap p = f := by
  classical
  have hex (p : {p // p ∈ P}) := hlim p.val p.property
  choose f hf hconv using hex
  have hcov (x : Base) : ∃ p : {p // p ∈ P}, ∃ z ∈ ball (0 : Yau.Jets.Coord) 1,
      sphereChartCoordMap p.val z = x := by
    obtain ⟨p,hp,z,hz,he⟩ := hcover x
    exact ⟨⟨p,hp⟩,z,hz,he⟩
  choose c z hz he using hcov
  let v : Base → ℝ := fun x ↦ f (c x) (z x)
  have hvpoint (x : Base) : Tendsto (fun j ↦ w j x) atTop (𝓝 (v x)) := by
    have h := (hconv (c x) {z x} isCompact_singleton).tendsto_at (mem_singleton (z x))
    simpa only [Function.comp_apply,he,v] using h
  have hvchart (p : {p // p ∈ P}) (y : Yau.Jets.Coord) :
      v (sphereChartCoordMap p.val y) = f p y := by
    exact tendsto_nhds_unique (hvpoint _) ((hconv p {y} isCompact_singleton).tendsto_at
      (mem_singleton y))
  have hvsmooth : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v := by
    intro x
    have hsource : x ∈ (extChartAt (𝓡 4) (c x).val).source := by
      have h := sphereChartCoordMap_source (c x).val (z x)
      rwa [he x] at h
    have hchart := contMDiffAt_extChartAt' (I := 𝓡 4) (n := ∞) (x := (c x).val) (x' := x)
      (by simpa only [extChartAt_source] using hsource)
    have hh := (((hf (c x)).comp seedCoordEquiv.symm.contDiff).contMDiff.contMDiffAt).comp x hchart
    apply hh.congr_of_eventuallyEq
    filter_upwards [(isOpen_extChartAt_source (c x).val).mem_nhds hsource] with y hy
    have h := hvchart (c x) (seedCoordEquiv.symm ((extChartAt (𝓡 4) (c x).val) y))
    simpa only [sphereChartCoordMap,seedCoordEquiv.apply_symm_apply,
      (extChartAt (𝓡 4) (c x).val).left_inv hy,Function.comp_apply] using h
  refine ⟨v,hvsmooth,?_,?_⟩
  · rw [Metric.tendstoUniformly_iff]
    intro eps heps
    have hh (p : {p // p ∈ P}) := Metric.tendstoUniformlyOn_iff.mp
      (hconv p (closedBall (0 : Yau.Jets.Coord) 1) (isCompact_closedBall _ _)) eps heps
    filter_upwards [Filter.eventually_all.mpr hh] with j hj x
    have h := hj (c x) (z x) (ball_subset_closedBall (hz x))
    simpa only [Function.comp_apply,he,v] using h
  · intro p hp g hg
    funext y
    exact tendsto_nhds_unique (hvpoint _) (hg y)

end
end Yau.Target

end OAI
