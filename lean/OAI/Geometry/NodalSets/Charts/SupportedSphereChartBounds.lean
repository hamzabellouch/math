import OAI.Geometry.NodalSets.Charts.SphereChartTransition
import OAI.Geometry.NodalSets.Elliptic.CompactLocalCompositionBounds

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem supported_sphere_chart_scalar_bound (r : ℝ) (p : Base)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q) (J : ℕ) :
    ∃ C > 0, ∀ f : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f →
      tsupport f ⊆ seedSpherePatch r → ∀ eps : ℝ, 0 ≤ eps →
      (∀ x i, i ≤ J → ‖iteratedFDeriv ℝ i (fun y ↦ f (seedSphereFromCoord y)) x‖ ≤ eps) →
      ∀ x ∈ Q, ∀ i, i ≤ J →
        ‖iteratedFDeriv ℝ i (fun y ↦ f (sphereChartCoordMap p y)) x‖ ≤ C*eps := by
  let K : Set Yau.Jets.Coord := Q ∩ sphereChartCoordMap p ⁻¹' closure (seedSpherePatch r)
  have hK : IsCompact K := hQ.inter_right
    (isClosed_closure.preimage (sphereChartCoordMap_smooth p).continuous)
  have hKU : K ⊆ sphereChartTransitionDomain p seedPoint := by
    intro x hx
    exact seedSpherePatch_closure_in_chart r hx.2
  obtain ⟨C,hC,hcomp⟩ := compact_local_composition_derivative_bound (G := ℝ)
    (sphereChartTransition p seedPoint) (sphereChartTransitionDomain_open p seedPoint)
    (sphereChartTransition_smoothOn p seedPoint) hK hKU J
  refine ⟨C,hC,?_⟩
  intro f hf hsup eps heps hb x hx i hi
  by_cases hxs : sphereChartCoordMap p x ∈ closure (seedSpherePatch r)
  · have hxK : x ∈ K := ⟨hx,hxs⟩
    have he : (fun y ↦ f (sphereChartCoordMap p y)) =ᶠ[𝓝 x]
        (fun y ↦ f (seedSphereFromCoord y)) ∘ sphereChartTransition p seedPoint := by
      filter_upwards [(sphereChartTransitionDomain_open p seedPoint).mem_nhds (hKU hxK)] with y hy
      exact congrArg f (sphereChartTransition_point p seedPoint hy).symm
    rw [(he.iteratedFDeriv ℝ i).eq_of_nhds]
    exact hcomp _ (hf.comp (sphereChartCoordMap_smooth seedPoint)).contDiff eps heps hb x hxK i hi
  · have hz : f =ᶠ[𝓝 (sphereChartCoordMap p x)] (fun _ ↦ 0) :=
      notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hxs (subset_closure (hsup h)))
    have hz' : (fun y ↦ f (sphereChartCoordMap p y)) =ᶠ[𝓝 x] (fun _ ↦ 0) :=
      hz.comp_tendsto (sphereChartCoordMap_smooth p).continuous.continuousAt
    rw [(hz'.iteratedFDeriv ℝ i).eq_of_nhds]
    simpa using mul_nonneg hC.le heps

end
end Yau.Target

end OAI
