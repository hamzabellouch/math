import OAI.Geometry.NodalSets.Coefficients.CoefficientLocality
import OAI.Geometry.NodalSets.Elliptic.CompactSmoothExtension

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

theorem compact_source_representatives {K U : Set Coord} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hUn : U.Nonempty)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w S : Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hS : ContDiffOn ℝ ∞ S U)
    (hwp : ∀ x ∈ U, 0 < w x) :
    ∃ (G : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (W A : Coord → ℝ) (E : Set Coord),
      ContDiff ℝ ∞ G ∧ ContDiff ℝ ∞ W ∧ ContDiff ℝ ∞ A ∧
      (∀ x u v, G x u v = G x v u) ∧ (∀ x v, v ≠ 0 → 0 < G x v v) ∧
      IsOpen E ∧ K ⊆ E ∧ E ⊆ U ∧ (∀ x ∈ E, 0 < W x) ∧
      ∀ x ∈ E, (G =ᶠ[𝓝 x] g) ∧ (W =ᶠ[𝓝 x] w) ∧ (A =ᶠ[𝓝 x] S) ∧
        metricGradient G A x = metricGradient g S x ∧ sourceHessian G A x = sourceHessian g S x := by
  obtain ⟨G,hG,hGs,hGp,hGe⟩ := compact_positive_metric_extension hK hU hKU hUn g hg hs hp
  obtain ⟨W,hW,_,_,hWe⟩ := compact_smooth_extension hK hU hKU w hw
  obtain ⟨A,hA,_,_,hAe⟩ := compact_smooth_extension hK hU hKU S hS
  let B : Set Coord := {x | G x = g x ∧ W x = w x ∧ A x = S x}
  let E := U ∩ interior B
  have hE : IsOpen E := hU.inter isOpen_interior
  have hKE : K ⊆ E := by
    intro x hx
    refine ⟨hKU hx,mem_interior_iff_mem_nhds.mpr ?_⟩
    exact (hGe x hx).and ((hWe x hx).and (hAe x hx))
  have hgerm (x : Coord) (hx : x ∈ E) : (G =ᶠ[𝓝 x] g) ∧
      (W =ᶠ[𝓝 x] w) ∧ (A =ᶠ[𝓝 x] S) := by
    have hh : ∀ᶠ z in 𝓝 x, G z = g z ∧ W z = w z ∧ A z = S z :=
      mem_of_superset (hE.mem_nhds hx) (fun z hz ↦ interior_subset hz.2)
    exact ⟨hh.mono (fun _ h ↦ h.1),hh.mono (fun _ h ↦ h.2.1),hh.mono (fun _ h ↦ h.2.2)⟩
  refine ⟨G,W,A,E,hG,hW,hA,hGs,hGp,hE,hKE,inter_subset_left,?_,?_⟩
  · intro x hx
    rw [(hgerm x hx).2.1.self_of_nhds]
    exact hwp x hx.1
  · intro x hx
    obtain ⟨heG,heW,heA⟩ := hgerm x hx
    exact ⟨heG,heW,heA,(metricGradient_eventuallyEq heG heA).self_of_nhds,
      (sourceHessian_eventuallyEq heG heA).self_of_nhds⟩

end
end Yau.Geometry

end OAI
