import OAI.Geometry.NodalSets.Elliptic.TransportedOperator

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter
open scoped ContDiff Topology
noncomputable section

lemma sourceOperator_eventuallyEq
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (w : Coord → ℝ)
    {f u : Coord → ℂ} {x : Coord} (he : f =ᶠ[𝓝 x] u) :
    sourceWeightedOperator g w f =ᶠ[𝓝 x] sourceWeightedOperator g w u := by
  have hf (i : Fin 4) : sourceFlux g w f i =ᶠ[𝓝 x] sourceFlux g w u i := by
    filter_upwards [Filter.eventually_all.mpr (fun j ↦ coordPartial_eventuallyEq he j)] with z hz
    simp only [sourceFlux,hz]
  filter_upwards [Filter.eventually_all.mpr (fun i ↦ coordPartial_eventuallyEq (hf i) i)] with z hz
  simp only [sourceWeightedOperator,complexDivergence,hz]

lemma sourceWeightedOperator_zero
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (w : Coord → ℝ) :
    sourceWeightedOperator g w (fun _ ↦ 0) = 0 := by
  have he : sourceFlux g w (fun _ ↦ 0) = fun _ _ ↦ 0 := by
    funext i z
    simp [sourceFlux,coordPartial]
  funext x
  simp [sourceWeightedOperator,complexDivergence,he,coordPartial]

theorem source_residual_derivative_zero
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (w : Coord → ℝ)
    (u : Coord → ℂ) (lam : ℂ) (x : Coord) (hx : x ∉ tsupport u) (k : ℕ) :
    iteratedFDeriv ℝ k (fun z ↦ sourceWeightedOperator g w u z + lam*u z) x = 0 := by
  have he : u =ᶠ[𝓝 x] (fun _ ↦ 0) := notMem_tsupport_iff_eventuallyEq.mp hx
  have hr : (fun z ↦ sourceWeightedOperator g w u z + lam*u z) =ᶠ[𝓝 x] (fun _ ↦ 0) := by
    filter_upwards [sourceOperator_eventuallyEq g w he,he] with z hz hu
    simp only [hz,hu,sourceWeightedOperator_zero,Pi.zero_apply,mul_zero,add_zero]
  rw [(hr.iteratedFDeriv ℝ k).self_of_nhds]
  simp

end
end Yau.Geometry

end OAI
