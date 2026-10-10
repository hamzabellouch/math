import OAI.Geometry.NodalSets.Charts.ChartedEnvelope
import OAI.Geometry.NodalSets.Elliptic.OperatorLocality

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter
open scoped Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma metricGradient_eventuallyEq
    {g G : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {S A : Coord → ℝ} {x : Coord}
    (hg : g =ᶠ[𝓝 x] G) (hS : S =ᶠ[𝓝 x] A) :
    metricGradient g S =ᶠ[𝓝 x] metricGradient G A := by
  filter_upwards [hg,hS.fderiv (𝕜 := ℝ)] with z hz hd
  simp only [metricGradient,hz,hd]

lemma sourceHessian_eventuallyEq
    {g G : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {S A : Coord → ℝ} {x : Coord}
    (hg : g =ᶠ[𝓝 x] G) (hS : S =ᶠ[𝓝 x] A) :
    sourceHessian g S =ᶠ[𝓝 x] sourceHessian G A := by
  filter_upwards [hg,hg.fderiv (𝕜 := ℝ),hS.fderiv (𝕜 := ℝ),
    (hS.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)] with z hz hd hs hss
  simp only [sourceHessian,hz,hd,hs,hss]

lemma sourceOperator_coefficients_eventuallyEq
    {g G : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w W : Coord → ℝ} {x : Coord}
    (hg : g =ᶠ[𝓝 x] G) (hw : w =ᶠ[𝓝 x] W) (u : Coord → ℂ) :
    sourceWeightedOperator g w u =ᶠ[𝓝 x] sourceWeightedOperator G W u := by
  have he (i : Fin 4) : sourceFlux g w u i =ᶠ[𝓝 x] sourceFlux G W u i := by
    filter_upwards [hg,hw] with z hz hwz
    simp only [sourceFlux,sourcePrincipal,hz,hwz]
  filter_upwards [hw,Filter.eventually_all.mpr (fun i ↦ coordPartial_eventuallyEq (he i) i)] with z hwz hz
  simp only [sourceWeightedOperator,complexDivergence,hwz,hz]

lemma sourceResidual_coefficients_derivative_eq
    {g G : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w W : Coord → ℝ} {x : Coord}
    (hg : g =ᶠ[𝓝 x] G) (hw : w =ᶠ[𝓝 x] W) (u : Coord → ℂ) (lam : ℂ) (k : ℕ) :
    iteratedFDeriv ℝ k (fun z ↦ sourceWeightedOperator g w u z+lam*u z) x =
      iteratedFDeriv ℝ k (fun z ↦ sourceWeightedOperator G W u z+lam*u z) x := by
  have he := sourceOperator_coefficients_eventuallyEq hg hw u
  have hr : (fun z ↦ sourceWeightedOperator g w u z+lam*u z) =ᶠ[𝓝 x]
      (fun z ↦ sourceWeightedOperator G W u z+lam*u z) := by
    filter_upwards [he] with z hz
    rw [hz]
  exact (hr.iteratedFDeriv ℝ k).self_of_nhds

end
end Yau.Geometry

end OAI
