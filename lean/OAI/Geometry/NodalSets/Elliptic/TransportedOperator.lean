import OAI.Geometry.NodalSets.Charts.ChartPushforward
import OAI.Geometry.NodalSets.Charts.CommonInvariantCharts

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter Set
open scoped ContDiff Topology
noncomputable section

lemma coordPartial_eventuallyEq {f u : Coord → ℂ} {x : Coord}
    (he : f =ᶠ[𝓝 x] u) (i : Fin 4) : coordPartial i f =ᶠ[𝓝 x] coordPartial i u := by
  exact (he.fderiv (𝕜 := ℝ)).mono (fun _ h ↦ congrArg (fun L : Coord →L[ℝ] ℂ ↦ L (Pi.single i 1)) h)

lemma smoothSecondOrder_congr_germ (a : Fin 4 → Fin 4 → Coord → ℂ)
    (b : Fin 4 → Coord → ℂ) {f u : Coord → ℂ} {x : Coord} (he : f =ᶠ[𝓝 x] u) :
    smoothSecondOrder a b f x = smoothSecondOrder a b u x := by
  have hfirst (i : Fin 4) := (coordPartial_eventuallyEq he i).self_of_nhds
  have hsecond (i j : Fin 4) := (coordPartial_eventuallyEq (coordPartial_eventuallyEq he j) i).self_of_nhds
  simp only [smoothSecondOrder,hfirst,hsecond]

theorem transported_operator_identity
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (w : Coord → ℝ) (hw : ContDiff ℝ ∞ w)
    (p : QuadParam Coord) (F : OpenPartialHomeomorph Coord Coord)
    (hF : (F : Coord → Coord) = rawQuadratic p)
    (hInv : ContDiffOn ℝ ∞ F.symm F.target)
    (hJ : ∀ x ∈ F.source, ∃ J : Coord ≃L[ℝ] Coord,
      fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (hwp : ∀ z ∈ F.target, 0 < w z)
    (u : Coord → ℂ) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (hs : tsupport u ⊆ F.source)
    (z : Coord) (hz : z ∈ F.target) :
    sourceWeightedOperator g w (chartPushforward F u) z =
      smoothSecondOrder (fun i j ↦ complexPrincipal g i j p)
        (fun j ↦ complexDrift g w j p) u (F.symm z) := by
  have hx := F.map_target hz
  obtain ⟨J,hJe⟩ := hJ (F.symm z) hx
  have he : (chartPushforward F u) ∘ rawQuadratic p =ᶠ[𝓝 (F.symm z)] u := by
    filter_upwards [F.open_source.mem_nhds hx] with x hx'
    rw [← hF]
    exact chartPushforward_pullback F u x hx'
  have h := actual_weighted_coordinate_invariance g hg hp w hw p (F.symm z)
    (by rw [← hF,F.right_inv hz]; exact hwp z hz) J hJe
    (chartPushforward F u) (chartPushforward_smooth F hInv u hu hc hs).1
  rw [smoothSecondOrder_congr_germ _ _ he] at h
  rw [← hF,F.right_inv hz] at h
  exact h.symm

theorem transported_residual_derivative
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (w : Coord → ℝ) (hw : ContDiff ℝ ∞ w)
    (p : QuadParam Coord) (F : OpenPartialHomeomorph Coord Coord)
    (hF : (F : Coord → Coord) = rawQuadratic p)
    (hInv : ContDiffOn ℝ ∞ F.symm F.target)
    (hJ : ∀ x ∈ F.source, ∃ J : Coord ≃L[ℝ] Coord,
      fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (hwp : ∀ z ∈ F.target, 0 < w z)
    (u : Coord → ℂ) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (hs : tsupport u ⊆ F.source)
    (lam : ℂ) (z : Coord) (hz : z ∈ F.target) (k : ℕ) :
    iteratedFDeriv ℝ k (fun z ↦ sourceWeightedOperator g w (chartPushforward F u) z +
      lam * chartPushforward F u z) z =
    iteratedFDeriv ℝ k ((fun x ↦ smoothSecondOrder (fun i j ↦ complexPrincipal g i j p)
      (fun j ↦ complexDrift g w j p) u x + lam*u x) ∘ F.symm) z := by
  have he : (fun z ↦ sourceWeightedOperator g w (chartPushforward F u) z + lam * chartPushforward F u z) =ᶠ[𝓝 z]
      (fun x ↦ smoothSecondOrder (fun i j ↦ complexPrincipal g i j p)
        (fun j ↦ complexDrift g w j p) u x + lam*u x) ∘ F.symm := by
    filter_upwards [F.open_target.mem_nhds hz] with z hz'
    rw [transported_operator_identity g hg hp w hw p F hF hInv hJ hwp u hu hc hs z hz']
    simp [chartPushforward,hz']
  exact (he.iteratedFDeriv ℝ k).self_of_nhds

end
end Yau.Geometry

end OAI
