import OAI.Geometry.NodalSets.Charts.CommonSmoothChart
import OAI.Geometry.NodalSets.Elliptic.WeightedDivergenceInvariance

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric
open scoped ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T]

theorem compact_invariant_charts {s : Set T} (hs : IsCompact s)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (w : Coord → ℝ) (hw : ContDiff ℝ ∞ w)
    (y : T → Coord) (hy : Continuous y) (e : T → Coord ≃L[ℝ] Coord)
    (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (B : T → Coord →L[ℝ] Coord →L[ℝ] Coord) (hB : Continuous B)
    {U : Set Coord} (hU : IsOpen U) (hyU : ∀ t ∈ s, y t ∈ U) (hwpos : ∀ x ∈ U, 0 < w x) :
    ∃ r > 0, ∃ d > 0, ∀ t ∈ s, ∃ F : OpenPartialHomeomorph Coord Coord,
      (F : Coord → Coord) = rawQuadratic (y t,(e t).toContinuousLinearMap,B t) ∧
      F.source = ball 0 r ∧ closedBall (y t) d ⊆ F.target ∧ F.target ⊆ U ∧
      ContDiffOn ℝ ∞ F.symm F.target ∧
      (∀ x ∈ F.source, ∃ J : Coord ≃L[ℝ] Coord,
        fderiv ℝ (rawQuadratic (y t,(e t).toContinuousLinearMap,B t)) x = J.toContinuousLinearMap) ∧
      ∀ (u : Coord → ℂ), ContDiff ℝ ∞ u → ∀ x ∈ F.source,
        smoothSecondOrder (fun i j ↦ complexPrincipal g i j (y t,(e t).toContinuousLinearMap,B t))
          (fun j ↦ complexDrift g w j (y t,(e t).toContinuousLinearMap,B t)) (u ∘ F) x =
          sourceWeightedOperator g w u (F x) := by
  obtain ⟨R,hR,hRi⟩ := compact_quadratic_chart_domain hs y hy e he B hB hU hyU
  have hD : Continuous (fun z : T × Coord ↦ fderiv ℝ
      (quadraticChartMap (y z.1) (e z.1) (B z.1)) z.2) :=
    (smooth_spatial_fderiv rawQuadratic rawQuadratic_smooth).continuous.comp
      (((hy.comp continuous_fst).prodMk ((he.comp continuous_fst).prodMk
        (hB.comp continuous_fst))).prodMk continuous_snd)
  obtain ⟨r,hr,hrR,d,hd,hF⟩ := compact_common_chart hs
    (fun t ↦ quadraticChartMap (y t) (e t) (B t))
    (fun t ↦ quadraticChartMap_smooth _ _ _) hD e he
    (fun t ↦ (quadraticChartMap_deriv_zero (y t) (e t) (B t)).fderiv) R hR
  refine ⟨r,hr,d,hd,?_⟩
  intro t ht
  obtain ⟨F,hFe,hFs,hFt⟩ := hF t ht
  have hFR (x : Coord) (hx : x ∈ F.source) : ‖x‖ < R := by
    rw [hFs,mem_ball,dist_zero_right] at hx
    exact hx.trans_le hrR
  have hsource (x : Coord) (hx : x ∈ F.source) : F x ∈ U := by
    rw [hFe]
    exact (hRi t ht x (hFR x hx)).1
  have hJac (x : Coord) (hx : x ∈ F.source) := (hRi t ht x (hFR x hx)).2
  have hsm : ContDiff ℝ ∞ (F : Coord → Coord) := by
    rw [hFe]; exact quadraticChartMap_smooth _ _ _
  refine ⟨F,hFe,hFs,by simpa only [quadraticChartMap_zero] using hFt,?_,?_,?_,?_⟩
  · intro z hz
    simpa only [F.right_inv hz] using hsource (F.symm z) (F.map_target hz)
  · intro z hz
    obtain ⟨J,hJe⟩ := hJac (F.symm z) (F.map_target hz)
    have hder : HasFDerivAt (F : Coord → Coord) J.toContinuousLinearMap (F.symm z) := by
      rw [hFe,hJe]
      exact (quadraticChartMap_smooth _ _ _).differentiable (by simp) _ |>.hasFDerivAt
    exact (F.contDiffAt_symm hz hder hsm.contDiffAt).contDiffWithinAt
  · intro x hx
    obtain ⟨J,hJe⟩ := hJac x hx
    exact ⟨J,hJe.symm⟩
  · intro u hu x hx
    obtain ⟨J,hJe⟩ := hJac x hx
    rw [hFe]
    have hwx : 0 < w (rawQuadratic (y t,(e t).toContinuousLinearMap,B t) x) := by
      change 0 < w (quadraticChartMap (y t) (e t) (B t) x)
      rw [← hFe]
      exact hwpos (F x) (hsource x hx)
    exact actual_weighted_coordinate_invariance g hg hp w hw
      (y t,(e t).toContinuousLinearMap,B t) x hwx J hJe.symm u hu

end
end Yau.Geometry

end OAI
