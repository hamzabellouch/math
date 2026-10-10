import OAI.Geometry.NodalSets.Charts.CommonSmoothChart
import OAI.Geometry.NodalSets.Charts.UniformInverseChartBounds

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
open scoped ContDiff Topology
noncomputable section

lemma nested_chart_inverse (F H : OpenPartialHomeomorph Coord Coord)
    (he : (F : Coord → Coord) = H) (hs : H.source ⊆ F.source)
    {z : Coord} (hz : z ∈ H.target) : F.symm z = H.symm z := by
  have hx := hs (H.map_target hz)
  have hv : F (H.symm z) = z := by rw [he]; exact H.right_inv hz
  calc
    F.symm z = F.symm (F (H.symm z)) := congrArg F.symm hv.symm
    _ = H.symm z := F.left_inv hx

lemma nested_chart_target (F H : OpenPartialHomeomorph Coord Coord)
    (he : (F : Coord → Coord) = H) (hs : H.source ⊆ F.source) : H.target ⊆ F.target := by
  intro z hz
  have h := F.map_source (hs (H.map_target hz))
  rwa [he,H.right_inv hz] at h

lemma nested_chart_inverse_germ (F H : OpenPartialHomeomorph Coord Coord)
    (he : (F : Coord → Coord) = H) (hs : H.source ⊆ F.source)
    {z : Coord} (hz : z ∈ H.target) :
    (F.symm : Coord → Coord) =ᶠ[𝓝 z] H.symm := by
  filter_upwards [H.open_target.mem_nhds hz] with x hx
  exact nested_chart_inverse F H he hs hx

variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem existing_chart_target_bounds
    (y : T → Coord) (hy : Continuous y)
    (e : T → Coord ≃L[ℝ] Coord) (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (B : T → Coord →L[ℝ] Coord →L[ℝ] Coord) (hB : Continuous B)
    (F : T → OpenPartialHomeomorph Coord Coord)
    (hF : ∀ t, (F t : Coord → Coord) = quadraticChartMap (y t) (e t) (B t))
    (r : ℝ) (hr : 0 < r) (hsource : ∀ t, (F t).source = ball 0 r)
    (k0 : ℕ) :
    ∃ delta > 0, ∃ R > 0, ∃ D : ℝ, 1 ≤ D ∧ ∀ t z,
      ‖z-y t‖ ≤ delta → z ∈ (F t).target ∧ ‖(F t).symm z‖ ≤ R ∧
      ContDiffAt ℝ ∞ ((F t).symm : Coord → Coord) z ∧
      ∀ k, 1 ≤ k → k ≤ k0 → ‖iteratedFDeriv ℝ k ((F t).symm : Coord → Coord) z‖ ≤ D^k := by
  let p : T → QuadParam Coord := fun t ↦ (y t,(e t).toContinuousLinearMap,B t)
  have hp : Continuous p := hy.prodMk (he.prodMk hB)
  have hD : Continuous (fun z : T × Coord ↦ fderiv ℝ (rawQuadratic (p z.1)) z.2) :=
    (smooth_spatial_fderiv rawQuadratic rawQuadratic_smooth).continuous.comp
      ((hp.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨R0,hR0,hJ0⟩ := compact_quadratic_chart_domain isCompact_univ y hy e he B hB
    isOpen_univ (fun _ _ ↦ mem_univ _)
  obtain ⟨r1,hr1,hr1R,d1,hd1,hH⟩ := compact_common_chart isCompact_univ
    (fun t ↦ rawQuadratic (p t)) (fun t ↦ quadraticChartMap_smooth _ _ _) hD e he
    (fun t ↦ (quadraticChartMap_deriv_zero (y t) (e t) (B t)).fderiv)
    (min R0 r) (lt_min hR0 hr)
  choose H hHe hHs hHt using fun t ↦ hH t (mem_univ t)
  have hJF (t : T) (x : Coord) (hx : x ∈ (H t).source) :
      ∃ J : Coord ≃L[ℝ] Coord, fderiv ℝ (rawQuadratic (p t)) x = J.toContinuousLinearMap := by
    have hn : ‖x‖ < r1 := by simpa [hHs] using hx
    obtain ⟨J,hJ⟩ := (hJ0 t (mem_univ t) x
      (hn.trans_le (hr1R.trans (min_le_left _ _)))).2
    exact ⟨J,hJ.symm⟩
  have hIs (t : T) : ContDiffOn ℝ ∞ (H t).symm (H t).target := by
    intro z hz
    obtain ⟨J,hJ⟩ := hJF t _ ((H t).map_target hz)
    have hd : HasFDerivAt (H t : Coord → Coord) J.toContinuousLinearMap ((H t).symm z) := by
      rw [hHe,← hJ]
      exact (quadraticChartMap_smooth _ _ _).differentiable (by simp) _ |>.hasFDerivAt
    apply ((H t).contDiffAt_symm hz hd _).contDiffWithinAt
    rw [hHe]
    exact (quadraticChartMap_smooth _ _ _).contDiffAt
  obtain ⟨r2,hr2,hr2r,d2,hd2,hQ⟩ := compact_common_chart isCompact_univ
    (fun t ↦ rawQuadratic (p t)) (fun t ↦ quadraticChartMap_smooth _ _ _) hD e he
    (fun t ↦ (quadraticChartMap_deriv_zero (y t) (e t) (B t)).fderiv) (r1/2) (by positivity)
  choose Q hQe hQs hQt using fun t ↦ hQ t (mem_univ t)
  have hclosed (t : T) : closedBall (0:Coord) (r1/2) ⊆ (H t).source := by
    rw [hHs]; exact closedBall_subset_ball (by linarith)
  obtain ⟨D,hD1,hDb⟩ := compact_inverse_derivative_bounds isCompact_univ p hp H
    (fun t _ ↦ hHe t) (fun t _ ↦ hIs t) (fun t _ ↦ hJF t) (r1/2)
    (fun t _ ↦ hclosed t) k0
  have hHF (t : T) : (H t).source ⊆ (F t).source := by
    rw [hHs,hsource]; exact ball_subset_ball (hr1R.trans (min_le_right _ _))
  have hQH (t : T) : (Q t).source ⊆ (H t).source := by
    rw [hQs,hHs]; exact ball_subset_ball (by linarith)
  have hFH (t : T) : (F t : Coord → Coord) = H t := (hF t).trans (hHe t).symm
  have hHQ (t : T) : (H t : Coord → Coord) = Q t := (hHe t).trans (hQe t).symm
  refine ⟨d2,hd2,r1/2,by positivity,D,hD1,?_⟩
  intro t z hz
  have hzQ : z ∈ (Q t).target := hQt t (by simpa [rawQuadratic,mem_closedBall,dist_eq_norm] using hz)
  have hzH := nested_chart_target (H t) (Q t) (hHQ t) (hQH t) hzQ
  have hqnorm : ‖(Q t).symm z‖ ≤ r1/2 := by
    have h := (Q t).map_target hzQ
    rw [hQs,mem_ball,dist_zero_right] at h
    exact h.le.trans hr2r
  have hinv := nested_chart_inverse (F t) (H t) (hFH t) (hHF t) hzH
  have hinv2 := nested_chart_inverse (H t) (Q t) (hHQ t) (hQH t) hzQ
  have hEq := nested_chart_inverse_germ (F t) (H t) (hFH t) (hHF t) hzH
  have hn : (H t).symm z ∈ closedBall (0:Coord) (r1/2) := by
    simpa [mem_closedBall,hinv2] using hqnorm
  refine ⟨nested_chart_target (F t) (H t) (hFH t) (hHF t) hzH,
    by simpa [hinv,hinv2] using hqnorm,
    ((hIs t).contDiffAt ((H t).open_target.mem_nhds hzH)).congr_of_eventuallyEq hEq,?_⟩
  intro k hk hk0
  rw [(hEq.iteratedFDeriv ℝ k).self_of_nhds]
  have hb := hDb t (mem_univ t) ((H t).symm z) hn k hk hk0
  rwa [(H t).right_inv hzH] at hb

end
end Yau.Geometry

end OAI
