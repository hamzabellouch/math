import OAI.Analysis.CircleDomains.Rigidity.MatchedPrincipalFlux
import OAI.Analysis.CircleDomains.Rigidity.ActualFiniteFluxLimit
import OAI.Analysis.CircleDomains.Sobolev.ExteriorOmittedAreaInput
import OAI.Analysis.CircleDomains.Rigidity.GeometricRigidity

namespace OAI

/-! The actual finite flux and the published exterior area theorem force
a principally normalized map to be the identity. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem normalized_identity_of_trace [Countable D.IndexedMatchedPair]
    (harea : ExteriorOmittedAreaTheorem) (E : D.MatchedRoundDisks)
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hnorm : IsPrincipalNormalized f)
    (hH : IsCircleDomain (f '' G))
    (htrace : ∀ i : Fin 2, ∀ᵐ y ∂volume, volume ((fun x => (complexPlaneCoordinates.symm
      (D.selectedPlane hG.1 hf (complexCoordinateLine i y x))) i) ''
      {x | complexCoordinateLine i y x ∈ D.commonPointPlane}) = 0) :
    ∀ p ∈ G, f p = p := by
  classical
  let U : Set ℂ := {z | (z : Sphere) ∈ G}
  let F : ℂ → ℂ := fun z => finiteCoord (f (z : Sphere))
  have hU : IsOpen U := hG.1.preimage OnePoint.continuous_coe
  obtain ⟨hUc,hUb⟩ := finite_part_connected_unbounded hG.2.1.isPreconnected
    (mem_interior_iff_mem_nhds.mpr (hG.1.mem_nhds hinf))
  have hUne : U.Nonempty := by
    by_contra h
    have he : U = ∅ := not_nonempty_iff_eq_empty.mp h
    apply hUb
    change IsBounded U
    rw [he]
    exact isBounded_empty
  obtain ⟨z₀,hz₀⟩ := hUne
  obtain ⟨A,hA,hAbound⟩ := finite_domain_exterior_radius hG.1 hinf
  obtain ⟨B,_,hBflux⟩ := D.selected_principal_quadrantFlux hG.1 hinf hf hnorm
  let R := max A (max B (‖z₀‖+1))
  have hAR : A ≤ R := le_max_left _ _
  have hBR : B ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hzR : ‖z₀‖ < R := by
    have h := (le_max_right B (‖z₀‖+1)).trans (le_max_right A (max B (‖z₀‖+1)))
    linarith
  have hR : 0 < R := hA.trans_le hAR
  have hExt : (closedBall (0 : ℂ) R)ᶜ ⊆ U := by
    intro z hz
    by_contra hg
    have hb := hAbound z hg
    have hz' : R < ‖z‖ := by simpa only [mem_compl_iff,mem_closedBall,dist_zero_right,not_le] using hz
    linarith
  have hcontain (j : D.IndexedMatchedPair) : closedBall (E.sourceCenter j) (E.sourceRadius j) ⊆ ball 0 R := by
    intro z hz
    have hm : (z : Sphere) ∈ j.val.1 := by rw [E.source_eq j]; exact mem_image_of_mem _ hz
    rw [j.property.1.1.eq_component_of_mem hm] at hm
    have hb := hAbound z (connectedComponentIn_subset _ _ hm)
    rw [mem_ball,dist_zero_right]
    exact hb.trans_le hAR
  have hd := D.finite_part_differentiableOn hG.1 hinf hf hnorm.1
  have hi := D.finite_part_injOn hG.1 hinf hf hnorm.1
  have hareaR := harea F R hR (hd.mono hExt) (hi.mono hExt) hnorm.2
  have hinf' : OnePoint.infty ∈ f '' G := hnorm.1 ▸ mem_image_of_mem f hinf
  obtain ⟨hid,_⟩ := identity_of_disk_geometry_exterior_area_and_finite_flux
    E.sourceCenter E.targetCenter E.sourceRadius E.targetRadius R hU hUc hd hi hExt
    (principal_remainder_tendsto_zero hnorm.2) hR.le E.source_nonneg E.target_nonneg
    ⟨z₀,hz₀,by simpa only [mem_ball,dist_zero_right] using hzR⟩
    (fun j k hjk => (E.source_disjoint hjk).mono ball_subset_closedBall ball_subset_closedBall)
    (fun j => MatchedRoundDisks.source_disjoint_domain D E j)
    (fun j => ball_subset_closedBall.trans (hcontain j))
    (fun j k hjk => (E.target_disjoint hjk).mono ball_subset_closedBall ball_subset_closedBall)
    (fun j => MatchedRoundDisks.target_disjoint_image D E hG.1 hinf hf hnorm.1 j) hareaR (by
      intro S
      have h := D.actual_finite_flux_of_trace E hG hinf hf hnorm.1 hH hinf' hR
        (show R < R+1 by linarith) htrace
        (D.actual_local_derivative_integrable hG.1 hinf hf hnorm.1 (R+1)) hcontain S
      rw [hBflux R hBR] at h
      nlinarith only [h])
  intro p hp
  cases p using OnePoint.rec with
  | infty => exact hnorm.1
  | coe z =>
    have hfinite := D.planeRelation_ne_infty hG.1 hinf hf hnorm.1 (D.componentRelation_graph hf hp)
    exact (CannonMobius.coe_coordinate hfinite).symm.trans
      (congrArg ((↑) : ℂ → Sphere) (hid z hp))

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
