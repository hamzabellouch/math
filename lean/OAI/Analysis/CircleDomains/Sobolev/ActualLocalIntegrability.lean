import OAI.Analysis.CircleDomains.Sobolev.SphereScalarLineSmooth
import OAI.Analysis.CircleDomains.Sobolev.TargetArea

namespace OAI

/-! Local derivative integrability follows from the actual bounded image
of each compact source disk. No boundary area or integrability premise is
needed for the finite-hole estimate. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)
include D

 theorem finite_part_differentiableOn (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty) :
    DifferentiableOn ℂ (fun z : ℂ => finiteCoord (f (z : Sphere))) {z | (z : Sphere) ∈ G} := by
  intro z hz
  exact (analyticAt_finite_map_of_conformal hG hf.1 hz
    (D.planeRelation_ne_infty hG hinf hf hfix (D.componentRelation_graph hf hz))).differentiableAt.differentiableWithinAt

 theorem selectedPlane_eq_finite_part (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {z : ℂ} (hz : (z : Sphere) ∈ G) :
    D.selectedPlane hG hf z = finiteCoord (f (z : Sphere)) :=
  congrArg finiteCoord (D.componentRelation_on_domain hz (D.selectedTarget_mem hG hf _))

 theorem finite_part_injOn (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty) :
    InjOn (fun z : ℂ => finiteCoord (f (z : Sphere))) {z | (z : Sphere) ∈ G} := by
  intro x hx y hy hxy
  have hfx := D.planeRelation_ne_infty hG hinf hf hfix (D.componentRelation_graph hf hx)
  have hfy := D.planeRelation_ne_infty hG hinf hf hfix (D.componentRelation_graph hf hy)
  apply OnePoint.coe_injective
  apply hf.bijOn.injOn hx hy
  exact (CannonMobius.coe_coordinate hfx).symm.trans
    ((congrArg ((↑) : ℂ → Sphere) hxy).trans (CannonMobius.coe_coordinate hfy))

 theorem actual_local_derivative_integrable (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty) (R : ℝ) :
    IntegrableOn (fun z => ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) z‖)
      ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 R) volume := by
  let U : Set ℂ := {z | (z : Sphere) ∈ G}
  have hU : IsOpen U := hG.preimage OnePoint.continuous_coe
  have hd := D.finite_part_differentiableOn hG hinf hf hfix
  obtain ⟨B,hB,hbound⟩ := D.selectedPlane_bounded_on_compact hG hinf hf hfix
    (isCompact_closedBall (0 : ℂ) R)
  have himage : (fun z : ℂ => finiteCoord (f (z : Sphere))) '' (U ∩ ball 0 R) ⊆ ball 0 B := by
    rintro w ⟨z,hz,rfl⟩
    rw [mem_ball,dist_zero_right]
    dsimp only
    rw [← D.selectedPlane_eq_finite_part hG hf hz.1]
    exact hbound z (ball_subset_closedBall hz.2)
  have hsq := integrable_norm_deriv_sq_of_image_area_finite (hU.inter isOpen_ball).measurableSet
    (fun z hz => (hd z hz.1).differentiableAt (hU.mem_nhds hz.1))
    ((D.finite_part_injOn hG hinf hf hfix).mono inter_subset_left)
    (ne_of_lt ((measure_mono himage).trans_lt measure_ball_lt_top))
  exact integrable_norm_deriv_of_sq hU hd (hU.inter isOpen_ball).measurableSet
    (isBounded_ball.subset inter_subset_right) inter_subset_left hsq

 theorem exists_source_containment_radius (E : D.MatchedRoundDisks)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) :
    ∃ R > 0, ∀ j, closedBall (E.sourceCenter j) (E.sourceRadius j) ⊆ ball 0 R := by
  obtain ⟨R,hR,hbound⟩ := ((OnePoint.isOpen_iff_of_mem hinf).mp hG).2.isBounded.exists_pos_norm_lt
  refine ⟨R,hR,?_⟩
  intro j z hz
  rw [mem_ball,dist_zero_right]
  apply hbound
  change (z : Sphere) ∈ Gᶜ
  have hm : (z : Sphere) ∈ j.val.1 := by
    rw [E.source_eq j]
    exact mem_image_of_mem _ hz
  rw [j.property.1.1.eq_component_of_mem hm] at hm
  exact connectedComponentIn_subset _ _ hm

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
