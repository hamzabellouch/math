import OAI.Analysis.CircleDomains.Rigidity.ActualFiniteCircleFlux
import OAI.Analysis.CircleDomains.Rigidity.FiniteInnerFluxLimit
import OAI.Analysis.CircleDomains.Topology.FiniteTailDiskSeparation
import OAI.Analysis.CircleDomains.Sobolev.ClosedDiskIntegral

namespace OAI

/-! Removing the finite enlargements proves the manuscript's precise
finite-hole flux inequality for the actual selected correspondence. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem actual_finite_flux_of_trace [Countable D.IndexedMatchedPair]
    (E : D.MatchedRoundDisks) (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {R W : ℝ} (hR : 0 < R) (hRW : R < W)
    (htrace : ∀ i : Fin 2, ∀ᵐ y ∂volume, volume ((fun x => (complexPlaneCoordinates.symm
      (D.selectedPlane hG.1 hf (complexCoordinateLine i y x))) i) ''
      {x | complexCoordinateLine i y x ∈ D.commonPointPlane}) = 0)
    (hρ : IntegrableOn (fun z => ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) z‖)
      ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 W) volume)
    (hcontain : ∀ j, closedBall (E.sourceCenter j) (E.sourceRadius j) ⊆ ball 0 R)
    (F : Finset D.IndexedMatchedPair) :
    quadrantFlux (D.selectedPlane hG.1 hf) 0 R ≤
      2*(∫ z in {z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 R,
        ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) z‖)+
      2*Real.pi*(∑ j ∈ F, E.sourceRadius j*E.targetRadius j)+
      16*∑' j : {j : D.IndexedMatchedPair // j ∉ F}, E.sourceRadius j*E.targetRadius j := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨δ₁,hδ₁,hsep⟩ := exists_finite_tail_disk_separation E.sourceCenter E.sourceRadius
    E.source_nonneg E.source_disjoint E.source_summable F
  obtain ⟨δ₂,hδ₂,hbox⟩ := exists_common_round_hole_offset
    (fun j : F => E.sourceCenter j) (fun j => E.sourceRadius j) (fun j => E.source_nonneg j)
    (fun j k hjk => E.source_disjoint (fun he => hjk (Subtype.ext he))) isOpen_ball
    (fun j => hcontain j)
  obtain ⟨δ₃,hδ₃,hinner⟩ := D.finite_inner_quadrantFlux_limiting_bound E hG.1 hf F hε
  let η := min δ₁ (min δ₂ δ₃)
  have hη : 0 < η := lt_min hδ₁ (lt_min hδ₂ hδ₃)
  have hη₁ : η ≤ δ₁ := min_le_left _ _
  have hη₂ : η ≤ δ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hη₃ : η ≤ δ₃ := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨hd,hone⟩ := hsep η ⟨hη,hη₁⟩
  have hin (j : D.IndexedMatchedPair) (hj : j ∈ F) := (hbox η ⟨hη,hη₂⟩).1 ⟨j,hj⟩
  have h := D.actual_finite_circle_flux E hG hinf hf hfix hH hinf' hR hRW htrace hρ F hη hd hin hone
  rw [integral_inter_closedBall_eq_ball] at h
  have hi := hinner η ⟨hη,hη₃⟩
  linarith

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
