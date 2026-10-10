import OAI.Analysis.CircleDomains.Sobolev.ActualLocalIntegrability
import OAI.Analysis.CircleDomains.Transfer.FiniteChartConnectivity

namespace OAI

/-! The actual matched disks are disjoint from the source and target
plane domains. All complementary points lie in one bounded disk. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem MatchedRoundDisks.source_disjoint_domain (E : D.MatchedRoundDisks) (j : D.IndexedMatchedPair) :
    Disjoint {z : ℂ | (z : Sphere) ∈ G} (ball (E.sourceCenter j) (E.sourceRadius j)) := by
  apply disjoint_left.mpr
  intro z hz hzb
  have hm : (z : Sphere) ∈ j.val.1 := by rw [E.source_eq j]; exact mem_image_of_mem _ (ball_subset_closedBall hzb)
  rw [j.property.1.1.eq_component_of_mem hm] at hm
  exact (connectedComponentIn_subset _ _ hm) hz

 theorem MatchedRoundDisks.target_disjoint_image (E : D.MatchedRoundDisks)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (j : D.IndexedMatchedPair) :
    Disjoint ((fun z : ℂ => finiteCoord (f (z : Sphere))) '' {z : ℂ | (z : Sphere) ∈ G})
      (ball (E.targetCenter j) (E.targetRadius j)) := by
  apply disjoint_left.mpr
  rintro w ⟨z,hz,rfl⟩ hw
  have hfinite := D.planeRelation_ne_infty hG hinf hf hfix (D.componentRelation_graph hf hz)
  have hm : (finiteCoord (f (z : Sphere)) : Sphere) ∈ j.val.2 := by
    rw [E.target_eq j]
    exact mem_image_of_mem _ (ball_subset_closedBall hw)
  have he : (finiteCoord (f (z : Sphere)) : Sphere) = f (z : Sphere) :=
    CannonMobius.coe_coordinate hfinite
  rw [he] at hm
  rw [j.property.1.2.1.eq_component_of_mem hm] at hm
  exact (connectedComponentIn_subset _ _ hm) (mem_image_of_mem f hz)

 theorem finite_domain_exterior_radius (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) :
    ∃ R > 0, ∀ z : ℂ, (z : Sphere) ∉ G → ‖z‖ < R := by
  exact ((OnePoint.isOpen_iff_of_mem hinf).mp hG).2.isBounded.exists_pos_norm_lt

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
