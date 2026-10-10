import OAI.Analysis.CircleDomains.Rigidity.ActualAxialSlice
import OAI.Analysis.CircleDomains.Topology.CompactRelationCoordinateTest

namespace OAI

/-! The compact scalar used in the slice proof is constructed from the
actual relation. One typical line supports every segment and finite
family of removed source disks inside the working disk. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] Classical.propDecidable
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem axial_slices_of_trace [Countable D.IndexedMatchedPair]
    (E : D.MatchedRoundDisks) (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    (R : ℝ) (i k : Fin 2) (y : ℝ)
    (htrace : volume ((fun x => (complexPlaneCoordinates.symm
      (D.selectedPlane hG.1 hf (complexCoordinateLine i y x))) k) ''
      {x | complexCoordinateLine i y x ∈ D.commonPointPlane}) = 0)
    (htoll : Summable (fun j : D.IndexedMatchedPair =>
      (Icc (transverseCoordinate i (E.sourceCenter j)-E.sourceRadius j)
        (transverseCoordinate i (E.sourceCenter j)+E.sourceRadius j)).indicator
          (fun _ => 2*E.targetRadius j) y))
    (hρ : IntegrableOn (fun x => ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere)))
        (complexCoordinateLine i y x)‖)
      {x | (complexCoordinateLine i y x : Sphere) ∈ G ∧ complexCoordinateLine i y x ∈ ball 0 R} volume) :
    ∀ a b : ℝ, a ≤ b → ∀ F : Finset D.IndexedMatchedPair,
      (∀ x ∈ Icc a b, complexCoordinateLine i y x ∈ ball 0 R) →
      (∀ x ∈ Icc a b, ∀ j ∈ F, (complexCoordinateLine i y x : Sphere) ∉ j.val.1) →
      |(complexPlaneCoordinates.symm (D.selectedPlane hG.1 hf (complexCoordinateLine i y b))) k-
        (complexPlaneCoordinates.symm (D.selectedPlane hG.1 hf (complexCoordinateLine i y a))) k| ≤
        (∫ x in Icc a b ∩ {x | (complexCoordinateLine i y x : Sphere) ∈ G},
          ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) (complexCoordinateLine i y x)‖) +
        ∑' j : {j : D.IndexedMatchedPair // j ∉ F},
          if ∃ x ∈ Icc a b, (complexCoordinateLine i y x : Sphere) ∈ j.val.val.1
            then 2*E.targetRadius j else 0 := by
  obtain ⟨Φ,hΦ,hsΦ,hcoord,hrel⟩ := D.exists_compact_relation_coordinate_test hG.1 hinf hf hfix
    hH.1 hinf' (isCompact_closedBall (0 : ℂ) R) k
  intro a b hab F hseg havoid
  exact D.actual_axial_slice_estimate E hG hinf hf hfix hH hinf' hΦ hsΦ isOpen_ball k
    hcoord (fun z hz => hrel z (ball_subset_closedBall hz)) i y htrace htoll hab F hseg havoid
    (hρ.mono_set (fun x hx => ⟨hx.2,hseg x hx.1⟩))

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
