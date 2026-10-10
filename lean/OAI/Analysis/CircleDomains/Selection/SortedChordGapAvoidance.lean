import OAI.Analysis.CircleDomains.Selection.SortedCrossingChords
import OAI.Analysis.CircleDomains.Topology.ClosedGapAvoidance
import OAI.Analysis.CircleDomains.Rigidity.AxialChordInterior

namespace OAI

/-! Enlarging the removed disks makes every closed retained gap avoid
the original source disks, including at the new boundary endpoints. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity
namespace SortedCrossingChords
variable {I : Type*} [Fintype I] {c : I → ℂ} {r : I → ℝ} {y a b : ℝ}

 theorem closed_gap_avoids_original (S : SortedCrossingChords c r y a b)
    (hr : ∀ j, 0 ≤ r j) (r₀ : I → ℝ) (hlt : ∀ j, r₀ j < r j)
    (i : Fin (S.count+1)) {x : ℝ}
    (hx : x ∈ Icc (gapsAfterHoles a b S.hole i).1 (gapsAfterHoles a b S.hole i).2) :
    ∀ j, (⟨x,y⟩ : ℂ) ∉ closedBall (c j) (r₀ j) := by
  intro j hxj
  have hout : (⟨x,y⟩ : ℂ) ∈ ball (c j) (r j) := (closedBall_subset_ball (hlt j)) hxj
  have hxab : x ∈ Icc a b := closed_gaps_inside S.hole
    (fun k => ⟨(S.inside k).1.le,(S.inside k).2.1,(S.inside k).2.2.le⟩) i hx
  have hj : j ∈ crossingDisks c r y a b := mem_crossingDisks.mpr ⟨x,hxab,ball_subset_closedBall hout⟩
  obtain ⟨k,hk⟩ := S.owner_surjective j hj
  have hxi := (mem_ball_iff_mem_horizontalChord _ (hr j) (crossingDisk_line_hit hj)).mp hout
  apply closed_gaps_avoid_hole_interiors a b S.hole S.monotone_first S.monotone_last i hx k
  simpa only [S.hole_eq,hk] using hxi

 theorem at_most_one_hole_for_disk (S : SortedCrossingChords c r y a b)
    (hr : ∀ j, 0 ≤ r j) (d : ℂ) (s : ℝ)
    (hone : ∀ i j, (closedBall d s ∩ closedBall (c i) (r i)).Nonempty →
      (closedBall d s ∩ closedBall (c j) (r j)).Nonempty → i = j) :
    ∀ i j, ({x | (⟨x,y⟩ : ℂ) ∈ closedBall d s} ∩ Icc (S.hole i).1 (S.hole i).2).Nonempty →
      ({x | (⟨x,y⟩ : ℂ) ∈ closedBall d s} ∩ Icc (S.hole j).1 (S.hole j).2).Nonempty → i = j := by
  intro i j hi hj
  obtain ⟨x,hxd,hxi⟩ := hi
  obtain ⟨z,hzd,hzj⟩ := hj
  apply S.owner_injective
  apply hone
  · refine ⟨(⟨x,y⟩ : ℂ),hxd,?_⟩
    apply (mem_closedBall_iff_mem_horizontalChord _ (hr _) (crossingDisk_line_hit (S.owner_mem i))).mpr
    simpa only [← S.hole_eq] using hxi
  · refine ⟨(⟨z,y⟩ : ℂ),hzd,?_⟩
    apply (mem_closedBall_iff_mem_horizontalChord _ (hr _) (crossingDisk_line_hit (S.owner_mem j))).mpr
    simpa only [← S.hole_eq] using hzj

end SortedCrossingChords
end CircleDomainRigidity

end

end OAI
