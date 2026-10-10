import OAI.Analysis.CircleDomains.Topology.RoundDiskSlices
import OAI.Analysis.CircleDomains.Rigidity.TypicalAxialDiskTolls

namespace OAI

/-! Both source-axis geometries use the same exact real chord intervals.
Swapping real coordinates preserves every source disk and its distances. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def axialSwap (i : Fin 2) (z : ℂ) : ℂ := if i = 0 then z else Complex.I*star z

 theorem axialSwap_dist (i : Fin 2) (z w : ℂ) : dist (axialSwap i z) (axialSwap i w) = dist z w := by
  unfold axialSwap
  split
  · rfl
  · simp only [dist_eq_norm,← mul_sub,norm_mul,Complex.norm_I,one_mul]
    rw [← star_sub,norm_star]

 theorem axialSwap_line (i : Fin 2) (y x : ℝ) :
    axialSwap i (complexCoordinateLine i y x) = (⟨x,y⟩ : ℂ) := by
  fin_cases i <;> apply Complex.ext <;>
    simp [axialSwap,complexCoordinateLine,realCoordinateLine]

 theorem axialSwap_im (i : Fin 2) (c : ℂ) : (axialSwap i c).im = transverseCoordinate i c := by
  fin_cases i <;> simp [axialSwap,transverseCoordinate]

 def axialChord (i : Fin 2) (c : ℂ) (r y : ℝ) : ℝ × ℝ := horizontalChord (axialSwap i c) r y

 theorem mem_closedBall_iff_mem_axialChord (i : Fin 2) (c : ℂ) {r y x : ℝ}
    (hr : 0 ≤ r) (hy : y ∈ Icc (transverseCoordinate i c-r) (transverseCoordinate i c+r)) :
    complexCoordinateLine i y x ∈ closedBall c r ↔
      x ∈ Icc (axialChord i c r y).1 (axialChord i c r y).2 := by
  have hd := axialSwap_dist i (complexCoordinateLine i y x) c
  rw [axialSwap_line] at hd
  change dist (complexCoordinateLine i y x) c ≤ r ↔ _
  rw [← hd]
  exact mem_closedBall_iff_mem_horizontalChord _ hr (by simpa only [axialSwap_im] using hy)

 theorem axial_ball_preimage_ordConnected (i : Fin 2) (y : ℝ) (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    OrdConnected {x | complexCoordinateLine i y x ∈ closedBall c r} := by
  by_cases he : ∃ x, complexCoordinateLine i y x ∈ closedBall c r
  · have hy := (complexCoordinateLine_meets_closedBall i y c r).mp he
    have hset : {x | complexCoordinateLine i y x ∈ closedBall c r} =
        Icc (axialChord i c r y).1 (axialChord i c r y).2 := by
      ext x
      exact mem_closedBall_iff_mem_axialChord i c hr hy
    rw [hset]
    exact ordConnected_Icc
  · have hset : {x | complexCoordinateLine i y x ∈ closedBall c r} = ∅ := by
      ext x
      simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false]
      exact fun hx => he ⟨x,hx⟩
    rw [hset]
    exact ordConnected_empty

end CircleDomainRigidity

end

end OAI
