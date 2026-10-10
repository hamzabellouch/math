import OAI.Analysis.CircleDomains.Rigidity.AxialSwapDisks
import OAI.Analysis.CircleDomains.Selection.CrossingChords

namespace OAI

/-! Chords of disks inside an outer circle. The selected crossed disks
are exactly those whose transverse interval contains the line. -/
open Set Function Metric
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CircleDomainRigidity

 theorem horizontalChord_strict (c : ℂ) {r y : ℝ}
    (hy : y ∈ Ioo (c.im-r) (c.im+r)) :
    (horizontalChord c r y).1 < (horizontalChord c r y).2 := by
  have hp : 0 < r^2-(y-c.im)^2 := by
    nlinarith [mul_pos (show 0 < r-(y-c.im) by linarith [hy.2])
      (show 0 < r+(y-c.im) by linarith [hy.1])]
  have hs := Real.sqrt_pos.mpr hp
  dsimp only [horizontalChord]
  linarith

 theorem horizontalChord_endpoint_dist (c : ℂ) {r y : ℝ} (hr : 0 ≤ r)
    (hy : y ∈ Icc (c.im-r) (c.im+r)) (right : Bool) :
    dist (⟨if right then (horizontalChord c r y).2 else (horizontalChord c r y).1,y⟩ : ℂ) c = r := by
  have hs := Real.sq_sqrt (horizontalChord_nonneg c hr hy)
  rw [dist_eq_norm]
  have hn := Complex.sq_norm ((⟨if right then (horizontalChord c r y).2 else (horizontalChord c r y).1,y⟩ : ℂ)-c)
  cases right <;>
    simp only [Bool.false_eq_true,ite_false,ite_true,horizontalChord,Complex.normSq_apply,
      Complex.sub_re,Complex.sub_im] at hn ⊢ <;>
    nlinarith [norm_nonneg ((⟨c.re-Real.sqrt (r^2-(y-c.im)^2),y⟩ : ℂ)-c),
      norm_nonneg ((⟨c.re+Real.sqrt (r^2-(y-c.im)^2),y⟩ : ℂ)-c)]

 theorem axialChord_endpoint_dist (i : Fin 2) (c : ℂ) {r y : ℝ} (hr : 0 ≤ r)
    (hy : y ∈ Icc (transverseCoordinate i c-r) (transverseCoordinate i c+r)) (right : Bool) :
    dist (complexCoordinateLine i y
      (if right then (axialChord i c r y).2 else (axialChord i c r y).1)) c = r := by
  rw [← axialSwap_dist i,axialSwap_line]
  exact horizontalChord_endpoint_dist _ hr (by simpa only [axialSwap_im] using hy) right

 theorem enclosed_crossing_iff {κ : Type*} [Fintype κ]
    (i : Fin 2) (c : κ → ℂ) (r : κ → ℝ) {R y : ℝ} (hR : 0 ≤ R)
    (hy : y ∈ Icc (-R) R)
    (hin : ∀ j, closedBall (c j) (r j) ⊆ closedBall 0 R) (j : κ) :
    j ∈ crossingDisks (fun j => axialSwap i (c j)) r y
      (axialChord i 0 R y).1 (axialChord i 0 R y).2 ↔
      y ∈ Icc (transverseCoordinate i (c j)-r j) (transverseCoordinate i (c j)+r j) := by
  constructor
  · intro hj
    simpa only [axialSwap_im] using crossingDisk_line_hit hj
  · intro hj
    obtain ⟨x,hx⟩ := (complexCoordinateLine_meets_closedBall i y (c j) (r j)).mpr hj
    apply mem_crossingDisks.mpr
    refine ⟨x,?_,(horizontal_mem_swapped_disk i x y (c j) (r j)).mpr hx⟩
    exact (mem_closedBall_iff_mem_axialChord i 0 hR (by
      simpa [transverseCoordinate] using hy)).mp (hin j hx)

end CircleDomainRigidity

end

end OAI
