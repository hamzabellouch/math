import OAI.Analysis.CircleDomains.Selection.SelectedCoordinateTest
import OAI.Analysis.CircleDomains.Rigidity.MatchedRoundDisks
import OAI.Analysis.CircleDomains.Sobolev.RealCoordinateLines
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! The exact axial cost of an indexed target disk is at most twice its
radius, including a zero-radius target component. -/
open Set Function MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem physical_coordinate_difference_le (k : Fin 2) (z c : ℂ) :
    |(complexPlaneCoordinates.symm z) k-(complexPlaneCoordinates.symm c) k| ≤ ‖z-c‖ := by
  fin_cases k
  · change |z.re-c.re| ≤ ‖z-c‖
    exact Complex.abs_re_le_norm (z-c)
  · change |z.im-c.im| ≤ ‖z-c‖
    exact Complex.abs_im_le_norm (z-c)

 theorem axial_closedBall_image_measure_le (k : Fin 2) (c : ℂ) {r : ℝ} (_hr : 0 ≤ r) :
    volume ((fun z => (complexPlaneCoordinates.symm z) k) '' closedBall c r) ≤
      ENNReal.ofReal (2*r) := by
  have hsub : ((fun z => (complexPlaneCoordinates.symm z) k) '' closedBall c r) ⊆
      Icc ((complexPlaneCoordinates.symm c) k-r) ((complexPlaneCoordinates.symm c) k+r) := by
    rintro _ ⟨z,hz,rfl⟩
    have hh := (physical_coordinate_difference_le k z c).trans (by simpa only [mem_closedBall,dist_eq_norm] using hz)
    exact ⟨by linarith [(abs_le.mp hh).1],by linarith [(abs_le.mp hh).2]⟩
  apply (measure_mono hsub).trans_eq
  rw [Real.volume_Icc]
  congr 1
  ring

namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}

 theorem MatchedRoundDisks.target_axial_image_measure_le (E : D.MatchedRoundDisks)
    (k : Fin 2) (j : D.IndexedMatchedPair) :
    volume ((fun p => (complexPlaneCoordinates.symm (finiteCoord p)) k) '' j.val.2) ≤
      ENNReal.ofReal (2*E.targetRadius j) := by
  rw [E.target_eq,image_image]
  simpa only [finiteCoord_coe,Function.comp_def] using
    axial_closedBall_image_measure_le k (E.targetCenter j) (E.target_nonneg j)

 theorem MatchedRoundDisks.target_scalar_image_measure_le (E : D.MatchedRoundDisks)
    (k : Fin 2) (j : D.IndexedMatchedPair) {φ : Sphere → ℝ}
    (hφ : ∀ p ∈ (f '' G)ᶜ, φ p = (complexPlaneCoordinates.symm (finiteCoord p)) k) :
    volume (φ '' j.val.2) ≤ ENNReal.ofReal (2*E.targetRadius j) := by
  have he : φ '' j.val.2 = (fun p => (complexPlaneCoordinates.symm (finiteCoord p)) k) '' j.val.2 := by
    apply image_congr
    intro p hp
    obtain ⟨q,_,hK⟩ := j.property.1.2.1
    exact hφ p (connectedComponentIn_subset _ _ (hK ▸ hp))
  rw [he]
  exact E.target_axial_image_measure_le k j

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
