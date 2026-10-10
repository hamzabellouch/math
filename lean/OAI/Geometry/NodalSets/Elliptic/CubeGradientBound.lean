import OAI.Geometry.NodalSets.Charts.BallGeometry
import OAI.Geometry.NodalSets.Elliptic.CoordinatePartialJets

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Analysis Set
open scoped ENNReal ContDiff
noncomputable section

lemma inUnitCube_of_source_ball {x : Coord} (hx : sourceEuclideanNorm x ≤ 1) :
    InUnitCube x := by
  intro j
  exact (norm_le_pi_norm x j).trans ((norm_le_sourceEuclideanNorm x).trans hx)

lemma source_two_ball_of_inUnitCube {x : Coord} (hx : InUnitCube x) :
    sourceEuclideanNorm x ≤ 2 := by
  have hh : ‖x‖ ≤ 1 := (pi_norm_le_iff_of_nonneg (by norm_num)).mpr hx
  exact (sourceEuclideanNorm_le x).trans (by linarith)

lemma sourceEuclideanNorm_le_two_sum (x : Coord) :
    sourceEuclideanNorm x ≤ 2 * ∑ j, |x j| := by
  apply (sourceEuclideanNorm_le x).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _))).mpr
  intro j
  exact Finset.single_le_sum (fun i _ ↦ abs_nonneg (x i)) (Finset.mem_univ j)

def partialCubeControl (f : Coord → ℝ) (ds : List (Fin 4)) : ℝ≥0∞ :=
  cubeControl (partialJet f) [0,1,2,3] ds 0

lemma partial_enorm_le_control (f : Coord → ℝ) (hf : ContDiff ℝ ∞ f)
    (ds : List (Fin 4)) (x : Coord) (hx : InUnitCube x) :
    ‖partialJet f ds x‖ₑ ≤ partialCubeControl f ds := by
  apply enorm_le_cubeControl_zero (partialJet f)
    (fun ds ↦ (partialJet_smooth f hf ds).of_le (by simp))
    (fun _ _ _ ↦ rfl) [0,1,2,3] ds _ x hx
  intro i
  fin_cases i <;> simp

lemma gradient_enorm_le_cube_control (f : Coord → ℝ) (hf : ContDiff ℝ ∞ f)
    (x : Coord) (hx : sourceEuclideanNorm x ≤ 1) :
    ENNReal.ofReal (sourceEuclideanNorm (fun j ↦ fderiv ℝ f x (Pi.single j 1))) ≤
      2 * ∑ j : Fin 4, partialCubeControl f [j] := by
  calc
    _ ≤ ENNReal.ofReal (2 * ∑ j : Fin 4, |fderiv ℝ f x (Pi.single j 1)|) :=
      ENNReal.ofReal_le_ofReal (sourceEuclideanNorm_le_two_sum _)
    _ = 2 * ∑ j : Fin 4, ‖partialJet f [j] x‖ₑ := by
      rw [ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_sum_of_nonneg
        (fun _ _ ↦ abs_nonneg _)]
      simp [partialJet,← Real.norm_eq_abs]
    _ ≤ _ := mul_le_mul' le_rfl (Finset.sum_le_sum (fun j _ ↦
      partial_enorm_le_control f hf [j] x (inUnitCube_of_source_ball hx)))

end
end Yau.Geometry

end OAI
