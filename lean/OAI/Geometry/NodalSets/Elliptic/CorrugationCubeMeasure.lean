import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import OAI.Geometry.NodalSets.Elliptic.CorrugationCubePartition

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric MeasureTheory
open scoped ENNReal
noncomputable section

lemma corrugationCube_closed_inside (o : Coord) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n) (k : Fin 4 → Fin n) :
    closedBall (corrugationCubeCenter o L n k) ((L/(n:ℝ))/2) ⊆ Icc o (fun i ↦ o i+L) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hR : 0 < L/(n:ℝ) := div_pos hL hnR
  have hRn : (L/(n:ℝ))*(n:ℝ) = L := div_mul_cancel₀ L hnR.ne'
  intro x hx
  have hdist : ‖x-corrugationCubeCenter o L n k‖ ≤ (L/(n:ℝ))/2 := by
    simpa only [mem_closedBall,dist_eq_norm] using hx
  constructor <;> intro i
  all_goals
    have hi := (norm_le_pi_norm (x-corrugationCubeCenter o L n k) i).trans hdist
    change |x i-(o i+(L/(n:ℝ))*((k i:ℝ)+1/2))| ≤ _ at hi
    have ha := abs_le.mp hi
    have hk0 : (0:ℝ) ≤ (k i:ℝ) := by positivity
    have hk1 : (k i:ℝ)+1 ≤ n := by exact_mod_cast (k i).isLt
    nlinarith

lemma coordinate_cube_volume (y : Coord) {R : ℝ} (hR : 0 ≤ R) :
    volume (closedBall y (R/2)) = ENNReal.ofReal (R^4) := by
  rw [Real.volume_pi_closedBall y (by positivity)]
  norm_num [show 2*(R/2)=R by ring]

lemma coordinate_cube_volume_real (y : Coord) {R : ℝ} (hR : 0 ≤ R) :
    volume.real (closedBall y (R/2)) = R^4 := by
  rw [measureReal_def,coordinate_cube_volume y hR,ENNReal.toReal_ofReal (by positivity)]

end
end Yau.Geometry

end OAI
