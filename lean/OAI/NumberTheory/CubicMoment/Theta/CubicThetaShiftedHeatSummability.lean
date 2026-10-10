import OAI.NumberTheory.CubicMoment.Theta.CubicThetaDualHeatBounds
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowGaussBounds

namespace OAI

/-! The frequency and summable heat majorant at the translated cusps. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaShiftedRowFrequency (h : Eisenstein) : ℂ := (h:ℂ)/(9*traceLambda)

def cubicThetaShiftedRowHeatScale (h : Eisenstein) : ℝ :=
  4*Real.pi^2*Complex.normSq (cubicThetaShiftedRowFrequency h)

lemma cubicThetaShiftedRowHeatScale_eq (h : Eisenstein) :
    cubicThetaShiftedRowHeatScale h=(4*Real.pi^2/243)*norm h := by
  unfold cubicThetaShiftedRowHeatScale cubicThetaShiftedRowFrequency
  rw [Complex.normSq_div,map_mul,traceLambda_normSq]
  norm_num
  change 4*Real.pi^2*(norm h/243)=_
  ring

lemma cubicThetaShiftedRowHeatScale_pos {h : Eisenstein} (hh : h≠0) :
    0<cubicThetaShiftedRowHeatScale h := by
  rw [cubicThetaShiftedRowHeatScale_eq]
  exact mul_pos (by positivity) (norm_pos_of_ne_zero hh)

@[simp] lemma cubicThetaShiftedRowHeatScale_zero : cubicThetaShiftedRowHeatScale 0=0 := by
  simp [cubicThetaShiftedRowHeatScale_eq,norm]

theorem cubicThetaShiftedDualHeat_mass_summable {v : ℝ} (hv : 0 < v) {s : ℂ}
    (hs : 1 < s.re) :
    Summable (fun h : Eisenstein => ∫ t in Ioi (0:ℝ),
      ‖cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t‖) := by
  let b : ℝ := 4*Real.pi^2/243
  have hb : 0 < b := by dsimp [b]; positivity
  let J : ℝ := Real.Gamma (s.re+1)*(v^2)^(-(s.re+1))
  have hJ : 0 ≤ J := by
    apply mul_nonneg (Real.Gamma_pos_of_pos (by linarith)).le
    exact Real.rpow_nonneg (sq_nonneg v) _
  let K : ℝ := (2/b^2)*J
  have hK : 0 ≤ K := mul_nonneg (by positivity) hJ
  let m0 : ℝ := ∫ t in Ioi (0:ℝ), ‖cubicThetaDualHeat v s 0 t‖
  have hm0 : 0 ≤ m0 := integral_nonneg (fun _ => _root_.norm_nonneg _)
  have ht := (hasSum_ite_eq (0:Eisenstein) m0).summable.add
    ((summable_eisenstein_norm_rpow (s := 2) (by norm_num)).mul_left K)
  apply ht.of_nonneg_of_le
  · intro h
    exact integral_nonneg (fun _ => _root_.norm_nonneg _)
  · intro h
    by_cases hh : h = 0
    · subst h
      simp only [cubicThetaShiftedRowHeatScale_zero, ite_true]
      exact le_add_of_nonneg_right (mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) _))
    · simp only [hh, ite_false, zero_add]
      apply (cubicThetaDualHeat_norm_mass_bound hv hs (cubicThetaShiftedRowHeatScale_pos hh)).trans_eq
      rw [cubicThetaShiftedRowHeatScale_eq]
      change (2/(b*norm h)^2)*J = K*(norm h)^(-(2:ℝ))
      rw [Real.rpow_neg (norm_nonneg h), Real.rpow_two]
      dsimp [K]
      ring

end CubicFirstMoment

end

end OAI
