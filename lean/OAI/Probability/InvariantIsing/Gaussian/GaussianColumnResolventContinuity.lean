import OAI.Probability.InvariantIsing.Gaussian.GaussianColumnDeletion
import OAI.Probability.InvariantIsing.Spectral.PositiveResolventBounds

namespace OAI

/-! Measurability of the actual deleted-column resolvent observables. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma continuous_gaussianGramLeaveOneOut {N m : ℕ} (j : Fin m) :
    Continuous (gaussianGramLeaveOneOut (N := N) · j) := by
  apply continuous_matrix
  intro i k
  simp only [gaussianGramLeaveOneOut,Matrix.smul_apply,Matrix.sum_apply,
    Matrix.vecMulVec_apply,gaussianGramRawColumn,smul_eq_mul]
  fun_prop

lemma continuous_gaussianGramLeaveResolvent {N m : ℕ} {t : ℝ} (ht : 0 < t) (j : Fin m) :
    Continuous (gaussianGramLeaveResolvent (N := N) t · j) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hi := continuousAt_matrix_inv
    (t • (1 : Matrix (Fin N) (Fin N) ℝ)+gaussianGramLeaveOneOut z j)
    (show ContinuousAt Ring.inverse _ from by
      simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀
        (gaussianGramLeaveShift_posDef ht z j).det_pos.ne')
  exact hi.comp (f := fun w : EuclideanSpace ℝ (Fin N × Fin m) =>
    t • (1 : Matrix (Fin N) (Fin N) ℝ)+gaussianGramLeaveOneOut w j)
    ((continuous_const.add (continuous_gaussianGramLeaveOneOut j)).continuousAt)

lemma continuous_gaussianGramColumnQuadratic {N m : ℕ} {t : ℝ} (ht : 0 < t) (j : Fin m) :
    Continuous (gaussianGramColumnQuadratic (N := N) t · j) := by
  have hr := continuous_gaussianGramLeaveResolvent (N := N) ht j
  simp only [gaussianGramColumnQuadratic,gaussianPatternScaledColumn,gaussianGramRawColumn,
    Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul]
  fun_prop

lemma continuous_gaussianColumnArray {N m : ℕ} :
    Continuous (gaussianColumnArray (N := N) (m := m)) := by
  unfold gaussianColumnArray
  exact (PiLp.continuous_toLp 2 (fun _ : Fin N × Fin m => ℝ)).comp
    (continuous_pi (fun p => (continuous_apply p.1).comp (continuous_apply p.2)))

end InvariantIsing

end

end OAI
