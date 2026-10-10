import OAI.Probability.InvariantIsing.Gaussian.GaussianGramResolvent
import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternEigenvalueMeasurability

namespace OAI

/-! Uniform bounds and measurability for the physical positive resolvent. -/
noncomputable section
open Matrix
namespace InvariantIsing

lemma gaussianGramResolvent_mixed_trace_nonneg {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    0 ≤ (gaussianPatternCoupling 1 z*gaussianGramResolvent t z).trace := by
  have hp := ((gaussianGramResolvent_posDef ht z).posSemidef.conjTranspose_mul_mul_same
    (gaussianPatternArray z)).trace_nonneg
  rw [gaussianPatternCoupling,smul_mul_assoc,Matrix.trace_smul,smul_eq_mul]
  apply mul_nonneg (by positivity)
  rw [Matrix.trace_mul_cycle,Matrix.trace_mul_cycle]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hp

lemma gaussianGramStieltjes_le {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) : gaussianGramStieltjes t z ≤ 1/t := by
  by_cases hN : N = 0
  · subst N
    simp only [gaussianGramStieltjes,Nat.cast_zero,div_zero]
    exact (one_div_pos.mpr ht).le
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hi := gaussianGramResolvent_trace_identity ht z
  have hp := gaussianGramResolvent_mixed_trace_nonneg ht z
  apply (div_le_iff₀ hN').mpr
  calc
    _ ≤ (N : ℝ)/t := (le_div_iff₀ ht).mpr (by nlinarith)
    _ = 1/t*N := by ring

lemma continuous_gaussianGramResolvent {N m : ℕ} {t : ℝ} (ht : 0 < t) :
    Continuous (gaussianGramResolvent (N := N) (m := m) t) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hdet := (gaussianGramShift_posDef ht z).det_pos
  have hi := continuousAt_matrix_inv
    (t • (1 : Matrix (Fin N) (Fin N) ℝ)+gaussianPatternCoupling 1 z)
    (show ContinuousAt Ring.inverse _ from by
      simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet.ne')
  change ContinuousAt (fun w : EuclideanSpace ℝ (Fin N × Fin m) =>
    (t • (1 : Matrix (Fin N) (Fin N) ℝ)+gaussianPatternCoupling 1 w)⁻¹) z
  exact hi.comp (f := fun w : EuclideanSpace ℝ (Fin N × Fin m) =>
    t • (1 : Matrix (Fin N) (Fin N) ℝ)+gaussianPatternCoupling 1 w)
    ((continuous_const.add (continuous_gaussianPatternCoupling N m 1)).continuousAt)

lemma continuous_gaussianGramStieltjes {N m : ℕ} {t : ℝ} (ht : 0 < t) :
    Continuous (gaussianGramStieltjes (N := N) (m := m) t) := by
  exact (continuous_gaussianGramResolvent ht).matrix_trace.div_const _

end InvariantIsing

end

end OAI
