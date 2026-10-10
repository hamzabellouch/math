import OAI.Probability.InvariantIsing.Gaussian.GaussianColumnDeviation
import OAI.Probability.InvariantIsing.Gaussian.GaussianGramTraceGap
import OAI.Probability.InvariantIsing.Gaussian.GaussianGramResolventBounds

namespace OAI

/-! Replacing a leave-one-column quadratic form by the full normalized trace. -/
noncomputable section
open Matrix
namespace InvariantIsing

lemma gaussianGramColumnQuadratic_error {N m : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) (j : Fin m) :
    |gaussianGramColumnQuadratic t z j-gaussianGramStieltjes t z| ≤
      gaussianGramColumnDeviation t z j+1/((N : ℝ)*t) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hg := gaussianGramLeaveResolvent_trace_gap ht z j
  have he : (gaussianGramLeaveResolvent t z j).trace/N-gaussianGramStieltjes t z =
      ((gaussianGramLeaveResolvent t z j).trace-(gaussianGramResolvent t z).trace)/N := by
    unfold gaussianGramStieltjes
    ring
  have hd : |(gaussianGramLeaveResolvent t z j).trace/N-gaussianGramStieltjes t z| ≤
      1/((N : ℝ)*t) := by
    rw [he,abs_of_nonneg (div_nonneg hg.1 hn.le)]
    calc
      _ ≤ (1/t)/N := div_le_div_of_nonneg_right hg.2 hn.le
      _ = _ := by ring
  exact (abs_sub_le (gaussianGramColumnQuadratic t z j)
    ((gaussianGramLeaveResolvent t z j).trace/N) (gaussianGramStieltjes t z)).trans
    (add_le_add le_rfl hd)

end InvariantIsing

end

end OAI
