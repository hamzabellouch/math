import OAI.NumberTheory.Catalan.Energy.BarrierFinitePotentialRat
import OAI.NumberTheory.Catalan.Energy.BarrierTwoNormPPrefix060
import OAI.NumberTheory.Catalan.Energy.BarrierTwoNormVPrefix225

namespace OAI


noncomputable section
namespace InternalCatalan

theorem barrier_case2_norm_rational_upper :
    2 * barrierTrialNormSq barrierP2 + (1 / 2 : ℝ) * barrierTrialNormSq barrierV2 ≤
      (48651467 / 62500000 : ℝ) := by
  have hp : barrierTrialNormSq barrierP2 ≤
      (66295876 / 1000000000 : ℝ) + 154 / 100000000 := by
    refine (barrierTrialNormSq_le_prefix_add_geometric_tail barrierP2 60
      (94 / 100) (33 / 10000) barrier_trials_norm_summable.1
      (by norm_num) (by norm_num) (by norm_num) barrierP2_tail_decay).trans ?_
    exact add_le_add barrierP2_norm_prefix_60 (by norm_num)
  have hv : barrierTrialNormSq barrierV2 ≤
      (1291645220 / 1000000000 : ℝ) + 1206 / 100000000 := by
    refine (barrierTrialNormSq_le_prefix_add_geometric_tail barrierV2 225
      (984 / 1000) (93 / 10000) barrier_trials_norm_summable.2.1
      (by norm_num) (by norm_num) (by norm_num) barrierV2_tail_decay).trans ?_
    exact add_le_add barrierV2_norm_prefix_225 (by norm_num)
  calc
    _ ≤ 2 * ((66295876 / 1000000000 : ℝ) + 154 / 100000000) +
        (1 / 2 : ℝ) * ((1291645220 / 1000000000 : ℝ) + 1206 / 100000000) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hp (by norm_num))
        (mul_le_mul_of_nonneg_left hv (by norm_num))
    _ = _ := by norm_num

theorem barrier_case2_norm_coarse_upper :
    2 * barrierTrialNormSq barrierP2 + (1 / 2 : ℝ) * barrierTrialNormSq barrierV2 <
      (77844 / 100000 : ℝ) :=
  lt_of_le_of_lt barrier_case2_norm_rational_upper (by norm_num)

end InternalCatalan

end

end OAI
