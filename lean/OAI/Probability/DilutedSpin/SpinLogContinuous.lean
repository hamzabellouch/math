import OAI.Probability.DilutedSpin.MeasureHierarchy
import OAI.Probability.DilutedSpin.ProductTower

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
variable {ι : Type} [Fintype ι]
lemma spinLog_bound (F : (ι → Spin) → ℝ) {C : ℝ} (hF : ∀ s, |F s|≤C) (x : ι → ℝ) :
    |spinLog F x|≤C := by
  classical
  apply weighted_log_exp_bound _ _ (fun s => (Finset.prod_pos (fun i _ => q_pos _ _)).le) _ hF
  rw [← Fintype.prod_sum]
  simp only [q_sum, Finset.prod_const_one]
lemma spinLog_continuous (F : (ι → Spin) → ℝ) : Continuous (spinLog F) := by
  classical
  apply Continuous.log
  · exact continuous_finsetSum _ (fun s _ =>
      (continuous_finsetProd _ (fun i _ => (continuous_q (s i)).comp (continuous_apply i))).mul_const _)
  · intro x
    apply ne_of_gt
    exact Finset.sum_pos (fun s _ => mul_pos (Finset.prod_pos (fun i _ => q_pos _ _)) (Real.exp_pos _))
      Finset.univ_nonempty
end DilutedSpinGlass.FiniteLaw

end

end OAI
