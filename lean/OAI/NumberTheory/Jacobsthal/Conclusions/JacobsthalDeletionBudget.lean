import OAI.NumberTheory.Jacobsthal.Conclusions.JacobsthalProgressionLength

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.JacobsthalDeletionBudget
open ProgressionSieve

theorem source_deletion_budget {x l : ℝ} (hx : 0 < x) (hl : 0 < l)
    (hlx : l^2 ≤ x) (Y Z : ℕ)
    (hT : (progressionLength Y Z:ℝ) ≤ 2*x/l)
    (hlog : l/2 ≤ Real.log (progressionLength Y Z:ℝ)) :
    x*deletionBudget Y Z ≤ 1275*x^2/l^2 := by
  have hlog0 : 0 < Real.log (progressionLength Y Z:ℝ) := by linarith
  have hquot : (progressionLength Y Z:ℝ)/Real.log (progressionLength Y Z:ℝ) ≤ 4*x/l^2 := by
    calc
      _ ≤ (2*x/l)/Real.log (progressionLength Y Z:ℝ) := div_le_div_of_nonneg_right hT hlog0.le
      _ ≤ (2*x/l)/(l/2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hlog
      _ = _ := by field_simp; ring
  have hunit : x ≤ x^2/l^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hl)).mpr
    nlinarith
  unfold deletionBudget
  calc
    _ ≤ x*(255*(1+4*x/l^2)) := by
      apply mul_le_mul_of_nonneg_left _ hx.le
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤255)
      linarith
    _ = 255*x+1020*(x^2/l^2) := by ring
    _ ≤ 1275*(x^2/l^2) := by linarith
    _ = _ := by ring
end NumberTheoryLean.JacobsthalDeletionBudget


end Erdos970

end OAI
