import OAI.Algebra.DepthFive.OccupationParameterBounds
import OAI.Algebra.DepthFive.ParameterBounds

namespace OAI

noncomputable section
namespace Problem335.LowerParameters

/-- The first-moment loss can be expressed at the common square-root scale. -/
theorem first_moment_loss_exp_lower {n : ℕ} (hn : 16 ≤ n) :
    Real.exp (-64 * Real.sqrt (n : ℝ)) ≤
      Real.exp (-64 / Real.sqrt (n : ℝ)) := by
  have hs := sqrt_ge_four hn
  have hspos : 0 < Real.sqrt (n : ℝ) := by linarith
  apply Real.exp_le_exp.mpr
  apply (le_div_iff₀ hspos).mpr
  nlinarith

/-- The actual U-layer correction has square-root exponential cost. -/
theorem u_layer_correction_le_exp {n : ℕ} (hn : 16 ≤ n)
    (hbeta : beta n ≤ 2 / Real.sqrt (n : ℝ)) :
    (1 + beta n) ^ m n ≤ Real.exp (2 * Real.sqrt (n : ℝ)) := by
  have hb : 0 ≤ beta n := (beta_pos (by omega : 4 ≤ n)).le
  have hm : (m n : ℝ) ≤ n := by exact_mod_cast m_le_n n
  have hs := sqrt_ge_four hn
  have hspos : 0 < Real.sqrt (n : ℝ) := by linarith
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hmul : (m n : ℝ) * beta n ≤ (n : ℝ) * (2 / Real.sqrt (n : ℝ)) := by
    gcongr
  have heq : (n : ℝ) * (2 / Real.sqrt (n : ℝ)) = 2 * Real.sqrt (n : ℝ) := by
    rw [← mul_div_assoc]
    apply (div_eq_iff hspos.ne').mpr
    nlinarith
  calc
    (1 + beta n) ^ m n ≤ (Real.exp (beta n)) ^ m n := by
      gcongr
      linarith [Real.add_one_le_exp (beta n)]
    _ = Real.exp ((m n : ℝ) * beta n) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (hmul.trans_eq heq)

/-- Consolidation of occupation, U-layer, and balanced-word losses. -/
theorem second_moment_loss_exp_upper {n : ℕ} (hn : 16 ≤ n)
    (hbeta : beta n ≤ 2 / Real.sqrt (n : ℝ)) :
    Real.exp (64 / Real.sqrt (n : ℝ)) * (1 + beta n) ^ m n *
      Real.exp (8 * Real.sqrt (n : ℝ)) ≤
      Real.exp (74 * Real.sqrt (n : ℝ)) := by
  have hs := sqrt_ge_four hn
  have hspos : 0 < Real.sqrt (n : ℝ) := by linarith
  have hloss : 64 / Real.sqrt (n : ℝ) ≤ 64 * Real.sqrt (n : ℝ) := by
    apply (div_le_iff₀ hspos).mpr
    nlinarith
  calc
    _ ≤ Real.exp (64 / Real.sqrt (n : ℝ)) *
        Real.exp (2 * Real.sqrt (n : ℝ)) * Real.exp (8 * Real.sqrt (n : ℝ)) := by
      gcongr
      exact u_layer_correction_le_exp hn hbeta
    _ = Real.exp (64 / Real.sqrt (n : ℝ) + 2 * Real.sqrt (n : ℝ) +
        8 * Real.sqrt (n : ℝ)) := by rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Problem335.LowerParameters

end

end OAI
