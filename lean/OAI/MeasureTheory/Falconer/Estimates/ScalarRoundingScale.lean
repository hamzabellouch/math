import OAI.MeasureTheory.Falconer.Geometry.ScalarRoundingBalls
import OAI.MeasureTheory.Falconer.Geometry.ScalarWeakProjection

namespace OAI

/-! The fixed losses of rounding fit into a quarter of the available
 scalar projection exponent at sufficiently fine scales. -/
namespace Falconer

 theorem scalar_rounding_scale {η κ : ℝ} (hη : 0 < η) (hκ : 0 ≤ κ)
    (B : ℕ) (hB : 0 < B) : ∃ M0 : ℕ, 0 < M0 ∧ ∀ M : ℕ, M0 ≤ M →
      5*Real.exp ((η/4)*(B:ℝ)*(M:ℝ)*Real.log 2) ≤ Real.exp (η*(B:ℝ)*(M:ℝ)*Real.log 2) ∧
      (2:ℝ)^κ*Real.exp ((η/4)*(B:ℝ)*(M:ℝ)*Real.log 2) ≤
        Real.exp (η*(B:ℝ)*(M:ℝ)*Real.log 2) := by
  have hb : (0:ℝ) < (B:ℝ) := by exact_mod_cast hB
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨M0,hM0⟩ := exists_nat_gt (max 1
    ((Real.log 5+κ*Real.log 2)/((3*η/4)*(B:ℝ)*Real.log 2)))
  have hM0pos : 0 < M0 := by
    have hh := (le_max_left _ _).trans_lt hM0
    exact_mod_cast (show (0:ℝ) < M0 by linarith)
  have hbase : Real.log 5+κ*Real.log 2 ≤ (3*η/4)*(B:ℝ)*(M0:ℝ)*Real.log 2 := by
    have hh := (div_lt_iff₀ (by positivity : 0 < (3*η/4)*(B:ℝ)*Real.log 2)).1
      ((le_max_right _ _).trans_lt hM0)
    nlinarith
  refine ⟨M0,hM0pos,?_⟩
  intro M hM
  have hh := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hM)
    (show 0 ≤ (3*η/4)*(B:ℝ)*Real.log 2 by positivity)
  have htotal : Real.log 5+κ*Real.log 2 ≤ (3*η/4)*(B:ℝ)*(M:ℝ)*Real.log 2 := by nlinarith
  have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have hklog : 0 ≤ κ*Real.log 2 := mul_nonneg hκ hl.le
  constructor
  · calc
      _ = Real.exp (Real.log 5+(η/4)*(B:ℝ)*(M:ℝ)*Real.log 2) := by
        rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ) < 5)]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  · rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2),← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith

end Falconer

end OAI
