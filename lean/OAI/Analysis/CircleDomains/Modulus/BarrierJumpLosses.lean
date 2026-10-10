import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-! A fixed summable loss schedule for the compatible-barrier chain distance.
Its retained lower bound stays strictly above one quarter at every stage. -/

noncomputable section

namespace CircleDomainRigidity

def barrierStageLower (n : ℕ) : ℝ := 7/16 + 1/16 * (1/2)^n

def barrierStageLoss (n : ℕ) : ℝ := 1/32 * (1/2)^n

@[simp] theorem barrierStageLower_zero : barrierStageLower 0 = 1/2 := by
  norm_num [barrierStageLower]

theorem barrierStageLower_sub_loss (n : ℕ) :
    barrierStageLower n - barrierStageLoss n = barrierStageLower (n+1) := by
  simp only [barrierStageLower, barrierStageLoss, pow_succ]
  ring

theorem barrierStageLoss_pos (n : ℕ) : 0 < barrierStageLoss n := by
  unfold barrierStageLoss
  positivity

theorem barrierStageLoss_lt (n : ℕ) : barrierStageLoss n < barrierStageLower n := by
  have h : (0 : ℝ) < (1/2)^n := pow_pos (by norm_num) _
  unfold barrierStageLoss barrierStageLower
  nlinarith

theorem quarter_lt_barrierStageLower (n : ℕ) : (1 : ℝ)/4 < barrierStageLower n := by
  have h : (0 : ℝ) < (1/2)^n := pow_pos (by norm_num) _
  unfold barrierStageLower
  nlinarith

end CircleDomainRigidity

end

end OAI
