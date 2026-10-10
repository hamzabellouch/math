import Mathlib.Data.EReal.Basic
import Mathlib.Order.LiminfLimsup
import OAI.NumberTheory.Catalan.Determinants.RealDeterminantUpper

namespace OAI


noncomputable section

namespace InternalCatalan

open Filter

def manuscriptNormalizedLogSize (N : ℕ) (a : ℝ) : EReal :=
  if a = 0 then ⊥ else
    ((Real.log |a| / (n N : ℝ) ^ 2 - Real.log 2 / 2 : ℝ) : EReal)

@[simp] theorem manuscriptNormalizedLogSize_zero (N : ℕ) :
    manuscriptNormalizedLogSize N 0 = ⊥ := by
  simp [manuscriptNormalizedLogSize]

theorem manuscriptNormalizedLogSize_of_ne_zero {N : ℕ} {a : ℝ} (ha : a ≠ 0) :
    manuscriptNormalizedLogSize N a =
      ((Real.log |a| / (n N : ℝ) ^ 2 - Real.log 2 / 2 : ℝ) : EReal) := by
  simp [manuscriptNormalizedLogSize, ha]

def manuscriptDeterminantLogSize (N : ℕ) : EReal :=
  manuscriptNormalizedLogSize N (determinant N)

theorem manuscriptDeterminantLogSize_of_eq_zero {N : ℕ} (hN : determinant N = 0) :
    manuscriptDeterminantLogSize N = ⊥ := by
  simp [manuscriptDeterminantLogSize, hN]

theorem manuscriptDeterminantLogSize_of_ne_zero {N : ℕ} (hN : determinant N ≠ 0) :
    manuscriptDeterminantLogSize N =
      ((Real.log |determinant N| / (n N : ℝ) ^ 2 - Real.log 2 / 2 : ℝ) : EReal) :=
  manuscriptNormalizedLogSize_of_ne_zero hN

theorem manuscript_limsup_le_of_eventually_le {u : ℕ → EReal} {c : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, u N ≤ ((c + ε : ℝ) : EReal)) :
    Filter.limsup u atTop ≤ (c : EReal) := by
  refine (Filter.limsup_le_iff').2 ?_
  intro y hy
  obtain ⟨r, hcr, hry⟩ := EReal.lt_iff_exists_real_btwn.mp hy
  have hε : 0 < r - c := sub_pos.mpr (EReal.coe_lt_coe_iff.mp hcr)
  filter_upwards [h (r - c) hε] with N hN
  have heq : c + (r - c) = r := by
    rw [add_comm c (r - c), sub_add_cancel]
  rw [heq] at hN
  exact hN.trans hry.le

end InternalCatalan





namespace InternalCatalan

open Filter

theorem determinant_real_place_limsup :
    Filter.limsup manuscriptDeterminantLogSize atTop ≤
      ((-(2290939875 / 1000000000 : ℝ)) : EReal) := by
  apply manuscript_limsup_le_of_eventually_le
  intro ε hε
  filter_upwards [eventually_realDeterminant_log_upper_sharp hε] with N hN
  by_cases hzero : determinant N = 0
  · rw [manuscriptDeterminantLogSize_of_eq_zero hzero]
    exact bot_le
  · rw [manuscriptDeterminantLogSize_of_ne_zero hzero]
    exact EReal.coe_le_coe_iff.mpr (hN hzero)

theorem real_place_limsup_constant_lt_threshold :
    ((-(2290939875 / 1000000000 : ℝ)) : EReal) <
      ((-(22909 / 10000 : ℝ)) : EReal) := by
  apply EReal.coe_lt_coe_iff.mpr
  norm_num

theorem determinant_real_place_limsup_lt_threshold :
    Filter.limsup manuscriptDeterminantLogSize atTop <
      ((-(22909 / 10000 : ℝ)) : EReal) :=
  determinant_real_place_limsup.trans_lt real_place_limsup_constant_lt_threshold

theorem real_place_separate_case_constants :
    ((realEnergyDualConstant 1 barrierP1 barrierV1
      (realEnergyRowTrialSup 1 barrierLambda1 barrierP1 barrierV1)
      (realEnergyColumnTrialSup barrierV1) : ℝ) : EReal) <
        ((-(2296789875 / 1000000000 : ℝ)) : EReal) ∧
    ((realEnergyDualConstant 2 barrierP2 barrierV2
      (realEnergyRowTrialSup 2 0 barrierP2 barrierV2)
      (realEnergyColumnTrialSup barrierV2) : ℝ) : EReal) <
        ((-(2290939875 / 1000000000 : ℝ)) : EReal) :=
  ⟨EReal.coe_lt_coe_iff.mpr realDeterminantCaseOneDual_sharp_lt,
    EReal.coe_lt_coe_iff.mpr realDeterminantCaseTwoDual_sharp_lt⟩

end InternalCatalan

end

end OAI
