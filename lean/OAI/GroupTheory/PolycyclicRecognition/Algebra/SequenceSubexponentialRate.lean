import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

/-! # A common vanishing rate for subexponential coordinate bounds -/

noncomputable section
namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- A subexponential upper bound can be expressed by one nonnegative
vanishing exponential rate, including every initial scale. -/
theorem exists_sequence_subexponential_rate
    (scale R : ℕ → ℝ) (hs : ∀ n, 0 < scale n)
    (hR : HasSubexponentialUpperBoundSeq scale R) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ n, R n ≤ Real.exp (scale n * ε n) := by
  let ε := fun n => Real.log (max 1 (R n)) / scale n
  have hpos n : 0 < max 1 (R n) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hε n : 0 ≤ ε n := div_nonneg (Real.log_nonneg (le_max_left _ _)) (hs n).le
  refine ⟨ε, hε, ?_, ?_⟩
  · apply tendsto_order.2
    constructor
    · intro a ha
      exact Eventually.of_forall (fun n => ha.trans_le (hε n))
    · intro a ha
      filter_upwards [hR (a / 2) (half_pos ha)] with n hn
      have hmax : max 1 (R n) ≤ Real.exp ((a / 2) * scale n) :=
        max_le (Real.one_le_exp (mul_nonneg (half_pos ha).le (hs n).le)) hn
      have hlog : Real.log (max 1 (R n)) ≤ (a / 2) * scale n :=
        (Real.log_le_iff_le_exp (hpos n)).mpr hmax
      exact ((div_le_iff₀ (hs n)).mpr hlog).trans_lt (half_lt_self ha)
  · intro n
    have he : scale n * ε n = Real.log (max 1 (R n)) := by
      dsimp only [ε]
      field_simp [(hs n).ne']
    rw [he, Real.exp_log (hpos n)]
    exact le_max_right _ _

end PolycyclicRecognition

end

end OAI
