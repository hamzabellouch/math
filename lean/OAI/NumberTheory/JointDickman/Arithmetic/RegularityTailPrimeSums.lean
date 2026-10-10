import OAI.NumberTheory.JointDickman.Arithmetic.RegularityPrimeSums

namespace OAI

/-! # A uniform lower bound for reciprocal-prime tail masses -/

namespace JointDickman

open Finset

theorem regularity_tail_prime_sum_lower
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ B X Y : ℝ, 0 < B → 2 ≤ X → c * B ≤ Real.log X → 1 ≤ Y →
      Real.log (B / Y) - K ≤ ∑ p ∈ largePrimeSet X (Real.exp Y), 1 / (p : ℝ) := by
  obtain ⟨C, hC, hm⟩ := prime_interval_mertens_error hM
  refine ⟨2 * C + |Real.log c|, by positivity, ?_⟩
  intro B X Y hB hX hlog hY
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hEY : 2 ≤ Real.exp Y := by
    calc
      (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      _ ≤ _ := Real.exp_le_exp.mpr hY
  have hlogB : Real.log (c * B) = Real.log c + Real.log B :=
    Real.log_mul hc.ne' hB.ne'
  by_cases hYX : Real.exp Y ≤ X
  · have hlogXY : Y ≤ Real.log X := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos Y) hYX
    have hlogX1 : 1 ≤ Real.log X := hY.trans hlogXY
    have herr := hm (Real.exp Y) X hEY hYX
    rw [Real.log_exp] at herr
    have hCY : C / Y ≤ C := div_le_self hC hY
    have hCX : C / Real.log X ≤ C := div_le_self hC hlogX1
    have hcompare : Real.log c + Real.log B ≤ Real.log (Real.log X) := by
      rw [← hlogB]
      exact Real.log_le_log (mul_pos hc hB) hlog
    rw [Real.log_div hB.ne' hY0.ne']
    have hlo := (abs_le.mp herr).1
    have habs := neg_abs_le (Real.log c)
    linarith
  · have hXY : X < Real.exp Y := lt_of_not_ge hYX
    have hlogXY : Real.log X < Y := by
      simpa only [Real.log_exp] using Real.log_lt_log hX0 hXY
    have hcompare : Real.log c + Real.log B ≤ Real.log Y := by
      rw [← hlogB]
      exact Real.log_le_log (mul_pos hc hB) (hlog.trans hlogXY.le)
    have hsum : 0 ≤ ∑ p ∈ largePrimeSet X (Real.exp Y), 1 / (p : ℝ) :=
      sum_nonneg (fun _ _ => by positivity)
    rw [Real.log_div hB.ne' hY0.ne']
    have habs := neg_abs_le (Real.log c)
    linarith

end JointDickman

end OAI
