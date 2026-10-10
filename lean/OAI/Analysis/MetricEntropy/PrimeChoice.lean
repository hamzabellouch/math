import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import OAI.Analysis.MetricEntropy.Parameters

namespace OAI

/-!
# Choosing the prime after the finite parameters

The field size is chosen after the dimension,
direction count, and encoding cost. Infinitude of primes permits all these
bounds to be imposed simultaneously, without any upper bound on the prime.
-/

noncomputable section

namespace MetricEntropyDuality

/-- A natural prime exceeds every prescribed real bound. -/
theorem exists_prime_gt_real (bound : ℝ) :
    ∃ p : ℕ, p.Prime ∧ bound < (p : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_gt bound
  obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes n
  exact ⟨p, hp, hn.trans_le (Nat.cast_le.mpr hnp)⟩

/-- All parameters, including the encoding cost, precede the choice of prime. -/
theorem exists_prime_after_parameters (h u D : ℕ) (C B bound : ℝ) :
    ∃ p : ℕ, p.Prime ∧ bound < (p : ℝ) ∧ h < p ∧
      h ^ 2 * u ^ (2 * h) < p ∧ Real.exp (B * C / (D : ℝ)) < (p : ℝ) := by
  obtain ⟨p, hp, hall⟩ := exists_prime_gt_real
    (max (max bound (h : ℝ))
      (max ((h ^ 2 * u ^ (2 * h) : ℕ) : ℝ) (Real.exp (B * C / (D : ℝ)))))
  obtain ⟨hleft, hright⟩ := max_lt_iff.mp hall
  obtain ⟨hbound, hh⟩ := max_lt_iff.mp hleft
  obtain ⟨hsize, hexp⟩ := max_lt_iff.mp hright
  exact ⟨p, hp, hbound, Nat.cast_lt.mp hh, Nat.cast_lt.mp hsize, hexp⟩

theorem prime_log_pos {p : ℕ} (hp : p.Prime) : 0 < Real.log (p : ℝ) := by
  apply Real.log_pos
  simpa only [Nat.cast_one] using
    (Nat.cast_lt.mpr hp.one_lt : ((1 : ℕ) : ℝ) < (p : ℝ))

/-- The exponential lower bound on the prime absorbs the fixed encoding cost. -/
theorem prime_choice_entropy_lt {p D : ℕ} (hD : 0 < D)
    {B C : ℝ} (hchoice : Real.exp (B * C / (D : ℝ)) < (p : ℝ)) :
    B * C < (D : ℝ) * Real.log (p : ℝ) := by
  have hDreal : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hlog := Real.log_lt_log (Real.exp_pos (B * C / (D : ℝ))) hchoice
  rw [Real.log_exp] at hlog
  exact (div_lt_iff₀' hDreal).mp hlog

/-- Positivity of the encoding cost is not needed for this comparison. -/
theorem prime_choice_encoding_ratio_lt {p D : ℕ} (hp : p.Prime) (hD : 0 < D)
    {B C : ℝ} (hB : 0 < B)
    (hchoice : Real.exp (B * C / (D : ℝ)) < (p : ℝ)) :
    2 * C / ((D : ℝ) * Real.log (p : ℝ)) < 2 / B := by
  have hDreal : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  apply (div_lt_div_iff₀ (mul_pos hDreal (prime_log_pos hp)) hB).mpr
  have hbudget := prime_choice_entropy_lt hD hchoice
  calc
    (2 * C) * B = 2 * (B * C) := by rw [mul_assoc, mul_comm C B]
    _ < 2 * ((D : ℝ) * Real.log (p : ℝ)) :=
      mul_lt_mul_of_pos_left hbudget zero_lt_two

/-- A single prime satisfies the finite construction and entropy bounds. -/
theorem exists_prime_with_entropy_budget (h u D : ℕ) (C B bound : ℝ)
    (hD : 0 < D) (hB : 0 < B) :
    ∃ p : ℕ, p.Prime ∧ bound < (p : ℝ) ∧ h < p ∧
      h ^ 2 * u ^ (2 * h) < p ∧ Real.exp (B * C / (D : ℝ)) < (p : ℝ) ∧
      0 < Real.log (p : ℝ) ∧ B * C < (D : ℝ) * Real.log (p : ℝ) ∧
      2 * C / ((D : ℝ) * Real.log (p : ℝ)) < 2 / B := by
  obtain ⟨p, hp, hbound, hh, hsize, hexp⟩ :=
    exists_prime_after_parameters h u D C B bound
  exact ⟨p, hp, hbound, hh, hsize, hexp, prime_log_pos hp,
    prime_choice_entropy_lt hD hexp, prime_choice_encoding_ratio_lt hp hD hB hexp⟩

/-- The finite parameters are all fixed before the prime.
The caller may impose any additional real lower bound on the prime. -/
theorem exists_prime_for_rank {a : ℝ} (ha : 1 ≤ a) {r : ℕ} (hr : 0 < r)
    (B bound : ℝ) (hB : 0 < B) :
    let h := compressionRadius a
    let D := formDimension r h
    let u := directionCount r h (accuracy a)
    let C := encodingCost h (accuracy a) u
    ∃ p : ℕ, p.Prime ∧ bound < (p : ℝ) ∧ h < p ∧
      h ^ 2 * u ^ (2 * h) < p ∧ Real.exp (B * C / (D : ℝ)) < (p : ℝ) ∧
      0 < Real.log (p : ℝ) ∧ B * C < (D : ℝ) * Real.log (p : ℝ) ∧
      2 * C / ((D : ℝ) * Real.log (p : ℝ)) < 2 / B ∧ 0 < C := by
  let h := compressionRadius a
  let D := formDimension r h
  let u := directionCount r h (accuracy a)
  let C := encodingCost h (accuracy a) u
  have hh : 0 < h := compressionRadius_pos a
  have hθ := accuracy_pos ha
  have hD : 0 < D := formDimension_pos (j := h) hr
  have hu : 0 < u := directionCount_pos hr hh hθ
  have hC : 0 < C := encodingCost_pos hh hθ hu
  obtain ⟨p, hp, hbound, hhp, hsize, hexp, hlog, hbudget, hratio⟩ :=
    exists_prime_with_entropy_budget h u D C B bound hD hB
  exact ⟨p, hp, hbound, hhp, hsize, hexp, hlog, hbudget, hratio, hC⟩

end MetricEntropyDuality

end

end OAI
