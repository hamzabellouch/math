import Mathlib

namespace OAI

namespace YauCounterexamples

lemma quartic_reparameterization (P : ℝ → Prop) {N : ℝ} (hN : 1 ≤ N)
    (h : ∀ s : ℝ, N ≤ s → P (s^4)) :
    ∀ n : ℝ, N^4 ≤ n → P n := by
  intro n hn
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  have hn0 : 0 ≤ n := (pow_nonneg hN0 _).trans hn
  let s := Real.sqrt (Real.sqrt n)
  have hs4 : s^4 = n := by
    calc
      _ = (s^2)^2 := by ring
      _ = (Real.sqrt n)^2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg n)]
      _ = n := Real.sq_sqrt hn0
  have hsN : N ≤ s := by
    have hh := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hn)
    have he : Real.sqrt (Real.sqrt (N^4)) = N := by
      rw [show N^4 = (N^2)^2 by ring,Real.sqrt_sq (sq_nonneg N),Real.sqrt_sq hN0]
    simpa only [he] using hh
  simpa only [hs4] using h s hsN
end YauCounterexamples

end OAI
