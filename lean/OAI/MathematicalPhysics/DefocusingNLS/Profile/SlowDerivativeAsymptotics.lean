import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowAllOrdersAsymptotic
import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowAsymptoticCoefficients

namespace OAI

/-! # All-order expansions after any fixed spatial differentiation -/

open Polynomial

namespace DefocusingNLS

/-- Normalizing the exact derivative leaves the same outgoing integral with
shifted parameters, multiplied by the Pochhammer coefficient. -/
theorem normalized_iteratedDeriv_regularizedSlowSolution (k : ℕ) (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    x ^ (q + k) * iteratedDeriv k (regularizedSlowSolution q m) x =
      ((-1 : ℂ) ^ k * (ascPochhammer ℂ k).eval q) *
        normalizedSlowSolution (q + k) (m + k) x := by
  rw [iteratedDeriv_regularizedSlowSolution_closed k q m x hq hx hx0]
  unfold normalizedSlowSolution
  ring

/-- The expansion and error control survive any fixed number of spatial
 derivatives, uniformly up to the imaginary rays. -/
theorem iteratedDeriv_regularizedSlowSolution_allOrders_remainder (k n : ℕ)
    (q : ℂ) (m : ℕ) (hq : -1 < q.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℂ, 0 ≤ x.re → 1 ≤ ‖x‖ →
      ‖x ^ (q + k) * iteratedDeriv k (regularizedSlowSolution q m) x -
        ((-1 : ℂ) ^ k * (ascPochhammer ℂ k).eval q) *
          slowAsymptoticPolynomial (q + k) (m + k) n x‖ ≤ C / ‖x‖ ^ (n + 1) := by
  have hq' : -1 < (q + k).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith [Nat.cast_nonneg (α := ℝ) k]
  obtain ⟨A, hA, hb⟩ := regularizedSlowSolution_allOrders_remainder n (q + k) (m + k) hq'
  let c : ℂ := (-1 : ℂ) ^ k * (ascPochhammer ℂ k).eval q
  refine ⟨‖c‖ * A, mul_nonneg (norm_nonneg _) hA, ?_⟩
  intro x hx hn
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (zero_lt_one.trans_le hn).ne'
  rw [normalized_iteratedDeriv_regularizedSlowSolution k q m x hq hx hx0,
    ← mul_sub, norm_mul]
  calc
    _ ≤ ‖c‖ * (A / ‖x‖ ^ (n + 1)) := mul_le_mul_of_nonneg_left (hb x hx hn) (norm_nonneg _)
    _ = _ := by ring

end DefocusingNLS

end OAI
