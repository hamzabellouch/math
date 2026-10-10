import Mathlib.Data.Nat.Totient
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCoprimePoisson

namespace OAI

/-! # The exact totient coefficient of the coprime Poisson main term -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_totient_moebius (q : ℕ) (hq : q ≠ 0) :
    (∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) / d) = (q.totient : ℝ) / q := by
  have hsum (n : ℕ) (_hn : 0 < n) :
      (∑ d ∈ n.divisors, (d.totient : ℝ)) = (n : ℝ) := by
    exact_mod_cast Nat.sum_totient n
  have hm := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℝ)).mp hsum
    q (Nat.pos_of_ne_zero hq)
  have hm' := (Nat.sum_divisorsAntidiagonal (n := q)
    (fun d e => (ArithmeticFunction.moebius d : ℝ) * (e : ℝ))).symm.trans hm
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  apply (mul_right_cancel₀ hqR)
  rw [div_mul_cancel₀ _ hqR, Finset.sum_mul]
  calc
    _ = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * ((q / d : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd)
        (by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne' : (d : ℝ) ≠ 0)]
      ring
    _ = _ := hm'

end Ostmann

end OAI
