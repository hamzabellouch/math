import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticPairPoisson

namespace OAI

/-! # The exact Möbius expansion of the common-divisor mask -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_moebius_divisor_sum (n : ℕ) :
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) =
      if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n)
    ArithmeticFunction.moebius_mul_coe_zeta
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] using h

 theorem coprime_mask_moebius (q n : ℕ) (hq : q ≠ 0) :
    (if n.Coprime q then (1 : ℤ) else 0) =
      ∑ d ∈ q.divisors, if d ∣ n then ArithmeticFunction.moebius d else 0 := by
  have hg : n.gcd q ≠ 0 := Nat.gcd_ne_zero_right hq
  have hf : q.divisors.filter (fun d => d ∣ n) = (n.gcd q).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdq, _⟩, hdn⟩
      exact ⟨Nat.dvd_gcd hdn hdq, hg⟩
    · rintro ⟨hd, _⟩
      exact ⟨⟨hd.trans (Nat.gcd_dvd_right n q), hq⟩,
        hd.trans (Nat.gcd_dvd_left n q)⟩
  rw [← Finset.sum_filter, hf, quadratic_moebius_divisor_sum]

 theorem principal_character_moebius {q : ℕ} [NeZero q] (n : ℤ) :
    (1 : DirichletCharacter ℂ q) (n : ZMod q) =
      ∑ d ∈ q.divisors, if (d : ℤ) ∣ n then (ArithmeticFunction.moebius d : ℂ) else 0 := by
  have h := congrArg (Int.cast : ℤ → ℂ) (coprime_mask_moebius q n.natAbs (NeZero.ne q))
  have hp : (1 : DirichletCharacter ℂ q) (n : ZMod q) =
      if n.natAbs.Coprime q then 1 else 0 := by
    rw [principal_character_intCast]
    rfl
  simpa only [hp, Int.cast_ite, Int.cast_one, Int.cast_zero, Int.cast_sum, Int.natCast_dvd] using h

end Ostmann

end OAI
