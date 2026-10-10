import OAI.NumberTheory.JointDickman.Arithmetic.RamanujanDivisorFormula

namespace OAI

/-! # Multiplicativity of the Ramanujan factor in its modulus -/

namespace JointDickman
open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable def divisorIndicatorWeight (k : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n ∣ k then (n : ℂ) else 0, by simp⟩

theorem divisorIndicatorWeight_multiplicative (k : ℕ) :
    (divisorIndicatorWeight k).IsMultiplicative := by
  refine ⟨by simp [divisorIndicatorWeight],?_⟩
  intro m n hcop
  have hdiv : m*n ∣ k ↔ m ∣ k ∧ n ∣ k := by
    constructor
    · intro h
      exact ⟨dvd_trans (dvd_mul_right m n) h,dvd_trans (dvd_mul_left n m) h⟩
    · rintro ⟨hm,hn⟩
      exact hcop.mul_dvd_of_dvd_of_dvd hm hn
  simp only [divisorIndicatorWeight,coe_mk,hdiv,Nat.cast_mul]
  by_cases hm : m ∣ k <;> by_cases hn : n ∣ k <;> simp [hm,hn]

noncomputable def ramanujanArithmetic (k : ℕ) : ArithmeticFunction ℂ :=
  (μ : ArithmeticFunction ℂ)*divisorIndicatorWeight k

theorem ramanujanArithmetic_multiplicative (k : ℕ) :
    (ramanujanArithmetic k).IsMultiplicative :=
  isMultiplicative_moebius.intCast.mul (divisorIndicatorWeight_multiplicative k)

theorem ramanujanSum_eq_arithmetic (q : ℕ) [NeZero q] (k : ℕ) :
    ramanujanSum q (k : ZMod q) = ramanujanArithmetic k q := by
  rw [ramanujanSum_divisor_formula]
  unfold ramanujanArithmetic
  rw [ArithmeticFunction.mul_apply]
  simp only [intCoe_apply,divisorIndicatorWeight,coe_mk]

theorem ramanujanSum_multiplicative {a b : ℕ} [NeZero a] [NeZero b]
    [NeZero (a*b)] (hab : a.Coprime b) (k : ℕ) :
    ramanujanSum (a*b) (k : ZMod (a*b)) =
      ramanujanSum a (k : ZMod a)*ramanujanSum b (k : ZMod b) := by
  simp_rw [ramanujanSum_eq_arithmetic]
  exact (ramanujanArithmetic_multiplicative k).map_mul_of_coprime hab

end JointDickman

end OAI
