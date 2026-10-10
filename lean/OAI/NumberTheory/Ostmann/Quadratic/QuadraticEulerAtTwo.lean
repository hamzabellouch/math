import OAI.NumberTheory.Ostmann.Quadratic.QuadraticRootCharacter

namespace OAI

/-! # The factor at two in the first quadratic Poisson main term -/

namespace Ostmann

open scoped Classical BigOperators

private noncomputable def quadraticMoebiusRoot (q : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => (ArithmeticFunction.moebius n : ℂ) * quadraticRootCharacter q n, by simp⟩

private theorem quadraticMoebiusRoot_multiplicative (q : ℕ) :
    (quadraticMoebiusRoot q).IsMultiplicative := by
  constructor
  · simp [quadraticMoebiusRoot, quadraticRootCharacter]
  · intro m n hmn
    change (ArithmeticFunction.moebius (m * n) : ℂ) * quadraticRootCharacter q (m * n) = _
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn,
      Int.cast_mul, quadraticRootCharacter_mul]
    change _ = ((ArithmeticFunction.moebius m : ℂ) * quadraticRootCharacter q m) *
      ((ArithmeticFunction.moebius n : ℂ) * quadraticRootCharacter q n)
    ring

theorem quadratic_root_euler_two (q D : ℕ) (hD : Odd D) :
    (∑ e ∈ (2 * D).divisors,
      (ArithmeticFunction.moebius e : ℂ) * quadraticRootCharacter q e) =
      (1 - quadraticRootCharacter q 2) *
        ∑ d ∈ D.divisors, (ArithmeticFunction.moebius d : ℂ) * quadraticRootCharacter q d := by
  have hh := ((quadraticMoebiusRoot_multiplicative q).mul
    ArithmeticFunction.isMultiplicative_zeta.natCast).map_mul_of_coprime hD.coprime_two_left
  simp only [ArithmeticFunction.coe_mul_zeta_apply] at hh
  change (∑ e ∈ (2 * D).divisors, quadraticMoebiusRoot q e) =
    (1 - quadraticRootCharacter q 2) * ∑ d ∈ D.divisors, quadraticMoebiusRoot q d
  rw [hh]
  congr 1
  have hd : Nat.divisors 2 = {1, 2} := by decide
  rw [hd]
  simp [quadraticMoebiusRoot, quadraticRootCharacter,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  ring

end Ostmann

end OAI
