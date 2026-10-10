import OAI.NumberTheory.Ostmann.Quadratic.QuadraticKernelConductor
import OAI.NumberTheory.Ostmann.ZeroDensity.PublishedRealZeros

namespace OAI

/-! # Primitive real characters representing the four signed kernel shapes -/

namespace Ostmann

theorem character_ne_one_of_conductor_dvd {n N : ℕ} [NeZero n]
    (χ : DirichletCharacter ℝ n) (hN : 1 < N) (hdiv : N ∣ χ.conductor) : χ ≠ 1 := by
  intro h
  rw [h, DirichletCharacter.conductor_one] at hdiv
  have := Nat.dvd_one.mp hdiv
  omega

noncomputable def primitiveRealOfCharacter {n : ℕ} [NeZero n]
    (χ : DirichletCharacter ℝ n) (hχ : χ ≠ 1) : PrimitiveRealCharacter where
  modulus := χ.conductor
  positive := Nat.pos_of_ne_zero χ.conductor_ne_zero
  character := χ.primitiveCharacter
  primitive := χ.primitiveCharacter_isPrimitive
  nontrivial := by
    intro h
    have he : χ = 1 := by
      rw [← χ.changeLevel_primitiveCharacter, h, map_one]
    exact hχ he

theorem primitiveRealOfCharacter_value {n : ℕ} [NeZero n]
    (χ : DirichletCharacter ℝ n) (hχ : χ ≠ 1) (a : ℕ) (ha : a.Coprime n) :
    (primitiveRealOfCharacter χ hχ).character a = χ a := by
  change χ.primitiveCharacter (a : ZMod χ.conductor) = χ (a : ZMod n)
  rw [← Int.cast_natCast (R := ZMod χ.conductor),
    ← Int.cast_natCast (R := ZMod n)]
  exact χ.primitiveCharacter_apply_of_isCoprime (Nat.isCoprime_iff_coprime.mpr ha)

/-- An odd squarefree numerator, including either sign, has a primitive
representative whose conductor lies between N and 4N. -/
theorem exists_odd_kernel_primitive (N : ℕ) (hN : 1 < N) (hsf : Squarefree N)
    (hodd : Odd N) (negative : Bool) :
    ∃ χ : PrimitiveRealCharacter, N ∣ χ.modulus ∧ χ.modulus ≤ 4 * N ∧
      ∀ a : ℕ, Odd a → a.Coprime N →
        χ.character a = (jacobiSym (if negative then -(N : ℤ) else N) a : ℝ) := by
  let : NeZero N := ⟨by omega⟩
  let : NeZero (Nat.lcm N 4) := ⟨Nat.lcm_ne_zero (NeZero.ne N) (by decide)⟩
  let ψ := signedOddKernelCharacter N negative
  have hb := signedOddKernelCharacter_conductor_bounds N negative hsf hodd
  have hn : ψ ≠ 1 := character_ne_one_of_conductor_dvd ψ hN hb.1
  refine ⟨primitiveRealOfCharacter ψ hn, hb.1, hb.2, ?_⟩
  intro a ha haN
  have ha4 : a.Coprime 4 := by simpa using ha.coprime_two_right.pow_right 2
  have hac : a.Coprime (Nat.lcm N 4) :=
    (haN.mul_right ha4).of_dvd_right (Nat.lcm_dvd_mul N 4)
  rw [primitiveRealOfCharacter_value ψ hn a hac]
  exact signedOddKernelCharacter_value N negative hodd a hac ha

/-- The same construction for twice an odd squarefree numerator. -/
theorem exists_even_kernel_primitive (N : ℕ) (hN : 1 < N) (hsf : Squarefree N)
    (hodd : Odd N) (negative : Bool) :
    ∃ χ : PrimitiveRealCharacter, N ∣ χ.modulus ∧ χ.modulus ≤ 8 * N ∧
      ∀ a : ℕ, Odd a → a.Coprime N →
        χ.character a = (jacobiSym (if negative then -(2 * (N : ℤ)) else 2 * N) a : ℝ) := by
  let : NeZero N := ⟨by omega⟩
  let : NeZero (Nat.lcm N 8) := ⟨Nat.lcm_ne_zero (NeZero.ne N) (by decide)⟩
  let ψ := signedEvenKernelCharacter N negative
  have hb := signedEvenKernelCharacter_conductor_bounds N negative hsf hodd
  have hn : ψ ≠ 1 := character_ne_one_of_conductor_dvd ψ hN hb.1
  refine ⟨primitiveRealOfCharacter ψ hn, hb.1, hb.2, ?_⟩
  intro a ha haN
  have ha8 : a.Coprime 8 := by simpa using ha.coprime_two_right.pow_right 3
  have hac : a.Coprime (Nat.lcm N 8) :=
    (haN.mul_right ha8).of_dvd_right (Nat.lcm_dvd_mul N 8)
  rw [primitiveRealOfCharacter_value ψ hn a hac]
  exact signedEvenKernelCharacter_value N negative hodd a hac ha

end Ostmann

end OAI
