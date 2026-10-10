import OAI.NumberTheory.Ostmann.QuadraticSieve.SquarefreeJacobiCharacter

namespace OAI

/-! # Reciprocity formulas for the sign and two-part of a kernel -/

namespace Ostmann

theorem jacobi_odd_numerator_formula (N a : ℕ) (hN : Odd N) (ha : Odd a) :
    jacobiSym (N : ℤ) a = jacobiSym (a : ℤ) N * (ZMod.χ₄ a) ^ (N / 2) := by
  have h := jacobiSym.quadratic_reciprocity' hN ha
  rw [qrSign.symm ha hN, qrSign.neg_one_pow hN ha] at h
  rw [ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp ha), ← pow_mul]
  rw [Nat.mul_comm (a / 2) (N / 2)]
  exact h.trans (mul_comm _ _)

theorem jacobi_negative_odd_formula (N a : ℕ) (hN : Odd N) (ha : Odd a) :
    jacobiSym (-(N : ℤ)) a = jacobiSym (a : ℤ) N * (ZMod.χ₄ a) ^ (N / 2 + 1) := by
  rw [jacobiSym.neg _ ha, jacobi_odd_numerator_formula N a hN ha, pow_succ]
  ring

theorem jacobi_twice_odd_formula (N a : ℕ) (hN : Odd N) (ha : Odd a) :
    jacobiSym (2 * (N : ℤ)) a =
      jacobiSym (a : ℤ) N * (ZMod.χ₄ a) ^ (N / 2) * ZMod.χ₈ a := by
  rw [jacobiSym.mul_left, jacobiSym.at_two ha, jacobi_odd_numerator_formula N a hN ha]
  ring

theorem jacobi_negative_twice_odd_formula (N a : ℕ) (hN : Odd N) (ha : Odd a) :
    jacobiSym (-(2 * (N : ℤ))) a =
      jacobiSym (a : ℤ) N * (ZMod.χ₄ a) ^ (N / 2 + 1) * ZMod.χ₈ a := by
  rw [jacobiSym.neg _ ha, jacobi_twice_odd_formula N a hN ha, pow_succ]
  ring

noncomputable def realFourCharacter : DirichletCharacter ℝ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℝ)

noncomputable def realEightCharacter : DirichletCharacter ℝ 8 :=
  ZMod.χ₈.ringHomComp (Int.castRingHom ℝ)

@[simp] theorem realFourCharacter_apply (a : ℕ) : realFourCharacter (a : ZMod 4) = (ZMod.χ₄ a : ℝ) := by
  rfl

@[simp] theorem realEightCharacter_apply (a : ℕ) : realEightCharacter (a : ZMod 8) = (ZMod.χ₈ a : ℝ) := by
  rfl

/-- The odd-part character, with the parity twist prescribed by reciprocity. -/
noncomputable def signedOddKernelCharacter (N : ℕ) [NeZero N] (negative : Bool) :
    DirichletCharacter ℝ (Nat.lcm N 4) :=
  DirichletCharacter.mul (jacobiCharacter N)
    (realFourCharacter ^ (N / 2 + if negative then 1 else 0))

theorem signedOddKernelCharacter_value (N : ℕ) [NeZero N] (negative : Bool)
    (hN : Odd N) (a : ℕ) (ha : a.Coprime (Nat.lcm N 4)) (haodd : Odd a) :
    signedOddKernelCharacter N negative (a : ZMod (Nat.lcm N 4)) =
      (jacobiSym (if negative then -(N : ℤ) else (N : ℤ)) a : ℝ) := by
  have hcop : IsCoprime (a : ℤ) (Nat.lcm N 4) := Nat.isCoprime_iff_coprime.mpr ha
  have hunit : IsUnit (a : ZMod 4) := (ZMod.isUnit_iff_coprime a 4).mpr
    (ha.of_dvd_right (Nat.dvd_lcm_right N 4))
  rw [← Int.cast_natCast (R := ZMod (Nat.lcm N 4))]
  rw [signedOddKernelCharacter, DirichletCharacter.mul, MulChar.mul_apply,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop,
    jacobiCharacter_intCast]
  have hpow (k : ℕ) : (realFourCharacter ^ k) ((a : ℤ) : ZMod 4) = (ZMod.χ₄ a : ℝ) ^ k := by
    rw [Int.cast_natCast, ← hunit.unit_spec, MulChar.pow_apply_coe]
    rfl
  rw [hpow]
  cases negative
  · simp only [Bool.false_eq_true, ite_false, add_zero]
    exact_mod_cast (jacobi_odd_numerator_formula N a hN haodd).symm
  · simp only [ite_true]
    exact_mod_cast (jacobi_negative_odd_formula N a hN haodd).symm

/-- The conductor-eight twist accounts for both the sign and the factor two. -/
noncomputable def evenKernelTwist (k : ℕ) : DirichletCharacter ℝ 8 :=
  (realFourCharacter ^ k).changeLevel (by decide : 4 ∣ 8) * realEightCharacter

theorem evenKernelTwist_value (k a : ℕ) (ha : a.Coprime 8) :
    evenKernelTwist k (a : ZMod 8) = (ZMod.χ₄ a : ℝ) ^ k * (ZMod.χ₈ a : ℝ) := by
  have hcop : IsCoprime (a : ℤ) 8 := Nat.isCoprime_iff_coprime.mpr ha
  have hunit : IsUnit (a : ZMod 4) := (ZMod.isUnit_iff_coprime a 4).mpr
    (ha.of_dvd_right (by decide : 4 ∣ 8))
  rw [evenKernelTwist, MulChar.mul_apply, ← Int.cast_natCast (R := ZMod 8),
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop, Int.cast_natCast,
    ← hunit.unit_spec, MulChar.pow_apply_coe, hunit.unit_spec]
  rfl

noncomputable def signedEvenKernelCharacter (N : ℕ) [NeZero N] (negative : Bool) :
    DirichletCharacter ℝ (Nat.lcm N 8) :=
  DirichletCharacter.mul (jacobiCharacter N)
    (evenKernelTwist (N / 2 + if negative then 1 else 0))

theorem signedEvenKernelCharacter_value (N : ℕ) [NeZero N] (negative : Bool)
    (hN : Odd N) (a : ℕ) (ha : a.Coprime (Nat.lcm N 8)) (haodd : Odd a) :
    signedEvenKernelCharacter N negative (a : ZMod (Nat.lcm N 8)) =
      (jacobiSym (if negative then -(2 * (N : ℤ)) else 2 * (N : ℤ)) a : ℝ) := by
  have hcop : IsCoprime (a : ℤ) (Nat.lcm N 8) := Nat.isCoprime_iff_coprime.mpr ha
  rw [← Int.cast_natCast (R := ZMod (Nat.lcm N 8)), signedEvenKernelCharacter,
    DirichletCharacter.mul, MulChar.mul_apply,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop, jacobiCharacter_intCast,
    Int.cast_natCast, evenKernelTwist_value _ _ (ha.of_dvd_right (Nat.dvd_lcm_right N 8))]
  rw [← mul_assoc]
  cases negative
  · simp only [Bool.false_eq_true, ite_false, add_zero]
    exact_mod_cast (jacobi_twice_odd_formula N a hN haodd).symm
  · simp only [ite_true]
    exact_mod_cast (jacobi_negative_twice_odd_formula N a hN haodd).symm

end Ostmann

end OAI
