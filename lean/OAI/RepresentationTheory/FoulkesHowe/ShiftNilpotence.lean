import Mathlib

namespace OAI

noncomputable section

namespace Problem346

section Derivation

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- A derivation is locally nilpotent at a product when it is locally nilpotent
at each factor. The deliberately loose exponent avoids binomial coefficients. -/
theorem derivation_pow_mul_eq_zero (D : Derivation R A A)
    (m n : ℕ) (a b : A)
    (ha : (D.toLinearMap ^ m) a = 0)
    (hb : (D.toLinearMap ^ n) b = 0) :
    (D.toLinearMap ^ (m + n)) (a * b) = 0 := by
  induction m generalizing n a b with
  | zero =>
      simp only [pow_zero, Module.End.one_apply] at ha
      simp [ha]
  | succ m hm =>
      induction n generalizing a b with
      | zero =>
          simp only [pow_zero, Module.End.one_apply] at hb
          simp [hb]
      | succ n hn =>
          have hDa : (D.toLinearMap ^ m) (D a) = 0 := by
            rw [pow_succ, Module.End.mul_apply] at ha
            exact ha
          have hDb : (D.toLinearMap ^ n) (D b) = 0 := by
            rw [pow_succ, Module.End.mul_apply] at hb
            exact hb
          have hp := hm (n + 1) (D a) b hDa hb
          have hq := hn a (D b) ha hDb
          have he : m + 1 + (n + 1) = (m + (n + 1)) + 1 := by omega
          rw [he, pow_succ, Module.End.mul_apply]
          change (D.toLinearMap ^ (m + (n + 1))) (D (a * b)) = 0
          rw [D.leibniz, map_add]
          have hp' : (D.toLinearMap ^ (m + (n + 1))) (b * D a) = 0 := by
            simpa only [mul_comm] using hp
          have hq' : (D.toLinearMap ^ (m + (n + 1))) (a * D b) = 0 := by
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq
          simp only [smul_eq_mul, hp', hq', add_zero]


/-- Pointwise local nilpotence of a derivation is closed under addition. -/
theorem derivation_exists_pow_add_eq_zero (D : Derivation R A A) (a b : A)
    (ha : ∃ m : ℕ, (D.toLinearMap ^ m) a = 0)
    (hb : ∃ n : ℕ, (D.toLinearMap ^ n) b = 0) :
    ∃ n : ℕ, (D.toLinearMap ^ n) (a + b) = 0 := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  refine ⟨m + n, ?_⟩
  rw [map_add, Module.End.pow_map_zero_of_le (Nat.le_add_right m n) hm,
    Module.End.pow_map_zero_of_le (Nat.le_add_left n m) hn, add_zero]

/-- Pointwise local nilpotence of a derivation is closed under multiplication. -/
theorem derivation_exists_pow_mul_eq_zero (D : Derivation R A A) (a b : A)
    (ha : ∃ m : ℕ, (D.toLinearMap ^ m) a = 0)
    (hb : ∃ n : ℕ, (D.toLinearMap ^ n) b = 0) :
    ∃ n : ℕ, (D.toLinearMap ^ n) (a * b) = 0 := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  exact ⟨m + n, derivation_pow_mul_eq_zero D m n a b hm hn⟩

end Derivation

section MvPolynomial

variable {R σ : Type*} [CommRing R]

/-- Local nilpotence on polynomial generators implies local nilpotence everywhere.
No finiteness assumption on the variable type is needed, so spectator variables
can be retained without changing the argument. -/
theorem mvPolynomial_derivation_locally_nilpotent
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (hX : ∀ i : σ, ∃ n : ℕ, (D.toLinearMap ^ n) (MvPolynomial.X i) = 0)
    (f : MvPolynomial σ R) : ∃ n : ℕ, (D.toLinearMap ^ n) f = 0 := by
  induction f using MvPolynomial.induction_on with
  | C r =>
      refine ⟨1, ?_⟩
      rw [pow_one]
      exact MvPolynomial.derivation_C D r
  | add p q hp hq =>
      exact derivation_exists_pow_add_eq_zero D p q hp hq
  | mul_X p i hp =>
      exact derivation_exists_pow_mul_eq_zero D p (MvPolynomial.X i) hp (hX i)

/-- The square-zero-on-generators criterion used for directional shifts. -/
theorem mvPolynomial_derivation_locally_nilpotent_of_square_zero_X
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (hX : ∀ i : σ, D (D (MvPolynomial.X i)) = 0)
    (f : MvPolynomial σ R) : ∃ n : ℕ, (D.toLinearMap ^ n) f = 0 := by
  apply mvPolynomial_derivation_locally_nilpotent D _ f
  intro i
  refine ⟨2, ?_⟩
  rw [pow_two, Module.End.mul_apply]
  exact hX i

end MvPolynomial

end Problem346

end

end OAI
