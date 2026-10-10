import OAI.NumberTheory.Ostmann.Quadratic.QuadraticPairKernel

namespace OAI

/-! # Unique square-times-squarefree decomposition for the Poisson comparison -/

namespace Ostmann

private theorem exists_quadratic_factor (m : ℕ) :
    ∃ a b : ℕ, a ^ 2 * b = m ∧ Squarefree b := by
  by_cases hm : m = 0
  · exact ⟨0, 1, by simp [hm], squarefree_one⟩
  · obtain ⟨b, a, _, _, he, hs⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero hm)
    exact ⟨a, b, he, hs⟩

noncomputable def quadraticSquarePart (m : ℕ) : ℕ :=
  Classical.choose (exists_quadratic_factor m)

noncomputable def quadraticSquarefreePart (m : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (exists_quadratic_factor m))

 theorem quadraticSquarePart_factor (m : ℕ) :
    quadraticSquarePart m ^ 2 * quadraticSquarefreePart m = m :=
  (Classical.choose_spec (Classical.choose_spec (exists_quadratic_factor m))).1

 theorem quadraticSquarefreePart_squarefree (m : ℕ) :
    Squarefree (quadraticSquarefreePart m) :=
  (Classical.choose_spec (Classical.choose_spec (exists_quadratic_factor m))).2

 theorem quadraticSquarePart_pos {m : ℕ} (hm : 0 < m) : 0 < quadraticSquarePart m := by
  have hh := quadraticSquarePart_factor m
  by_contra h
  have hz : quadraticSquarePart m = 0 := by omega
  simp only [hz, zero_pow (by decide : 2 ≠ 0), zero_mul] at hh
  omega

 theorem quadraticSquarefreePart_pos (m : ℕ) : 0 < quadraticSquarefreePart m :=
  Nat.pos_of_ne_zero (quadraticSquarefreePart_squarefree m).ne_zero

 theorem quadratic_squarefree_factor_unique {a b c d : ℕ}
    (ha : a ≠ 0) (hc : c ≠ 0) (hb : Squarefree b) (hd : Squarefree d)
    (he : a ^ 2 * b = c ^ 2 * d) : a = c ∧ b = d := by
  have hbd : b = d := by
    apply Nat.eq_of_factorization_eq hb.ne_zero hd.ne_zero
    intro p
    have hf := congrArg (fun n : ℕ => n.factorization p) he
    rw [Nat.factorization_mul (pow_ne_zero _ ha) hb.ne_zero,
      Nat.factorization_mul (pow_ne_zero _ hc) hd.ne_zero,
      Nat.factorization_pow, Nat.factorization_pow] at hf
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hf
    have hb' := hb.natFactorization_le_one p
    have hd' := hd.natFactorization_le_one p
    omega
  subst d
  have hs : a ^ 2 = c ^ 2 := mul_right_cancel₀ hb.ne_zero he
  have hac : a = c := by nlinarith
  exact ⟨hac, rfl⟩

 theorem quadraticSquarefreePart_of_squarefree {m : ℕ} (hm : Squarefree m) :
    quadraticSquarePart m = 1 ∧ quadraticSquarefreePart m = m := by
  exact quadratic_squarefree_factor_unique
    (quadraticSquarePart_pos (Nat.pos_of_ne_zero hm.ne_zero)).ne'
    one_ne_zero (quadraticSquarefreePart_squarefree m) hm
    (by simpa using quadraticSquarePart_factor m)

 theorem quadraticSquarefreePart_of_mul_square {a b : ℕ} (ha : a ≠ 0)
    (hb : Squarefree b) : quadraticSquarePart (a ^ 2 * b) = a ∧
      quadraticSquarefreePart (a ^ 2 * b) = b := by
  exact quadratic_squarefree_factor_unique
    (quadraticSquarePart_pos (Nat.pos_of_ne_zero (mul_ne_zero (pow_ne_zero _ ha) hb.ne_zero))).ne'
    ha (quadraticSquarefreePart_squarefree _) hb (quadraticSquarePart_factor _)

 theorem quadraticSquarefreePart_pair {n₁ n₂ : ℕ}
    (h₁ : Squarefree n₁) (h₂ : Squarefree n₂) :
    quadraticSquarePart (n₁ * n₂) = n₁.gcd n₂ ∧
      quadraticSquarefreePart (n₁ * n₂) = quadraticPairKernel n₁ n₂ := by
  rw [← quadraticPairKernel_factor]
  exact quadraticSquarefreePart_of_mul_square
    (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero h₁.ne_zero)).ne'
    (quadraticPairKernel_squarefree h₁ h₂)

end Ostmann

end OAI
