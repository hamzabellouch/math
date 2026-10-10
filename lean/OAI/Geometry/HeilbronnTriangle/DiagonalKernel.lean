import OAI.Geometry.HeilbronnTriangle.ZModAnnihilator

namespace OAI


namespace Problem355.DiagonalKernel

open scoped BigOperators Matrix

variable {R ι : Type*} [Semiring R] [Fintype ι] [DecidableEq ι]

abbrev Kernel (A : Matrix ι ι R) := {x : ι → R // A.mulVec x = 0}

def diagonalKernelEquiv (d : ι → R) :
    Kernel (Matrix.diagonal d) ≃ (∀ i, {x : R // d i * x = 0}) where
  toFun x i := ⟨x.1 i, by
    have h := congrFun x.2 i
    simpa only [Matrix.mulVec_diagonal, Pi.zero_apply] using h⟩
  invFun x := ⟨fun i => (x i).1, by
    funext i
    simpa only [Matrix.mulVec_diagonal, Pi.zero_apply] using (x i).2⟩
  left_inv x := by rfl
  right_inv x := by rfl

def unitMulVecEquiv (Q : (Matrix ι ι R)ˣ) : (ι → R) ≃ (ι → R) where
  toFun := (Q : Matrix ι ι R).mulVec
  invFun := ((Q⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R).mulVec
  left_inv x := by
    rw [Matrix.mulVec_mulVec]
    simp
  right_inv x := by
    rw [Matrix.mulVec_mulVec]
    simp

def changeKernelEquiv (A : Matrix ι ι R) (P Q : (Matrix ι ι R)ˣ) :
    Kernel ((P : Matrix ι ι R) * A * (Q : Matrix ι ι R)) ≃ Kernel A := by
  apply Equiv.subtypeEquiv (unitMulVecEquiv Q)
  intro x
  change (((P : Matrix ι ι R) * A * (Q : Matrix ι ι R)).mulVec x = 0) ↔
    A.mulVec ((Q : Matrix ι ι R).mulVec x) = 0
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact (Matrix.mulVec_injective_of_isUnit P.isUnit).eq_iff' (by simp)

theorem natCard_kernel_change (A : Matrix ι ι R) (P Q : (Matrix ι ι R)ˣ) :
    Nat.card (Kernel ((P : Matrix ι ι R) * A * (Q : Matrix ι ι R))) =
      Nat.card (Kernel A) :=
  Nat.card_congr (changeKernelEquiv A P Q)

section Cardinality

variable [Fintype R] [DecidableEq R]

theorem card_kernel_diagonal (d : ι → R) :
    Fintype.card (Kernel (Matrix.diagonal d)) =
      ∏ i, Fintype.card {x : R // d i * x = 0} := by
  classical
  rw [Fintype.card_congr (diagonalKernelEquiv d), Fintype.card_pi]

theorem card_kernel_change (A : Matrix ι ι R) (P Q : (Matrix ι ι R)ˣ) :
    Fintype.card (Kernel ((P : Matrix ι ι R) * A * (Q : Matrix ι ι R))) =
      Fintype.card (Kernel A) :=
  Fintype.card_congr (changeKernelEquiv A P Q)

theorem card_kernel_diagonal_three (D E : R) :
    Fintype.card (Kernel (Matrix.diagonal ![1, D, E])) =
      Fintype.card {x : R // D * x = 0} *
        Fintype.card {x : R // E * x = 0} := by
  rw [card_kernel_diagonal]
  simp [Fin.prod_univ_succ]
  exact Or.inl rfl

end Cardinality

theorem card_pow_annihilator (B j b : ℕ) [NeZero B] :
    Nat.card {x : ZMod (B ^ j) // (B : ZMod (B ^ j)) ^ b * x = 0} =
      B ^ min b j := by
  rcases le_total b j with h | h
  · simpa only [Nat.min_eq_left h] using zmod_card_pow_mul_eq_zero B j b h
  · simpa only [Nat.cast_pow, Nat.gcd_eq_left (pow_dvd_pow B h),
      Nat.min_eq_right h] using zmod_card_mul_eq_zero (B ^ j) (B ^ b)

theorem card_kernel_diagonal_prime_power (B j b e : ℕ) [NeZero B]
    (hje : j ≤ e) :
    Nat.card (Kernel (Matrix.diagonal
      ![1, (B : ZMod (B ^ j)) ^ b, (B : ZMod (B ^ j)) ^ e])) =
        B ^ (j + min b j) := by
  classical
  rw [Nat.card_eq_fintype_card, card_kernel_diagonal_three,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    card_pow_annihilator, card_pow_annihilator,
    Nat.min_eq_right hje, pow_add]
  exact Nat.mul_comm _ _

theorem card_kernel_diagonal_prime_power_density (B j b e : ℕ) [NeZero B]
    (hje : j ≤ e) :
    Nat.card (Kernel (Matrix.diagonal
      ![1, (B : ZMod (B ^ j)) ^ b, (B : ZMod (B ^ j)) ^ e])) *
          B ^ (j + (j - b)) = (B ^ j) ^ 3 := by
  rw [card_kernel_diagonal_prime_power B j b e hje, ← pow_add, ← pow_mul]
  congr 1
  omega

theorem card_kernel_prime_power_density (B j b e : ℕ) [NeZero B]
    (hje : j ≤ e) (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ j)))
    (P Q : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ j)))ˣ)
    (hC : C = (P : Matrix _ _ _) *
      Matrix.diagonal ![1, (B : ZMod (B ^ j)) ^ b, (B : ZMod (B ^ j)) ^ e] *
        (Q : Matrix _ _ _)) :
    Nat.card (Kernel C) * B ^ (j + (j - b)) = (B ^ j) ^ 3 := by
  rw [hC, natCard_kernel_change]
  exact card_kernel_diagonal_prime_power_density B j b e hje

theorem card_kernel_reduction_density (B k j b e : ℕ) [NeZero B]
    (hjk : j ≤ k) (hje : j ≤ e)
    (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
    (P Q : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))ˣ)
    (hC : C = (P : Matrix _ _ _) *
      Matrix.diagonal ![1, (B : ZMod (B ^ k)) ^ b, (B : ZMod (B ^ k)) ^ e] *
        (Q : Matrix _ _ _)) :
    Nat.card (Kernel (C.map
      (ZMod.castHom (pow_dvd_pow B hjk) (ZMod (B ^ j))))) *
        B ^ (j + (j - b)) = (B ^ j) ^ 3 := by
  let f : ZMod (B ^ k) →+* ZMod (B ^ j) :=
    ZMod.castHom (pow_dvd_pow B hjk) (ZMod (B ^ j))
  have hd : (Matrix.diagonal
      ![1, (B : ZMod (B ^ k)) ^ b, (B : ZMod (B ^ k)) ^ e]).map f =
      Matrix.diagonal ![1, (B : ZMod (B ^ j)) ^ b, (B : ZMod (B ^ j)) ^ e] := by
    ext i l
    by_cases h : i = l
    · subst l
      fin_cases i <;> simp
    · simp [h]
  apply card_kernel_prime_power_density B j b e hje (C.map f)
    (Units.map f.mapMatrix.toMonoidHom P) (Units.map f.mapMatrix.toMonoidHom Q)
  change C.map f = (P : Matrix _ _ _).map f *
    Matrix.diagonal ![1, (B : ZMod (B ^ j)) ^ b, (B : ZMod (B ^ j)) ^ e] *
      (Q : Matrix _ _ _).map f
  simpa only [Matrix.map_mul, hd] using congrArg (fun A => A.map f) hC

end Problem355.DiagonalKernel

end OAI
