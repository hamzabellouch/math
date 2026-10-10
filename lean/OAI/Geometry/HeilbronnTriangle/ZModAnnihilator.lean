import Mathlib

namespace OAI


namespace Problem355

theorem zmod_card_mul_eq_zero (m d : ℕ) [NeZero m] :
    Nat.card {x : ZMod m // (d : ZMod m) * x = 0} = Nat.gcd m d := by
  simpa only [Nat.card_zmod, AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply,
    nsmul_eq_mul] using IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod m) d

theorem zmod_card_mul_eq_zero_of_dvd (m d : ℕ) [NeZero m] (hd : d ∣ m) :
    Nat.card {x : ZMod m // (d : ZMod m) * x = 0} = d := by
  rw [zmod_card_mul_eq_zero, Nat.gcd_eq_right hd]

theorem zmod_card_pow_mul_eq_zero (B k e : ℕ) [NeZero B] (he : e ≤ k) :
    Nat.card {x : ZMod (B ^ k) // (B ^ e : ZMod (B ^ k)) * x = 0} = B ^ e := by
  simpa only [Nat.cast_pow] using
    zmod_card_mul_eq_zero_of_dvd (B ^ k) (B ^ e) (pow_dvd_pow B he)

def matrixFixedDiagonalEquiv {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [Ring R] (d : ι → R) :
    {A : Matrix ι ι R // A * Matrix.diagonal d = Matrix.diagonal d} ≃
      (ι → (j : ι) → {x : R // x * d j = 0}) where
  toFun A i j := ⟨(A.1 - 1) i j, by
    have hzero : (A.1 - 1) * Matrix.diagonal d = 0 := by
      rw [Matrix.sub_mul, A.2, Matrix.one_mul, sub_self]
    simpa only [Matrix.mul_diagonal, Matrix.zero_apply] using
      congrArg (fun M : Matrix ι ι R => M i j) hzero⟩
  invFun f := ⟨(Matrix.of (fun i j => (f i j).1)) + 1, by
    have hzero : (Matrix.of (fun i j => (f i j).1)) * Matrix.diagonal d = 0 := by
      ext i j
      simpa only [Matrix.mul_diagonal, Matrix.zero_apply, Matrix.of_apply] using (f i j).2
    rw [Matrix.add_mul, hzero, Matrix.one_mul, zero_add]⟩
  left_inv A := by
    apply Subtype.ext
    exact sub_add_cancel A.1 1
  right_inv f := by
    funext i j
    apply Subtype.ext
    change ((Matrix.of (fun i j => (f i j).1)) + 1 - 1) i j = (f i j).1
    rw [add_sub_cancel_right]
    rfl

theorem card_matrix_fixed_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) [NeZero m] (d : ι → ℕ) :
    Nat.card {A : Matrix ι ι (ZMod m) //
      A * Matrix.diagonal (fun j => (d j : ZMod m)) =
        Matrix.diagonal (fun j => (d j : ZMod m))} =
      (∏ j, Nat.gcd m (d j)) ^ Fintype.card ι := by
  rw [Nat.card_congr (matrixFixedDiagonalEquiv (fun j => (d j : ZMod m)))]
  rw [Nat.card_fun, Nat.card_pi, Nat.card_eq_fintype_card]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simpa only [mul_comm] using zmod_card_mul_eq_zero m (d j)

theorem card_matrix_fixed_diagonal_three (m D E : ℕ) [NeZero m]
    (hD : D ∣ m) (hE : E ∣ m) :
    Nat.card {A : Matrix (Fin 3) (Fin 3) (ZMod m) //
      A * Matrix.diagonal ![1, (D : ZMod m), (E : ZMod m)] =
        Matrix.diagonal ![1, (D : ZMod m), (E : ZMod m)]} = D ^ 3 * E ^ 3 := by
  have hv : (fun j : Fin 3 => (![1, D, E] j : ZMod m)) =
      ![1, (D : ZMod m), (E : ZMod m)] := by
    funext j
    fin_cases j <;> simp
  have hc := card_matrix_fixed_diagonal (ι := Fin 3) m ![1, D, E]
  rw [hv] at hc
  simpa [Fin.prod_univ_succ, Nat.gcd_eq_right hD, Nat.gcd_eq_right hE,
    mul_pow] using hc

theorem card_unit_matrix_fixed_diagonal_three_le (m D E : ℕ) [NeZero m]
    (hD : D ∣ m) (hE : E ∣ m) :
    Nat.card {A : (Matrix (Fin 3) (Fin 3) (ZMod m))ˣ //
      (A : Matrix (Fin 3) (Fin 3) (ZMod m)) *
          Matrix.diagonal ![1, (D : ZMod m), (E : ZMod m)] =
        Matrix.diagonal ![1, (D : ZMod m), (E : ZMod m)]} ≤ D ^ 3 * E ^ 3 := by
  rw [← card_matrix_fixed_diagonal_three m D E hD hE]
  apply Nat.card_le_card_of_injective (fun A => ⟨(A.1 : Matrix _ _ _), A.2⟩)
  intro A B h
  apply Subtype.ext
  apply Units.ext
  exact congrArg Subtype.val h

end Problem355

end OAI
