import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalBounds

namespace OAI

section

namespace KS.W30

def prependLinear {n : ℕ} (c y : Fin n → ℚ) : Fin (n + 1) → ℚ :=
  Fin.cons (∑ i, c i * y i) y

theorem natAbs_sum_le {n : ℕ} (z : Fin n → ℤ) :
    (∑ i, z i).natAbs ≤ ∑ i, (z i).natAbs := by
  have h := Finset.abs_sum_le_sum_abs z Finset.univ
  have hcast : ((∑ i, z i).natAbs : ℤ) ≤ ((∑ i, (z i).natAbs : ℕ) : ℤ) := by
    simpa only [Nat.cast_sum, Int.natCast_natAbs] using h
  exact_mod_cast hcast

theorem prependLinear_common_representation {n : ℕ} (c y : Fin n → ℚ)
    (C D : ℕ) (hC : C ≠ 0) (P Z : Fin n → ℤ)
    (hc : ∀ i, c i = (P i : ℚ) / C) (hy : ∀ i, y i = (Z i : ℚ) / D) :
    let Z' : Fin (n + 1) → ℤ := Fin.cons (∑ i, P i * Z i) (fun i => (C : ℤ) * Z i)
    ∀ i, prependLinear c y i = (Z' i : ℚ) / (D * C : ℕ) := by
  dsimp only
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change (∑ i, c i * y i) = ((∑ i, P i * Z i : ℤ) : ℚ) / (D * C : ℕ)
    simp only [Int.cast_sum]
    rw [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [hc, hy, div_mul_div_comm]
    simp only [Int.cast_mul, Nat.cast_mul, mul_comm (D : ℚ) (C : ℚ), div_eq_mul_inv]
  · change y j = (((C : ℤ) * Z j : ℤ) : ℚ) / (D * C : ℕ)
    rw [hy]
    symm
    simpa only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul,
      mul_comm (D : ℚ) (C : ℚ)] using
      (mul_div_mul_left (Z j : ℚ) (D : ℚ) (Nat.cast_ne_zero.mpr hC : (C : ℚ) ≠ 0))

theorem prependLinear_common_height {n : ℕ} (c y : Fin n → ℚ) (H E : ℕ)
    (hcnum : ∀ i, (c i).num.natAbs ≤ 2 ^ H)
    (hcden : ∀ i, (c i).den ≤ 2 ^ H)
    (D : ℕ) (hD : 0 < D) (hDb : D ≤ 2 ^ E) (Z : Fin n → ℤ)
    (hy : ∀ i, y i = (Z i : ℚ) / D) (hZ : ∀ i, (Z i).natAbs ≤ 2 ^ E) :
    let E' := E + (n + 1) * H + n + 1
    ∃ D' : ℕ, 0 < D' ∧ D' ≤ 2 ^ E' ∧
      ∃ Z' : Fin (n + 1) → ℤ,
        (∀ i, prependLinear c y i = (Z' i : ℚ) / D') ∧
        ∀ i, (Z' i).natAbs ≤ 2 ^ E' := by
  let R : Matrix (Fin 1) (Fin n) ℚ := fun _ i => c i
  let C := R.den
  let P : Fin n → ℤ := fun i => R.num 0 i
  let E' := E + (n + 1) * H + n + 1
  have hC : 0 < C := Nat.pos_of_ne_zero R.den_ne_zero
  have hCb : C ≤ 2 ^ (H * n) := by
    simpa [C] using matrix_den_le_two_pow R H (fun _ i => hcden i)
  have hPb : ∀ i, (P i).natAbs ≤ 2 ^ (H * n + H) := by
    intro i
    simpa [P] using cleared_num_le_two_pow R H
      (fun _ i => hcnum i) (fun _ i => hcden i) 0 i
  have hc : ∀ i, c i = (P i : ℚ) / C := by
    intro i
    exact (Matrix.num_div_den R 0 i).symm
  have hE : E' = E + H * n + H + n + 1 := by dsimp [E']; ring
  have hDen : D * C ≤ 2 ^ E' := by
    calc
      D * C ≤ 2 ^ E * 2 ^ (H * n) := Nat.mul_le_mul hDb hCb
      _ = 2 ^ (E + H * n) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ E' := Nat.pow_le_pow_right (by decide : 0 < 2) (by rw [hE]; omega)
  have hProd : ∀ i, (P i * Z i).natAbs ≤ 2 ^ (H * n + H + E) := by
    intro i
    rw [Int.natAbs_mul, pow_add]
    exact Nat.mul_le_mul (hPb i) (hZ i)
  have hHead : (∑ i, P i * Z i).natAbs ≤ 2 ^ E' := by
    calc
      (∑ i, P i * Z i).natAbs ≤ ∑ i, (P i * Z i).natAbs := natAbs_sum_le _
      _ ≤ ∑ _i : Fin n, 2 ^ (H * n + H + E) := Finset.sum_le_sum (fun i _ => hProd i)
      _ = n * 2 ^ (H * n + H + E) := by simp
      _ ≤ 2 ^ n * 2 ^ (H * n + H + E) :=
        Nat.mul_le_mul_right _ (Nat.le_of_lt n.lt_two_pow_self)
      _ = 2 ^ (n + (H * n + H + E)) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ E' := Nat.pow_le_pow_right (by decide : 0 < 2) (by rw [hE]; omega)
  have hTail : ∀ i, ((C : ℤ) * Z i).natAbs ≤ 2 ^ E' := by
    intro i
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    calc
      C * (Z i).natAbs ≤ 2 ^ (H * n) * 2 ^ E := Nat.mul_le_mul hCb (hZ i)
      _ = 2 ^ (H * n + E) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ E' := Nat.pow_le_pow_right (by decide : 0 < 2) (by rw [hE]; omega)
  refine ⟨D * C, Nat.mul_pos hD hC, hDen,
    Fin.cons (∑ i, P i * Z i) (fun i => (C : ℤ) * Z i), ?_, ?_⟩
  · exact prependLinear_common_representation c y C D (Nat.ne_of_gt hC) P Z hc hy
  · intro i
    exact Fin.cases hHead hTail i

end KS.W30

end

end OAI
