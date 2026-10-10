import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import OAI.NumberTheory.Catalan.Estimates.FixedTypedChebyshevT39To41

namespace OAI


noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevU_typed_29 :
    Chebyshev.U ℤ 29 = fixedChebyshevUData_29 := by
  calc
    Chebyshev.U ℤ 29 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_28 - fixedChebyshevUData_27 :=
      fixedTyped_chebyshevU_link 27 28 29 fixedChebyshevUData_27 fixedChebyshevUData_28
        (by decide) (by decide) fixed_chebyshevU_typed_27 fixed_chebyshevU_typed_28
    _ = fixedChebyshevUData_29 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_28, fixedChebyshevUData_27, fixedChebyshevUData_29, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_28, fixedChebyshevUData_27, fixedChebyshevUData_29, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 29
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 29, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 29 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [ite_eq_right, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_30 :
    Chebyshev.U ℤ 30 = fixedChebyshevUData_30 := by
  calc
    Chebyshev.U ℤ 30 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_29 - fixedChebyshevUData_28 :=
      fixedTyped_chebyshevU_link 28 29 30 fixedChebyshevUData_28 fixedChebyshevUData_29
        (by decide) (by decide) fixed_chebyshevU_typed_28 fixed_chebyshevU_typed_29
    _ = fixedChebyshevUData_30 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_29, fixedChebyshevUData_28, fixedChebyshevUData_30, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_29, fixedChebyshevUData_28, fixedChebyshevUData_30, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 30
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 30, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 30 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [ite_eq_right, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_31 :
    Chebyshev.U ℤ 31 = fixedChebyshevUData_31 := by
  calc
    Chebyshev.U ℤ 31 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_30 - fixedChebyshevUData_29 :=
      fixedTyped_chebyshevU_link 29 30 31 fixedChebyshevUData_29 fixedChebyshevUData_30
        (by decide) (by decide) fixed_chebyshevU_typed_29 fixed_chebyshevU_typed_30
    _ = fixedChebyshevUData_31 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_30, fixedChebyshevUData_29, fixedChebyshevUData_31, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_30, fixedChebyshevUData_29, fixedChebyshevUData_31, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 31
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 31, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 31 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [ite_eq_right, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_32 :
    Chebyshev.U ℤ 32 = fixedChebyshevUData_32 := by
  calc
    Chebyshev.U ℤ 32 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_31 - fixedChebyshevUData_30 :=
      fixedTyped_chebyshevU_link 30 31 32 fixedChebyshevUData_30 fixedChebyshevUData_31
        (by decide) (by decide) fixed_chebyshevU_typed_30 fixed_chebyshevU_typed_31
    _ = fixedChebyshevUData_32 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_31, fixedChebyshevUData_30, fixedChebyshevUData_32, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_31, fixedChebyshevUData_30, fixedChebyshevUData_32, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 32
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 32, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 32 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [ite_eq_right, mul_zero, sub_zero, add_zero]

end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevU_typed_33 :
    Chebyshev.U ℤ 33 = fixedChebyshevUData_33 := by
  calc
    Chebyshev.U ℤ 33 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_32 - fixedChebyshevUData_31 :=
      fixedTyped_chebyshevU_link 31 32 33 fixedChebyshevUData_31 fixedChebyshevUData_32
        (by decide) (by decide) fixed_chebyshevU_typed_31 fixed_chebyshevU_typed_32
    _ = fixedChebyshevUData_33 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_32, fixedChebyshevUData_31, fixedChebyshevUData_33, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_32, fixedChebyshevUData_31, fixedChebyshevUData_33, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 33
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 33, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 33 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [ite_eq_right, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_34 :
    Chebyshev.U ℤ 34 = fixedChebyshevUData_34 := by
  calc
    Chebyshev.U ℤ 34 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_33 - fixedChebyshevUData_32 :=
      fixedTyped_chebyshevU_link 32 33 34 fixedChebyshevUData_32 fixedChebyshevUData_33
        (by decide) (by decide) fixed_chebyshevU_typed_32 fixed_chebyshevU_typed_33
    _ = fixedChebyshevUData_34 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_33, fixedChebyshevUData_32, fixedChebyshevUData_34, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_33, fixedChebyshevUData_32, fixedChebyshevUData_34, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 34
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 34, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 34 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [ite_eq_right, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_35 :
    Chebyshev.U ℤ 35 = fixedChebyshevUData_35 := by
  calc
    Chebyshev.U ℤ 35 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_34 - fixedChebyshevUData_33 :=
      fixedTyped_chebyshevU_link 33 34 35 fixedChebyshevUData_33 fixedChebyshevUData_34
        (by decide) (by decide) fixed_chebyshevU_typed_33 fixed_chebyshevU_typed_34
    _ = fixedChebyshevUData_35 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_34, fixedChebyshevUData_33, fixedChebyshevUData_35, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_34, fixedChebyshevUData_33, fixedChebyshevUData_35, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 35
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 35, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 35 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [ite_eq_right, mul_zero, sub_zero, add_zero]

end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevU_typed_36 :
    Chebyshev.U ℤ 36 = fixedChebyshevUData_36 := by
  calc
    Chebyshev.U ℤ 36 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_35 - fixedChebyshevUData_34 :=
      fixedTyped_chebyshevU_link 34 35 36 fixedChebyshevUData_34 fixedChebyshevUData_35
        (by decide) (by decide) fixed_chebyshevU_typed_34 fixed_chebyshevU_typed_35
    _ = fixedChebyshevUData_36 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_35, fixedChebyshevUData_34, fixedChebyshevUData_36, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_35, fixedChebyshevUData_34, fixedChebyshevUData_36, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 36
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 36, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 36 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [ite_eq_right, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_37 :
    Chebyshev.U ℤ 37 = fixedChebyshevUData_37 := by
  calc
    Chebyshev.U ℤ 37 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_36 - fixedChebyshevUData_35 :=
      fixedTyped_chebyshevU_link 35 36 37 fixedChebyshevUData_35 fixedChebyshevUData_36
        (by decide) (by decide) fixed_chebyshevU_typed_35 fixed_chebyshevU_typed_36
    _ = fixedChebyshevUData_37 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_36, fixedChebyshevUData_35, fixedChebyshevUData_37, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_36, fixedChebyshevUData_35, fixedChebyshevUData_37, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 37
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 37, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 37 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [ite_eq_right, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_38 :
    Chebyshev.U ℤ 38 = fixedChebyshevUData_38 := by
  calc
    Chebyshev.U ℤ 38 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_37 - fixedChebyshevUData_36 :=
      fixedTyped_chebyshevU_link 36 37 38 fixedChebyshevUData_36 fixedChebyshevUData_37
        (by decide) (by decide) fixed_chebyshevU_typed_36 fixed_chebyshevU_typed_37
    _ = fixedChebyshevUData_38 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_37, fixedChebyshevUData_36, fixedChebyshevUData_38, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_37, fixedChebyshevUData_36, fixedChebyshevUData_38, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 38
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 38, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 38 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [ite_eq_right, mul_zero, sub_zero, add_zero]

end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevU_typed_39 :
    Chebyshev.U ℤ 39 = fixedChebyshevUData_39 := by
  calc
    Chebyshev.U ℤ 39 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_38 - fixedChebyshevUData_37 :=
      fixedTyped_chebyshevU_link 37 38 39 fixedChebyshevUData_37 fixedChebyshevUData_38
        (by decide) (by decide) fixed_chebyshevU_typed_37 fixed_chebyshevU_typed_38
    _ = fixedChebyshevUData_39 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_38, fixedChebyshevUData_37, fixedChebyshevUData_39, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_38, fixedChebyshevUData_37, fixedChebyshevUData_39, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 39
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 39, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 39 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [ite_eq_right, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_40 :
    Chebyshev.U ℤ 40 = fixedChebyshevUData_40 := by
  calc
    Chebyshev.U ℤ 40 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_39 - fixedChebyshevUData_38 :=
      fixedTyped_chebyshevU_link 38 39 40 fixedChebyshevUData_38 fixedChebyshevUData_39
        (by decide) (by decide) fixed_chebyshevU_typed_38 fixed_chebyshevU_typed_39
    _ = fixedChebyshevUData_40 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_39, fixedChebyshevUData_38, fixedChebyshevUData_40, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_39, fixedChebyshevUData_38, fixedChebyshevUData_40, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 40
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 40, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 40 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [ite_eq_right, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_41 :
    Chebyshev.U ℤ 41 = fixedChebyshevUData_41 := by
  calc
    Chebyshev.U ℤ 41 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_40 - fixedChebyshevUData_39 :=
      fixedTyped_chebyshevU_link 39 40 41 fixedChebyshevUData_39 fixedChebyshevUData_40
        (by decide) (by decide) fixed_chebyshevU_typed_39 fixed_chebyshevU_typed_40
    _ = fixedChebyshevUData_41 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_40, fixedChebyshevUData_39, fixedChebyshevUData_41, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_40, fixedChebyshevUData_39, fixedChebyshevUData_41, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 41
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 41, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 41 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [ite_eq_right, mul_zero, sub_zero, add_zero]

end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevT_typed_42 :
    Chebyshev.T ℤ 42 = fixedChebyshevTData_42 := by
  calc
    Chebyshev.T ℤ 42 =
        (2 : ℤ[X]) * X * fixedChebyshevTData_41 - fixedChebyshevTData_40 :=
      fixedTyped_chebyshevT_link 40 41 42 fixedChebyshevTData_40 fixedChebyshevTData_41
        (by decide) (by decide) fixed_chebyshevT_typed_40 fixed_chebyshevT_typed_41
    _ = fixedChebyshevTData_42 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_41, fixedChebyshevTData_40, fixedChebyshevTData_42, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_41, fixedChebyshevTData_40, fixedChebyshevTData_42, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 42
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 42, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 42 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [ite_eq_right, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_43 :
    Chebyshev.T ℤ 43 = fixedChebyshevTData_43 := by
  calc
    Chebyshev.T ℤ 43 =
        (2 : ℤ[X]) * X * fixedChebyshevTData_42 - fixedChebyshevTData_41 :=
      fixedTyped_chebyshevT_link 41 42 43 fixedChebyshevTData_41 fixedChebyshevTData_42
        (by decide) (by decide) fixed_chebyshevT_typed_41 fixed_chebyshevT_typed_42
    _ = fixedChebyshevTData_43 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_42, fixedChebyshevTData_41, fixedChebyshevTData_43, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_42, fixedChebyshevTData_41, fixedChebyshevTData_43, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 43
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 43, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 43 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [ite_eq_right, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_44 :
    Chebyshev.T ℤ 44 = fixedChebyshevTData_44 := by
  calc
    Chebyshev.T ℤ 44 =
        (2 : ℤ[X]) * X * fixedChebyshevTData_43 - fixedChebyshevTData_42 :=
      fixedTyped_chebyshevT_link 42 43 44 fixedChebyshevTData_42 fixedChebyshevTData_43
        (by decide) (by decide) fixed_chebyshevT_typed_42 fixed_chebyshevT_typed_43
    _ = fixedChebyshevTData_44 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_43, fixedChebyshevTData_42, fixedChebyshevTData_44, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_43, fixedChebyshevTData_42, fixedChebyshevTData_44, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 44
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 44, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 44 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [ite_eq_right, mul_zero, sub_zero, add_zero]

end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevU_typed_42 :
    Chebyshev.U ℤ 42 = fixedChebyshevUData_42 := by
  calc
    Chebyshev.U ℤ 42 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_41 - fixedChebyshevUData_40 :=
      fixedTyped_chebyshevU_link 40 41 42 fixedChebyshevUData_40 fixedChebyshevUData_41
        (by decide) (by decide) fixed_chebyshevU_typed_40 fixed_chebyshevU_typed_41
    _ = fixedChebyshevUData_42 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_41, fixedChebyshevUData_40, fixedChebyshevUData_42, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_41, fixedChebyshevUData_40, fixedChebyshevUData_42, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 42
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 42, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 42 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [ite_eq_right, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_43 :
    Chebyshev.U ℤ 43 = fixedChebyshevUData_43 := by
  calc
    Chebyshev.U ℤ 43 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_42 - fixedChebyshevUData_41 :=
      fixedTyped_chebyshevU_link 41 42 43 fixedChebyshevUData_41 fixedChebyshevUData_42
        (by decide) (by decide) fixed_chebyshevU_typed_41 fixed_chebyshevU_typed_42
    _ = fixedChebyshevUData_43 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_42, fixedChebyshevUData_41, fixedChebyshevUData_43, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_42, fixedChebyshevUData_41, fixedChebyshevUData_43, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 43
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 43, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 43 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [ite_eq_right, mul_zero, sub_zero, add_zero]

end InternalCatalan

end




noncomputable section
open Polynomial
namespace InternalCatalan

def fixedReversedTData_0 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ)

def fixedReversedTCoeff_0 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0)

theorem fixed_reversedT_typed_data_0 : reversedRow 63 fixedChebyshevTData_0 = fixedReversedTData_0 := by
  simp only [fixedChebyshevTData_0, fixedReversedTData_0]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide)]

theorem fixed_reversedT_typed_coeff_0 (n : ℕ) :
    fixedReversedTData_0.coeff n = fixedReversedTCoeff_0 n := by
  simp only [fixedReversedTData_0, fixedReversedTCoeff_0, coeff_monomial]

theorem fixed_reversedT_typed_tail_0 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_0 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_0, ite_eq_right]

def fixedReversedTData_1 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (1 : ℤ)

def fixedReversedTCoeff_1 (n : ℕ) : ℤ :=
    (if 61 = n then (1 : ℤ) else 0)

theorem fixed_reversedT_typed_data_1 : reversedRow 63 fixedChebyshevTData_1 = fixedReversedTData_1 := by
  simp only [fixedChebyshevTData_1, fixedReversedTData_1]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 1 (by decide)]

theorem fixed_reversedT_typed_coeff_1 (n : ℕ) :
    fixedReversedTData_1.coeff n = fixedReversedTCoeff_1 n := by
  simp only [fixedReversedTData_1, fixedReversedTCoeff_1, coeff_monomial]

theorem fixed_reversedT_typed_tail_1 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_1 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_1, ite_eq_right]

def fixedReversedTData_2 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (2 : ℤ)

def fixedReversedTCoeff_2 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (2 : ℤ) else 0)

theorem fixed_reversedT_typed_data_2 : reversedRow 63 fixedChebyshevTData_2 = fixedReversedTData_2 := by
  simp only [fixedChebyshevTData_2, fixedReversedTData_2, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (2 : ℤ) 2 (by decide)]

theorem fixed_reversedT_typed_coeff_2 (n : ℕ) :
    fixedReversedTData_2.coeff n = fixedReversedTCoeff_2 n := by
  simp only [fixedReversedTData_2, fixedReversedTCoeff_2, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_2 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_2 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_2, ite_eq_right, add_zero]

def fixedReversedTData_3 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-3 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (4 : ℤ)

def fixedReversedTCoeff_3 (n : ℕ) : ℤ :=
    (if 61 = n then (-3 : ℤ) else 0) +
    (if 59 = n then (4 : ℤ) else 0)

theorem fixed_reversedT_typed_data_3 : reversedRow 63 fixedChebyshevTData_3 = fixedReversedTData_3 := by
  simp only [fixedChebyshevTData_3, fixedReversedTData_3, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-3 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (4 : ℤ) 3 (by decide)]

theorem fixed_reversedT_typed_coeff_3 (n : ℕ) :
    fixedReversedTData_3.coeff n = fixedReversedTCoeff_3 n := by
  simp only [fixedReversedTData_3, fixedReversedTCoeff_3, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_3 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_3 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_3, ite_eq_right, add_zero]

def fixedReversedTData_4 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-8 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (8 : ℤ)

def fixedReversedTCoeff_4 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-8 : ℤ) else 0) +
    (if 58 = n then (8 : ℤ) else 0)

theorem fixed_reversedT_typed_data_4 : reversedRow 63 fixedChebyshevTData_4 = fixedReversedTData_4 := by
  simp only [fixedChebyshevTData_4, fixedReversedTData_4, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-8 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (8 : ℤ) 4 (by decide)]

theorem fixed_reversedT_typed_coeff_4 (n : ℕ) :
    fixedReversedTData_4.coeff n = fixedReversedTCoeff_4 n := by
  simp only [fixedReversedTData_4, fixedReversedTCoeff_4, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_4 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_4 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_4, ite_eq_right, add_zero]

def fixedReversedTData_5 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (5 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-20 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (16 : ℤ)

def fixedReversedTCoeff_5 (n : ℕ) : ℤ :=
    (if 61 = n then (5 : ℤ) else 0) +
    (if 59 = n then (-20 : ℤ) else 0) +
    (if 57 = n then (16 : ℤ) else 0)

theorem fixed_reversedT_typed_data_5 : reversedRow 63 fixedChebyshevTData_5 = fixedReversedTData_5 := by
  simp only [fixedChebyshevTData_5, fixedReversedTData_5, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (5 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-20 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (16 : ℤ) 5 (by decide)]

theorem fixed_reversedT_typed_coeff_5 (n : ℕ) :
    fixedReversedTData_5.coeff n = fixedReversedTCoeff_5 n := by
  simp only [fixedReversedTData_5, fixedReversedTCoeff_5, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_5 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_5 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_5, ite_eq_right, add_zero]

def fixedReversedTData_6 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (18 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-48 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (32 : ℤ)

def fixedReversedTCoeff_6 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (18 : ℤ) else 0) +
    (if 58 = n then (-48 : ℤ) else 0) +
    (if 56 = n then (32 : ℤ) else 0)

theorem fixed_reversedT_typed_data_6 : reversedRow 63 fixedChebyshevTData_6 = fixedReversedTData_6 := by
  simp only [fixedChebyshevTData_6, fixedReversedTData_6, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (18 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-48 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (32 : ℤ) 6 (by decide)]

theorem fixed_reversedT_typed_coeff_6 (n : ℕ) :
    fixedReversedTData_6.coeff n = fixedReversedTCoeff_6 n := by
  simp only [fixedReversedTData_6, fixedReversedTCoeff_6, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_6 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_6 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_6, ite_eq_right, add_zero]

def fixedReversedTData_7 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-7 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (56 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-112 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (64 : ℤ)

def fixedReversedTCoeff_7 (n : ℕ) : ℤ :=
    (if 61 = n then (-7 : ℤ) else 0) +
    (if 59 = n then (56 : ℤ) else 0) +
    (if 57 = n then (-112 : ℤ) else 0) +
    (if 55 = n then (64 : ℤ) else 0)

theorem fixed_reversedT_typed_data_7 : reversedRow 63 fixedChebyshevTData_7 = fixedReversedTData_7 := by
  simp only [fixedChebyshevTData_7, fixedReversedTData_7, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-7 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (56 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-112 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (64 : ℤ) 7 (by decide)]

theorem fixed_reversedT_typed_coeff_7 (n : ℕ) :
    fixedReversedTData_7.coeff n = fixedReversedTCoeff_7 n := by
  simp only [fixedReversedTData_7, fixedReversedTCoeff_7, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_7 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_7 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_7, ite_eq_right, add_zero]

end InternalCatalan

end

end OAI
