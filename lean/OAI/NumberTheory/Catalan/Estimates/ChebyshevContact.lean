import Mathlib.Algebra.BigOperators.Intervals
import OAI.NumberTheory.Catalan.Analysis.ContactSeries
import OAI.NumberTheory.Catalan.Determinants.RealColumnDeterminant

namespace OAI


noncomputable section

open Polynomial

namespace InternalCatalan

def centralCoefficientMap (m : ℤ) (k : ℕ) : ℚ →ₗ[ℚ] ℚ where
  toFun a := a * centralCoeffKernel ((k : ℤ) - m)
  map_add' a b := by ring
  map_smul' a b := by simp only [smul_eq_mul, RingHom.id_apply]; ring

def centralFunctional (m : ℤ) : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum (centralCoefficientMap m)

@[simp] theorem centralFunctional_monomial (m : ℤ) (k : ℕ) (a : ℚ) :
    centralFunctional m (monomial k a) = a * centralCoeffKernel ((k : ℤ) - m) := by
  simp [centralFunctional, Polynomial.lsum_apply, Polynomial.sum_monomial_index,
    centralCoefficientMap]

theorem centralFunctional_C_mul (m : ℤ) (a : ℚ) (P : ℚ[X]) :
    centralFunctional m (Polynomial.C a * P) = a * centralFunctional m P := by
  rw [← smul_eq_C_mul, (centralFunctional m).map_smul]
  rfl

theorem centralFunctional_X_mul (m : ℤ) (P : ℚ[X]) :
    centralFunctional m (X * P) = centralFunctional (m - 1) P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [mul_add, map_add, hP, hQ]
  | monomial k a =>
      rw [X_mul_monomial, centralFunctional_monomial, centralFunctional_monomial]
      congr 2
      push_cast
      omega

theorem centralFunctional_stein (P : ℚ[X]) :
    centralFunctional 0 ((1 - X ^ 2) * derivative P) =
      centralFunctional 0 (X * P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [mul_add, map_add, hP, hQ]
  | monomial k a =>
      cases k with
      | zero =>
          rw [X_mul_monomial]
          simp [centralCoeffKernel]
      | succ k =>
          rw [derivative_monomial_succ, sub_mul, one_mul, X_pow_mul_monomial,
            X_mul_monomial, map_sub]
          simp only [centralFunctional_monomial, sub_zero]
          have hs := centralCoeffKernel_nat_step k
          have hscaled := congrArg (fun z : ℚ => a * z) hs
          push_cast at hscaled ⊢
          norm_num only [add_assoc, Int.reduceAdd] at hscaled ⊢
          nlinarith only [hscaled]

theorem centralFunctional_T_zero (d : ℕ) (hd : 0 < d) :
    centralFunctional 0 (Chebyshev.T ℚ (d : ℤ)) = 0 := by
  have hode := congrArg (centralFunctional 0)
    (Chebyshev.one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T (R := ℚ) (d : ℤ))
  have hstein := centralFunctional_stein (derivative (Chebyshev.T ℚ (d : ℤ)))
  have hcast : ((d : ℤ) ^ 2 : ℚ[X]) = Polynomial.C ((d : ℚ) ^ 2) := by
    simp
  simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq] at hode
  rw [map_sub, hcast, centralFunctional_C_mul] at hode
  have hz : (d : ℚ) ^ 2 * centralFunctional 0 (Chebyshev.T ℚ (d : ℤ)) = 0 := by
    linarith only [hode, hstein]
  have hdn : (d : ℚ) ^ 2 ≠ 0 := by positivity
  exact (mul_eq_zero.mp hz).resolve_left hdn

theorem centralFunctional_two_X_mul (m : ℤ) (P : ℚ[X]) :
    centralFunctional m (2 * X * P) = 2 * centralFunctional (m - 1) P := by
  rw [← Polynomial.C_ofNat, mul_assoc,
    centralFunctional_C_mul, centralFunctional_X_mul]

theorem centralFunctional_T_tail (d : ℕ) : ∀ m : ℕ,
    centralFunctional ((m : ℤ) + 1) (Chebyshev.T ℚ (d : ℤ)) =
      (Chebyshev.U ℚ ((d : ℤ) - 1)).coeff m := by
  induction d using Nat.twoStepInduction with
  | zero =>
      intro m
      rw [Nat.cast_zero, Chebyshev.T_zero, zero_sub, Chebyshev.U_neg_one,
        coeff_zero, ← monomial_zero_one, centralFunctional_monomial,
        centralCoeffKernel_of_neg (by omega : ((0 : ℕ) : ℤ) - ((m : ℤ) + 1) < 0)]
      ring
  | one =>
      intro m
      rw [Nat.cast_one, Chebyshev.T_one, sub_self, Chebyshev.U_zero,
        ← monomial_one_one_eq_X, centralFunctional_monomial]
      cases m with
      | zero => norm_num
      | succ m =>
          rw [centralCoeffKernel_of_neg (by omega :
            ((1 : ℕ) : ℤ) - (((m + 1 : ℕ) : ℤ) + 1) < 0)]
          simp [Polynomial.coeff_one]
  | more d ih0 ih1 =>
      intro m
      have hindex : ((d + 2 : ℕ) : ℤ) - 1 = (d : ℤ) + 1 := by omega
      rw [hindex, Nat.cast_add, Nat.cast_ofNat, Chebyshev.T_add_two,
        map_sub, centralFunctional_two_X_mul, Chebyshev.U_add_one]
      rw [coeff_sub, mul_assoc, coeff_ofNat_mul]
      cases m with
      | zero =>
          norm_num only [Nat.cast_zero, zero_add, sub_self]
          have hvan := centralFunctional_T_zero (d + 1) (by omega)
          simp only [Nat.cast_add, Nat.cast_one] at hvan
          have hprev := ih0 0
          simp only [Nat.cast_zero, zero_add] at hprev
          rw [hvan, hprev, coeff_X_mul_zero]
      | succ m =>
          have hmain := ih1 m
          simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hmain
          have hprev := ih0 (m + 1)
          simp only [Nat.cast_add, Nat.cast_one] at hprev
          simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
          rw [hmain, hprev, coeff_X_mul]

end InternalCatalan

end



noncomputable section

open Polynomial

namespace InternalCatalan

private theorem rationalIntCast_apply (z : ℤ) :
    (Int.castRingHom ℚ) z = (z : ℚ) := rfl

theorem centralFunctional_eq_sum_range (m : ℤ) {P : ℚ[X]} {C : ℕ}
    (hP : P.natDegree < C) :
    centralFunctional m P = ∑ u ∈ Finset.range C,
      P.coeff u * centralCoeffKernel ((u : ℤ) - m) := by
  change P.sum (fun u a => a * centralCoeffKernel ((u : ℤ) - m)) = _
  apply Polynomial.sum_eq_of_subset
  · intro u
    simp
  · intro u hu
    apply Finset.mem_range.mpr
    exact lt_of_le_of_lt (Polynomial.le_natDegree_of_ne_zero
      (Polynomial.mem_support_iff.mp hu)) hP

theorem reversedRow_centralFunctional {C j : ℕ} (hj : j < C) (F : ℤ[X])
    (hF : F.natDegree < C) :
    (∑ i ∈ Finset.range C,
      ((reversedRow C F).coeff i : ℚ) * centralCoeffKernel ((j : ℤ) - i - 1)) =
      centralFunctional ((C : ℤ) - j) (F.map (Int.castRingHom ℚ)) := by
  have hC : 0 < C := (Nat.zero_le j).trans_lt hj
  have hmap : (F.map (Int.castRingHom ℚ)).natDegree < C :=
    lt_of_le_of_lt Polynomial.natDegree_map_le hF
  rw [centralFunctional_eq_sum_range _ hmap]
  simp only [Polynomial.coeff_map, rationalIntCast_apply]
  calc
    _ = ∑ i ∈ Finset.range C, (F.coeff (C - 1 - i) : ℚ) *
        centralCoeffKernel ((((C - 1 - i : ℕ) : ℤ)) - ((C : ℤ) - j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [reversedRow_coeff, ite_eq_left hi']
      congr 2
      omega
    _ = _ := Finset.sum_range_reflect
      (fun u => (F.coeff u : ℚ) * centralCoeffKernel ((u : ℤ) - ((C : ℤ) - j))) C

theorem reversedChebyshev_contact {C d j : ℕ} (hd : d < C) (hj : j < C) :
    (∑ i ∈ Finset.range C,
      ((reversedRow C (Chebyshev.T ℤ (d : ℤ))).coeff i : ℚ) *
        centralCoeffKernel ((j : ℤ) - i - 1)) =
      ((reversedRow C (Chebyshev.U ℤ ((d : ℤ) - 1))).coeff j : ℚ) := by
  rw [reversedRow_centralFunctional hj _ (by simpa using hd), Chebyshev.map_T]
  have hindex : (C : ℤ) - j = ((C - 1 - j : ℕ) : ℤ) + 1 := by omega
  rw [hindex, centralFunctional_T_tail, reversedRow_coeff, ite_eq_left hj]
  have hmap := congrArg (fun P : ℚ[X] => P.coeff (C - 1 - j))
    (Chebyshev.map_U (Int.castRingHom ℚ) ((d : ℤ) - 1))
  simpa only [Polynomial.coeff_map, rationalIntCast_apply] using hmap.symm

end InternalCatalan

end

end OAI
