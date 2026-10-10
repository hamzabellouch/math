import OAI.NumberTheory.Catalan.Polynomial.PalindromicPolynomialFrobenius

namespace OAI


noncomputable section

namespace InternalCatalan

open Polynomial

theorem chebyshev_U_sign_natAbs_eval {K : Type*} [Field K]
    (φ : ℤ →+* K) (x : K) (m : ℤ) :
    φ (Int.sign m) * (Chebyshev.U ℤ ((m.natAbs : ℤ) - 1)).eval₂ φ x =
      (Chebyshev.U ℤ (m - 1)).eval₂ φ x := by
  rcases lt_trichotomy m 0 with hm | hm | hm
  · rw [Int.ofNat_natAbs_of_nonpos hm.le, Int.sign_eq_neg_one_of_neg hm,
      map_neg, map_one, neg_one_mul, Chebyshev.U_neg_sub_one, eval₂_neg, neg_neg]
  · subst m
    simp
  · rw [Int.natAbs_of_nonneg hm.le, Int.sign_eq_one_of_pos hm, map_one, one_mul]

theorem rowP_eval₂_of_distance_lt {K : Type*} [Field K] (φ : ℤ →+* K)
    {N r : ℕ} (hd : rowDistance N r < Cdegree N) {x : K} (hx : x ≠ 0) :
    (rowP N r).eval₂ φ x =
      (1 - x) ^ h N * x ^ (Cdegree N - 1) *
        (Chebyshev.T ℤ (rowDistance N r : ℤ)).eval₂ φ x⁻¹ := by
  have hT : (Chebyshev.T ℤ (rowDistance N r : ℤ)).natDegree < Cdegree N := by
    simpa [Chebyshev.natDegree_T] using hd
  unfold rowP
  rw [eval₂_mul, reversedRow_eval₂ φ hT hx]
  simp only [eval₂_pow, eval₂_sub, eval₂_one, eval₂_X]
  exact (mul_assoc _ _ _).symm

theorem rowD_eval₂_of_distance_lt {K : Type*} [Field K] (φ : ℤ →+* K)
    {N r : ℕ} (hd : rowDistance N r < Cdegree N) {x : K} (hx : x ≠ 0) :
    (rowD N r).eval₂ φ x =
      φ (Int.sign (rowOffset N r)) * (1 - x) ^ h N * x ^ (Cdegree N - 1) *
        (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1)).eval₂ φ x⁻¹ := by
  have hU : (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1)).natDegree <
      Cdegree N := by
    rw [Chebyshev.natDegree_U]
    simp only [sub_add_cancel, Int.natAbs_natCast]
    omega
  unfold rowD
  rw [eval₂_mul, eval₂_mul, reversedRow_eval₂ φ hU hx]
  simp only [eval₂_C, eval₂_pow, eval₂_sub, eval₂_one, eval₂_X]
  ring

theorem palindromicRat_row_identity_of_distance_lt {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {N r : ℕ} (hN : 0 < N)
    (hd : rowDistance N r < Cdegree N) :
    palindromicRatT p * (rowP N r).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
        (palindromicRatT p) -
      palindromicRatF p * (rowD N r).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
        (palindromicRatT p) =
      (1 - palindromicRatT p) ^ (2 * N) * palindromicRatT p ^ (63 * N) *
        palindromicRatW p ^ ((r : ℤ) - 4 * (N : ℤ)) := by
  have heval := palindromicRat_chebyshev_signed hp2 (rowOffset N r)
  rw [← Chebyshev.T_natAbs ℤ (rowOffset N r),
    ← chebyshev_U_sign_natAbs_eval (Int.castRingHom (RatFunc (ZMod p)))
      ((palindromicRatT p)⁻¹) (rowOffset N r)] at heval
  have hpow : palindromicRatT p ^ (Cdegree N - 1) * palindromicRatT p =
      palindromicRatT p ^ Cdegree N := by
    rw [← pow_succ, show Cdegree N - 1 + 1 = Cdegree N by
      have hC := Cdegree_pos hN
      omega]
  rw [rowP_eval₂_of_distance_lt _ hd (palindromicRat_T_ne_zero hp2),
    rowD_eval₂_of_distance_lt _ hd (palindromicRat_T_ne_zero hp2)]
  calc
    _ = (1 - palindromicRatT p) ^ h N * palindromicRatT p ^ (Cdegree N - 1) *
        (palindromicRatT p *
          (Chebyshev.T ℤ (rowDistance N r : ℤ)).eval₂
            (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p)⁻¹ -
        palindromicRatF p *
          ((Int.castRingHom (RatFunc (ZMod p))) (Int.sign (rowOffset N r)) *
            (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1)).eval₂
              (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p)⁻¹)) := by ring
    _ = (1 - palindromicRatT p) ^ h N * palindromicRatT p ^ (Cdegree N - 1) *
        (palindromicRatT p * palindromicRatW p ^ rowOffset N r) := by
      exact congrArg (fun z : RatFunc (ZMod p) =>
        (1 - palindromicRatT p) ^ h N *
          palindromicRatT p ^ (Cdegree N - 1) * z) heval
    _ = (1 - palindromicRatT p) ^ h N *
        (palindromicRatT p ^ (Cdegree N - 1) * palindromicRatT p) *
          palindromicRatW p ^ rowOffset N r := by ring
    _ = _ := by
      rw [hpow]
      simp only [h, Cdegree, rowOffset, g, Nat.cast_mul, Nat.cast_ofNat]

theorem palindromicRat_row_identity {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {N r : ℕ} (hN : 0 < N) (hr : r < n N) :
    palindromicRatT p * (rowP N r).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
        (palindromicRatT p) -
      palindromicRatF p * (rowD N r).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
        (palindromicRatT p) =
      (1 - palindromicRatT p) ^ (2 * N) * palindromicRatT p ^ (63 * N) *
        palindromicRatW p ^ ((r : ℤ) - 4 * (N : ℤ)) :=
  palindromicRat_row_identity_of_distance_lt hp2 hN (rowDistance_lt_Cdegree hN hr)

theorem palindromicRat_row_identity_auxiliary {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    palindromicRatT p * (rowP 1 48).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
        (palindromicRatT p) -
      palindromicRatF p * (rowD 1 48).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
        (palindromicRatT p) =
      (1 - palindromicRatT p) ^ 2 * palindromicRatT p ^ 63 *
        palindromicRatW p ^ (44 : ℤ) := by
  simpa using palindromicRat_row_identity_of_distance_lt hp2 (N := 1) (r := 48)
    (by decide) (by decide)

end InternalCatalan





namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem palindromic_base_distance_lt {j : ℕ} (hj : j ≤ 48) :
    rowDistance 1 j < Cdegree 1 := by
  unfold rowDistance rowOffset g Cdegree
  omega

theorem palindromic_block_row_lt {p r₀ : ℕ} [Fact p.Prime]
    (hr : r₀ < 48) (i : Fin p) : p * r₀ + i.val < n p := by
  have hm := Nat.mul_le_mul_left p (show r₀ + 1 ≤ 48 by omega)
  have hi := i.isLt
  simp only [Nat.mul_add, Nat.mul_one] at hm
  unfold n
  nlinarith

theorem palindromicRatRow_eq_actual_rows {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {N r : ℕ} (hN : 0 < N)
    (hd : rowDistance N r < Cdegree N) :
    palindromicRatRow p N r =
      palindromicRatT p * (rowP N r).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
          (palindromicRatT p) -
        palindromicRatF p * (rowD N r).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
          (palindromicRatT p) := by
  symm
  simpa only [palindromicRatRow, Nat.cast_mul, Nat.cast_ofNat] using
    palindromicRat_row_identity_of_distance_lt hp2 hN hd

theorem palindromicRat_rows_separated {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {r₀ : ℕ} (hr : r₀ < 48) (i : Fin p) :
    (palindromicRatT p *
        (rowP p (p * r₀ + i.val)).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
          (palindromicRatT p) * palindromicRatE p =
      (palindromicPResidueSum p r₀ i).eval₂
        (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p)) ∧
    ((rowD p (p * r₀ + i.val)).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
        (palindromicRatT p) =
      (palindromicDResidueSum p r₀ i).eval₂
        (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p)) := by
  let ev : ℤ[X] → RatFunc (ZMod p) := fun P =>
    P.eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p)
  let evp : (ZMod p)[X] → RatFunc (ZMod p) := fun P =>
    P.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p)
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hmain := palindromicRatRow_eq_actual_rows hp2 hp
    (rowDistance_lt_Cdegree hp (palindromic_block_row_lt hr i))
  have hbase := palindromicRatRow_eq_actual_rows hp2 (N := 1) (r := r₀)
    (by decide) (palindromic_base_distance_lt (by omega))
  have hnext := palindromicRatRow_eq_actual_rows hp2 (N := 1) (r := r₀ + 1)
    (by decide) (palindromic_base_distance_lt (by omega))
  have hraw := palindromicRatRow_expansion hp2 r₀ i
  rw [hmain, hbase, hnext] at hraw
  have hleft :
      (palindromicRatT p * ev (rowP p (p * r₀ + i.val)) -
        palindromicRatF p * ev (rowD p (p * r₀ + i.val))) * palindromicRatE p =
      palindromicRatT p * ev (rowP p (p * r₀ + i.val)) * palindromicRatE p -
        palindromicRatF p ^ p * ev (rowD p (p * r₀ + i.val)) := by
    rw [← palindromicRat_F_mul_E hp2]
    ring
  have hright :
      (∑ l : Fin p, palindromicRatT p ^ l.val *
        (algebraMap (ZMod p) (RatFunc (ZMod p)) (palindromicTransitionMatrix p l i) *
            (palindromicRatT p * ev (rowP 1 r₀) - palindromicRatF p * ev (rowD 1 r₀)) ^ p +
          algebraMap (ZMod p) (RatFunc (ZMod p))
            (palindromicReversedTransitionMatrix p l i) *
              (palindromicRatT p * ev (rowP 1 (r₀ + 1)) -
                palindromicRatF p * ev (rowD 1 (r₀ + 1))) ^ p)) =
        evp (palindromicPResidueSum p r₀ i) -
          palindromicRatF p ^ p * evp (palindromicDResidueSum p r₀ i) := by
    dsimp only [evp]
    rw [palindromicRat_PResidueSum_eval₂, palindromicRat_DResidueSum_eval₂,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    simp only [sub_pow_char, mul_pow]
    dsimp only [ev]
    ring
  change (palindromicRatT p * ev (rowP p (p * r₀ + i.val)) -
      palindromicRatF p * ev (rowD p (p * r₀ + i.val))) * palindromicRatE p = _ at hraw
  rw [hleft, hright] at hraw
  have hstar := congrArg (palindromicRatStar p) hraw
  dsimp only [ev, evp] at hstar
  simp only [map_sub, map_mul, palindromicRatStar_T, palindromicRatStar_E,
    palindromicRatStar_eval₂_int, palindromicRatStar_F_pow hp2,
    palindromicRatStar_eval₂] at hstar
  have hP : palindromicRatT p * ev (rowP p (p * r₀ + i.val)) * palindromicRatE p =
      evp (palindromicPResidueSum p r₀ i) := by
    apply mul_left_cancel₀ (palindromicRat_two_ne_zero hp2)
    dsimp only [ev, evp] at *
    linear_combination hraw + hstar
  have hD : ev (rowD p (p * r₀ + i.val)) = evp (palindromicDResidueSum p r₀ i) := by
    apply mul_left_cancel₀ (pow_ne_zero p (palindromicRat_F_ne_zero (p := p)))
    linear_combination hP - hraw
  exact ⟨hP, hD⟩

theorem palindromic_rowP_frobenius {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {r₀ : ℕ} (hr : r₀ < 48) (i : Fin p) :
    X * (rowP p (p * r₀ + i.val)).map (Int.castRingHom (ZMod p)) *
        (1 - X ^ 2) ^ ((p - 1) / 2) = palindromicPResidueSum p r₀ i := by
  apply palindromicRatT_eval₂RingHom_injective hp2
  change eval₂ _ _ _ = eval₂ _ _ _
  simp only [eval₂_mul, eval₂_X, eval₂_pow, eval₂_sub, eval₂_one,
    palindromicRat_int_map_eval₂]
  exact (palindromicRat_rows_separated hp2 hr i).1

theorem palindromic_rowD_frobenius {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {r₀ : ℕ} (hr : r₀ < 48) (i : Fin p) :
    (rowD p (p * r₀ + i.val)).map (Int.castRingHom (ZMod p)) =
      palindromicDResidueSum p r₀ i := by
  apply palindromicRatT_eval₂RingHom_injective hp2
  change eval₂ _ _ _ = eval₂ _ _ _
  rw [palindromicRat_int_map_eval₂]
  exact (palindromicRat_rows_separated hp2 hr i).2

end InternalCatalan

end

end OAI
