import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.FieldTheory.Finite.Basic
import OAI.NumberTheory.Catalan.Estimates.PalindromicStarParameters

namespace OAI


noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem palindromicRat_coefficient_frobenius {p : ℕ} [Fact p.Prime]
    (a : ZMod p) :
    (algebraMap (ZMod p) (RatFunc (ZMod p)) a) ^ p =
      algebraMap (ZMod p) (RatFunc (ZMod p)) a := by
  rw [← map_pow, ZMod.pow_card]

theorem palindromicRat_polynomial_eval₂_pow {p : ℕ} [Fact p.Prime]
    (P : (ZMod p)[X]) (x : RatFunc (ZMod p)) :
    (P.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) x) ^ p =
      P.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) (x ^ p) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [eval₂_add, add_pow_char, hP, hQ, eval₂_add]
  | monomial n a =>
    simp only [eval₂_monomial, mul_pow, palindromicRat_coefficient_frobenius]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm n p]

theorem palindromicRat_polynomial_T_frobenius {p : ℕ} [Fact p.Prime]
    (P : (ZMod p)[X]) :
    (P.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p)) ^ p =
      P.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p ^ p) :=
  palindromicRat_polynomial_eval₂_pow P (palindromicRatT p)

theorem palindromicRat_polynomial_comp_X_pow_eval₂ {p : ℕ} [Fact p.Prime]
    (P : (ZMod p)[X]) (x : RatFunc (ZMod p)) :
    (P.comp (X ^ p)).eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) x =
      (P.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) x) ^ p := by
  rw [eval₂_comp, eval₂_X_pow]
  exact (palindromicRat_polynomial_eval₂_pow P x).symm

theorem palindromicRat_polynomial_comp_X_pow_at_T {p : ℕ} [Fact p.Prime]
    (P : (ZMod p)[X]) :
    (P.comp (X ^ p)).eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p)))
        (palindromicRatT p) =
      (P.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p)) ^ p :=
  palindromicRat_polynomial_comp_X_pow_eval₂ P (palindromicRatT p)

theorem palindromicRat_int_map_eval₂ {p : ℕ} [Fact p.Prime]
    (P : ℤ[X]) (x : RatFunc (ZMod p)) :
    (P.map (Int.castRingHom (ZMod p))).eval₂
        (algebraMap (ZMod p) (RatFunc (ZMod p))) x =
      P.eval₂ (Int.castRingHom (RatFunc (ZMod p))) x := by
  have hmap : (algebraMap (ZMod p) (RatFunc (ZMod p))).comp
      (Int.castRingHom (ZMod p)) = Int.castRingHom (RatFunc (ZMod p)) := by
    ext z
    simp
  rw [eval₂_map, hmap]

theorem palindromicRat_rowP_map_eval₂ {p : ℕ} [Fact p.Prime]
    (N r : ℕ) (x : RatFunc (ZMod p)) :
    ((rowP N r).map (Int.castRingHom (ZMod p))).eval₂
        (algebraMap (ZMod p) (RatFunc (ZMod p))) x =
      (rowP N r).eval₂ (Int.castRingHom (RatFunc (ZMod p))) x :=
  palindromicRat_int_map_eval₂ (rowP N r) x

theorem palindromicRat_rowD_map_eval₂ {p : ℕ} [Fact p.Prime]
    (N r : ℕ) (x : RatFunc (ZMod p)) :
    ((rowD N r).map (Int.castRingHom (ZMod p))).eval₂
        (algebraMap (ZMod p) (RatFunc (ZMod p))) x =
      (rowD N r).eval₂ (Int.castRingHom (RatFunc (ZMod p))) x :=
  palindromicRat_int_map_eval₂ (rowD N r) x

theorem palindromicRat_int_polynomial_T_frobenius {p : ℕ} [Fact p.Prime]
    (P : ℤ[X]) :
    (P.eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p)) ^ p =
      P.eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p ^ p) := by
  have h := palindromicRat_polynomial_T_frobenius
    (P.map (Int.castRingHom (ZMod p)))
  simpa only [palindromicRat_int_map_eval₂] using h

theorem palindromicRat_PResidueSum_eval₂ {p : ℕ} [Fact p.Prime]
    (r0 : ℕ) (i : Fin p) :
    (palindromicPResidueSum p r0 i).eval₂
        (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p) =
      ∑ l : Fin p, palindromicRatT p ^ l.val * palindromicRatT p ^ p *
        (algebraMap (ZMod p) (RatFunc (ZMod p))
            (palindromicTransitionMatrix p l i) *
            ((rowP 1 r0).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
              (palindromicRatT p)) ^ p +
          algebraMap (ZMod p) (RatFunc (ZMod p))
            (palindromicReversedTransitionMatrix p l i) *
            ((rowP 1 (r0 + 1)).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
              (palindromicRatT p)) ^ p) := by
  simp only [palindromicPResidueSum, eval₂_finsetSum, eval₂_mul,
    eval₂_X_pow, eval₂_add, eval₂_C, palindromicRat_polynomial_comp_X_pow_eval₂,
    palindromicPBase, palindromicRat_int_map_eval₂]

theorem palindromicRat_DResidueSum_eval₂ {p : ℕ} [Fact p.Prime]
    (r0 : ℕ) (i : Fin p) :
    (palindromicDResidueSum p r0 i).eval₂
        (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p) =
      ∑ l : Fin p, palindromicRatT p ^ l.val *
        (algebraMap (ZMod p) (RatFunc (ZMod p))
            (palindromicTransitionMatrix p l i) *
            ((rowD 1 r0).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
              (palindromicRatT p)) ^ p +
          algebraMap (ZMod p) (RatFunc (ZMod p))
            (palindromicReversedTransitionMatrix p l i) *
            ((rowD 1 (r0 + 1)).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
              (palindromicRatT p)) ^ p) := by
  simp only [palindromicDResidueSum, eval₂_finsetSum, eval₂_mul,
    eval₂_X_pow, eval₂_add, eval₂_C, palindromicRat_polynomial_comp_X_pow_eval₂,
    palindromicDBase, palindromicRat_int_map_eval₂]

end InternalCatalan

end

end OAI
