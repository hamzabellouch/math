import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import OAI.NumberTheory.Catalan.Arithmetic.PalindromicPrimeGeom
import OAI.NumberTheory.Catalan.Estimates.PalindromicReversalMultiplicities

namespace OAI


noncomputable section

namespace InternalCatalan

open Polynomial

def palindromicRatW (p : ℕ) [Fact p.Prime] : RatFunc (ZMod p) :=
  algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) X

def palindromicRatT (p : ℕ) [Fact p.Prime] : RatFunc (ZMod p) :=
  2 * palindromicRatW p / (1 + palindromicRatW p ^ 2)

def palindromicRatF (p : ℕ) [Fact p.Prime] : RatFunc (ZMod p) :=
  (1 - palindromicRatW p ^ 2) / (1 + palindromicRatW p ^ 2)

def palindromicRatE (p : ℕ) [Fact p.Prime] : RatFunc (ZMod p) :=
  (1 - palindromicRatT p ^ 2) ^ ((p - 1) / 2)

theorem palindromicRat_map_one_add_X_sq {p : ℕ} [Fact p.Prime] :
    algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) (1 + X ^ 2) =
      1 + palindromicRatW p ^ 2 := by
  simp [palindromicRatW]

theorem palindromicRat_map_one_sub_X_sq {p : ℕ} [Fact p.Prime] :
    algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) (1 - X ^ 2) =
      1 - palindromicRatW p ^ 2 := by
  simp [palindromicRatW]

theorem palindromic_one_add_X_sq_ne_zero {p : ℕ} [Fact p.Prime] :
    (1 + X ^ 2 : (ZMod p)[X]) ≠ 0 := by
  intro h
  have hcoeff : (1 : ZMod p) = 0 := by
    simpa [coeff_one, coeff_X_pow] using
      congrArg (fun P : (ZMod p)[X] => P.coeff 0) h
  exact one_ne_zero hcoeff

theorem palindromicRat_denominator_ne_zero {p : ℕ} [Fact p.Prime] :
    (1 + palindromicRatW p ^ 2 : RatFunc (ZMod p)) ≠ 0 := by
  intro h
  apply palindromic_one_add_X_sq_ne_zero (p := p)
  apply RatFunc.algebraMap_injective (ZMod p)
  simpa only [palindromicRat_map_one_add_X_sq, map_zero] using h

theorem palindromicRat_F_sq {p : ℕ} [Fact p.Prime] :
    palindromicRatF p ^ 2 = 1 - palindromicRatT p ^ 2 := by
  unfold palindromicRatF palindromicRatT
  field_simp [palindromicRat_denominator_ne_zero (p := p)]
  ring

theorem palindromic_prime_pred_twice_half {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) : 2 * ((p - 1) / 2) = p - 1 := by
  obtain ⟨m, hm⟩ := (Fact.out : p.Prime).even_sub_one hp2
  omega

theorem palindromicRat_E_eq_F_pow {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    palindromicRatE p = palindromicRatF p ^ (p - 1) := by
  unfold palindromicRatE
  rw [← palindromicRat_F_sq, ← pow_mul, palindromic_prime_pred_twice_half hp2]

end InternalCatalan





namespace InternalCatalan

open Polynomial

theorem palindromicRatW_transcendental {p : ℕ} [Fact p.Prime] :
    Transcendental (ZMod p) (palindromicRatW p) := by
  unfold palindromicRatW
  rw [transcendental_algebraMap_iff (RatFunc.algebraMap_injective (ZMod p))]
  exact Polynomial.transcendental_X (ZMod p)

theorem palindromicRatW_ne_zero {p : ℕ} [Fact p.Prime] :
    palindromicRatW p ≠ 0 := by
  intro h
  apply Polynomial.X_ne_zero (R := ZMod p)
  apply RatFunc.algebraMap_injective (ZMod p)
  simp [palindromicRatW] at h

theorem palindromicRatW_inv_transcendental {p : ℕ} [Fact p.Prime] :
    Transcendental (ZMod p) (palindromicRatW p)⁻¹ := by
  intro h
  exact palindromicRatW_transcendental (IsAlgebraic.inv_iff.mp h)

theorem palindromicRatW_inv_eval₂RingHom_injective {p : ℕ} [Fact p.Prime] :
    Function.Injective
      (eval₂RingHom (algebraMap (ZMod p) (RatFunc (ZMod p)))
        (palindromicRatW p)⁻¹) :=
  transcendental_iff_injective.mp palindromicRatW_inv_transcendental

def palindromicRatStar (p : ℕ) [Fact p.Prime] :
    RatFunc (ZMod p) →+* RatFunc (ZMod p) :=
  RatFunc.liftRingHom
    (eval₂RingHom (algebraMap (ZMod p) (RatFunc (ZMod p)))
      (palindromicRatW p)⁻¹)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (palindromicRatW_inv_eval₂RingHom_injective (p := p)))

theorem palindromicRatStar_map_polynomial {p : ℕ} [Fact p.Prime]
    (P : (ZMod p)[X]) :
    palindromicRatStar p (algebraMap ((ZMod p)[X]) (RatFunc (ZMod p)) P) =
      eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatW p)⁻¹ P := by
  exact RatFunc.liftRingHom_algebraMap _ _ P

@[simp]
theorem palindromicRatStar_W {p : ℕ} [Fact p.Prime] :
    palindromicRatStar p (palindromicRatW p) = (palindromicRatW p)⁻¹ := by
  exact (palindromicRatStar_map_polynomial (p := p) X).trans (eval₂_X _ _)

@[simp]
theorem palindromicRatStar_scalar {p : ℕ} [Fact p.Prime] (c : ZMod p) :
    palindromicRatStar p (algebraMap (ZMod p) (RatFunc (ZMod p)) c) =
      algebraMap (ZMod p) (RatFunc (ZMod p)) c := by
  have hc : algebraMap ((ZMod p)[X]) (RatFunc (ZMod p)) (C c) =
      algebraMap (ZMod p) (RatFunc (ZMod p)) c := by
    simpa only [map_one, div_one, Polynomial.algebraMap_eq] using
      (RatFunc.algebraMap_apply (K := ZMod p) (R := ZMod p) c).symm
  calc
    palindromicRatStar p (algebraMap (ZMod p) (RatFunc (ZMod p)) c) =
        palindromicRatStar p
          (algebraMap ((ZMod p)[X]) (RatFunc (ZMod p)) (C c)) :=
      congrArg (palindromicRatStar p) hc.symm
    _ = _ := by rw [palindromicRatStar_map_polynomial, eval₂_C]

theorem palindromicRatStar_injective {p : ℕ} [Fact p.Prime] :
    Function.Injective (palindromicRatStar p) :=
  (palindromicRatStar p).injective

end InternalCatalan





namespace InternalCatalan

open Polynomial

theorem palindromicRatT_ne_C {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ¬ ∃ c : ZMod p, palindromicRatT p = algebraMap (ZMod p) (RatFunc (ZMod p)) c := by
  rintro ⟨c, hc⟩
  have hmul : 2 * palindromicRatW p =
      algebraMap (ZMod p) (RatFunc (ZMod p)) c * (1 + palindromicRatW p ^ 2) := by
    exact (div_eq_iff (palindromicRat_denominator_ne_zero (p := p))).mp hc
  have hpoly : C (2 : ZMod p) * X = C c * (1 + X ^ 2) := by
    apply RatFunc.algebraMap_injective (ZMod p)
    have hC (a : ZMod p) :
        algebraMap ((ZMod p)[X]) (RatFunc (ZMod p)) (C a) =
          algebraMap (ZMod p) (RatFunc (ZMod p)) a := rfl
    simpa only [map_mul, map_add, map_one, map_pow, hC, map_ofNat,
      palindromicRatW] using hmul
  have hcoeff : (2 : ZMod p) = 0 := by
    simpa [coeff_C_mul, coeff_one, coeff_X_pow] using
      congrArg (fun P : (ZMod p)[X] => P.coeff 1) hpoly
  exact palindromic_two_ne_zero hp2 hcoeff

theorem palindromicRatT_transcendental {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    Transcendental (ZMod p) (palindromicRatT p) := by
  intro ht
  let S : Subalgebra (ZMod p) (RatFunc (ZMod p)) :=
    Subalgebra.algebraicClosure (ZMod p) (RatFunc (ZMod p))
  let t : S := ⟨palindromicRatT p, ht⟩
  have hw : Transcendental (ZMod p) (palindromicRatW p) := by
    unfold palindromicRatW
    rw [transcendental_algebraMap_iff (RatFunc.algebraMap_injective (ZMod p))]
    exact Polynomial.transcendental_X (ZMod p)
  have hwS : Transcendental S (palindromicRatW p) :=
    hw.subalgebraAlgebraicClosure
  apply hwS
  refine ⟨C t * (1 + X ^ 2) - C (2 : S) * X, ?_, ?_⟩
  · intro hpoly
    have ht0 : t = 0 := by
      simpa [coeff_C_mul, coeff_one, coeff_X_pow] using
        congrArg (fun Q : S[X] => Q.coeff 0) hpoly
    have ht0' : palindromicRatT p = 0 :=
      congrArg (fun a : S => (a : RatFunc (ZMod p))) ht0
    exact palindromicRatT_ne_C hp2 ⟨0, by simpa only [map_zero] using ht0'⟩
  · have htcoe : algebraMap S (RatFunc (ZMod p)) t = palindromicRatT p := rfl
    simp only [map_sub, map_mul, map_add, map_one, map_pow, aeval_C, aeval_X,
      htcoe, map_ofNat]
    rw [palindromicRatT,
      div_mul_cancel₀ _ (palindromicRat_denominator_ne_zero (p := p)), sub_self]

theorem palindromicRatT_aeval_injective {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    Function.Injective
      (aeval (palindromicRatT p) : (ZMod p)[X] →ₐ[ZMod p] RatFunc (ZMod p)) :=
  transcendental_iff_injective.mp (palindromicRatT_transcendental hp2)

theorem palindromicRatT_eval₂RingHom_injective {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    Function.Injective
      (eval₂RingHom (algebraMap (ZMod p) (RatFunc (ZMod p)))
        (palindromicRatT p)) :=
  palindromicRatT_aeval_injective hp2

theorem palindromicRatT_eval₂_eq_zero_iff {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (P : (ZMod p)[X]) :
    eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p) P = 0 ↔
      P = 0 := by
  constructor
  · intro h
    apply palindromicRatT_eval₂RingHom_injective hp2
    simpa using h
  · rintro rfl
    simp

end InternalCatalan





namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem palindromic_denominator_cleared_expansion {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (i : Fin p) :
    (X : (ZMod p)[X]) ^ i.val * (1 - X ^ 2) ^ (p - 1) =
      ∑ l : Fin p, (C (palindromicTransitionMatrix p l i) +
        C (palindromicReversedTransitionMatrix p l i) * X ^ p) *
          palindromicU p l.val := by
  rw [← palindromic_prime_geometric_identity]
  exact palindromicPairing_eq_sum_U hp2 i

theorem palindromicRat_map_C {p : ℕ} [Fact p.Prime] (a : ZMod p) :
    algebraMap ((ZMod p)[X]) (RatFunc (ZMod p)) (C a) =
      algebraMap (ZMod p) (RatFunc (ZMod p)) a := by
  simpa only [map_one, div_one, Polynomial.algebraMap_eq] using
    (RatFunc.algebraMap_apply (K := ZMod p) (R := ZMod p) a).symm

theorem palindromicRat_map_U {p : ℕ} [Fact p.Prime] (l : Fin p) :
    algebraMap ((ZMod p)[X]) (RatFunc (ZMod p)) (palindromicU p l.val) =
      palindromicRatT p ^ l.val * (1 + palindromicRatW p ^ 2) ^ (p - 1) := by
  have hle : l.val ≤ p - 1 := by have h := l.isLt; omega
  have hpow : (1 + palindromicRatW p ^ 2) ^ l.val *
      (1 + palindromicRatW p ^ 2) ^ (p - 1 - l.val) =
        (1 + palindromicRatW p ^ 2) ^ (p - 1) := by
    rw [← pow_add, Nat.add_sub_of_le hle]
  simp only [palindromicU, map_mul, map_pow, map_add, map_one, map_ofNat]
  change (2 * palindromicRatW p) ^ l.val *
      (1 + palindromicRatW p ^ 2) ^ (p - 1 - l.val) = _
  rw [palindromicRatT, div_pow, ← hpow, ← mul_assoc,
    div_mul_cancel₀ _ (pow_ne_zero _ (palindromicRat_denominator_ne_zero (p := p)))]

theorem palindromicRat_F_pow_expansion {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (i : Fin p) :
    palindromicRatF p ^ (p - 1) * palindromicRatW p ^ i.val =
      ∑ l : Fin p, palindromicRatT p ^ l.val *
        (algebraMap (ZMod p) (RatFunc (ZMod p)) (palindromicTransitionMatrix p l i) +
          algebraMap (ZMod p) (RatFunc (ZMod p))
            (palindromicReversedTransitionMatrix p l i) * palindromicRatW p ^ p) := by
  have hmap := congrArg (algebraMap ((ZMod p)[X]) (RatFunc (ZMod p)))
    (palindromic_denominator_cleared_expansion hp2 i)
  simp only [map_mul, map_pow, map_sub, map_one, map_sum, map_add,
    palindromicRat_map_C, palindromicRat_map_U] at hmap
  change palindromicRatW p ^ i.val * (1 - palindromicRatW p ^ 2) ^ (p - 1) =
    ∑ l : Fin p,
      (algebraMap (ZMod p) (RatFunc (ZMod p)) (palindromicTransitionMatrix p l i) +
        algebraMap (ZMod p) (RatFunc (ZMod p))
          (palindromicReversedTransitionMatrix p l i) * palindromicRatW p ^ p) *
        (palindromicRatT p ^ l.val * (1 + palindromicRatW p ^ 2) ^ (p - 1)) at hmap
  apply mul_right_cancel₀
    (pow_ne_zero (p - 1) (palindromicRat_denominator_ne_zero (p := p)))
  calc
    (palindromicRatF p ^ (p - 1) * palindromicRatW p ^ i.val) *
        (1 + palindromicRatW p ^ 2) ^ (p - 1) =
      palindromicRatW p ^ i.val * (1 - palindromicRatW p ^ 2) ^ (p - 1) := by
        rw [palindromicRatF, div_pow]
        field_simp [palindromicRat_denominator_ne_zero (p := p)]
    _ = _ := hmap
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l hl
      ring

theorem palindromicRat_expansion {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (i : Fin p) :
    palindromicRatE p * palindromicRatW p ^ i.val =
      ∑ l : Fin p, palindromicRatT p ^ l.val *
        (algebraMap (ZMod p) (RatFunc (ZMod p)) (palindromicTransitionMatrix p l i) +
          algebraMap (ZMod p) (RatFunc (ZMod p))
            (palindromicReversedTransitionMatrix p l i) * palindromicRatW p ^ p) := by
  rw [palindromicRat_E_eq_F_pow hp2]
  exact palindromicRat_F_pow_expansion hp2 i

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem palindromicRat_W_ne_zero {p : ℕ} [Fact p.Prime] :
    palindromicRatW p ≠ 0 := by
  exact RatFunc.algebraMap_ne_zero (Polynomial.X_ne_zero (R := ZMod p))

theorem palindromicRat_two_pow {p : ℕ} [Fact p.Prime] :
    (2 : RatFunc (ZMod p)) ^ p = 2 := by
  simpa only [one_add_one_eq_two, one_pow] using
    add_pow_char (1 : RatFunc (ZMod p)) 1 p

theorem palindromicRat_T_frobenius {p : ℕ} [Fact p.Prime] :
    palindromicRatT p ^ p =
      2 * palindromicRatW p ^ p / (1 + (palindromicRatW p ^ p) ^ 2) := by
  have hpw : (palindromicRatW p ^ 2) ^ p = (palindromicRatW p ^ p) ^ 2 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 p]
  rw [palindromicRatT, div_pow, mul_pow, palindromicRat_two_pow,
    add_pow_char, one_pow, hpw]

theorem palindromicRat_F_frobenius {p : ℕ} [Fact p.Prime] :
    palindromicRatF p ^ p =
      (1 - (palindromicRatW p ^ p) ^ 2) /
        (1 + (palindromicRatW p ^ p) ^ 2) := by
  rw [palindromicRatF, div_pow, sub_pow_char, add_pow_char, one_pow]
  have hpw : (palindromicRatW p ^ 2) ^ p = (palindromicRatW p ^ p) ^ 2 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 p]
  rw [hpw]

theorem palindromicRat_F_mul_E {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    palindromicRatF p * palindromicRatE p = palindromicRatF p ^ p := by
  have hp : 1 ≤ p := by have h := (Fact.out : p.Prime).pos; omega
  rw [palindromicRat_E_eq_F_pow hp2, ← pow_succ', Nat.sub_add_cancel hp]

def palindromicRatRow (p N r : ℕ) [Fact p.Prime] : RatFunc (ZMod p) :=
  (1 - palindromicRatT p) ^ (2 * N) * palindromicRatT p ^ (63 * N) *
    palindromicRatW p ^ ((r : ℤ) - ((4 * N : ℕ) : ℤ))

theorem palindromicRatRow_successor {p : ℕ} [Fact p.Prime] (N r : ℕ) :
    palindromicRatRow p N (r + 1) =
      palindromicRatRow p N r * palindromicRatW p := by
  simp only [palindromicRatRow,
    zpow_natCast_sub_natCast₀ (palindromicRat_W_ne_zero (p := p)), pow_succ]
  ring

theorem palindromicRatRow_scale {p : ℕ} [Fact p.Prime] (r₀ i : ℕ) :
    palindromicRatRow p p (p * r₀ + i) =
      palindromicRatRow p 1 r₀ ^ p * palindromicRatW p ^ i := by
  simp only [palindromicRatRow, mul_one,
    zpow_natCast_sub_natCast₀ (palindromicRat_W_ne_zero (p := p)),
    mul_pow, div_pow, ← pow_mul]
  rw [pow_add, Nat.mul_comm r₀ p]
  ring

theorem palindromicRatRow_expansion {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (r₀ : ℕ) (i : Fin p) :
    palindromicRatRow p p (p * r₀ + i.val) * palindromicRatE p =
      ∑ l : Fin p, palindromicRatT p ^ l.val *
        (algebraMap (ZMod p) (RatFunc (ZMod p)) (palindromicTransitionMatrix p l i) *
            palindromicRatRow p 1 r₀ ^ p +
          algebraMap (ZMod p) (RatFunc (ZMod p))
            (palindromicReversedTransitionMatrix p l i) *
              palindromicRatRow p 1 (r₀ + 1) ^ p) := by
  rw [palindromicRatRow_scale]
  have he := palindromicRat_expansion hp2 i
  calc
    (palindromicRatRow p 1 r₀ ^ p * palindromicRatW p ^ i.val) *
        palindromicRatE p =
      palindromicRatRow p 1 r₀ ^ p *
        (palindromicRatE p * palindromicRatW p ^ i.val) := by ring
    _ = _ := by
      rw [he, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      rw [palindromicRatRow_successor, mul_pow]
      ring

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Polynomial

theorem chebyshev_signed_laurent_eval {K : Type*} [Field K]
    (φ : ℤ →+* K) (x y w : K) (hw : w ≠ 0)
    (hxy : x - y = w) (hcurve : y ^ 2 = x ^ 2 - 1) (m : ℤ) :
    (Chebyshev.T ℤ m).eval₂ φ x -
        y * (Chebyshev.U ℤ (m - 1)).eval₂ φ x = w ^ m := by
  let A : ℤ → K := fun n =>
    (Chebyshev.T ℤ n).eval₂ φ x - y * (Chebyshev.U ℤ (n - 1)).eval₂ φ x
  have hT (n : ℤ) : (Chebyshev.T ℤ (n + 1)).eval₂ φ x =
      x * (Chebyshev.T ℤ n).eval₂ φ x -
        (1 - x ^ 2) * (Chebyshev.U ℤ (n - 1)).eval₂ φ x := by
    have h := congrArg (fun P : ℤ[X] => P.eval₂ φ x)
      (Chebyshev.T_eq_X_mul_T_sub_pol_U ℤ (n - 1))
    simpa only [show n - 1 + 2 = n + 1 by omega, sub_add_cancel,
      eval₂_sub, eval₂_mul, eval₂_X, eval₂_one, eval₂_pow] using h
  have hU (n : ℤ) : (Chebyshev.U ℤ n).eval₂ φ x =
      x * (Chebyshev.U ℤ (n - 1)).eval₂ φ x +
        (Chebyshev.T ℤ n).eval₂ φ x := by
    have h := congrArg (fun P : ℤ[X] => P.eval₂ φ x)
      (Chebyshev.U_eq_X_mul_U_add_T ℤ (n - 1))
    simpa only [sub_add_cancel, eval₂_add, eval₂_mul, eval₂_X] using h
  have hstep (n : ℤ) : A (n + 1) = w * A n := by
    simp only [A, show n + 1 - 1 = n by omega, hT n, hU n]
    rw [← hxy]
    linear_combination -((Chebyshev.U ℤ (n - 1)).eval₂ φ x) * hcurve
  change A m = w ^ m
  induction m using Int.induction_on with
  | zero => simp [A]
  | succ n ih =>
    rw [hstep, ih, zpow_add₀ hw, zpow_one]
    exact mul_comm _ _
  | pred n ih =>
    apply mul_left_cancel₀ hw
    calc
      w * A (-(n : ℤ) - 1) = A (-(n : ℤ)) := by
        rw [← hstep, show (-(n : ℤ) - 1) + 1 = -(n : ℤ) by omega]
      _ = w ^ (-(n : ℤ)) := ih
      _ = w * w ^ (-(n : ℤ) - 1) := by
        rw [zpow_sub₀ hw, zpow_one]
        field_simp [hw]

theorem palindromicRat_two_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : RatFunc (ZMod p)) ≠ 0 := by
  have hpoly : (2 : (ZMod p)[X]) ≠ 0 := by
    intro h
    apply palindromic_two_ne_zero hp2
    simpa using congrArg (fun P : (ZMod p)[X] => P.coeff 0) h
  have hmap := RatFunc.algebraMap_ne_zero hpoly
  simpa only [map_ofNat] using hmap

theorem palindromicRat_T_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    palindromicRatT p ≠ 0 :=
  div_ne_zero (mul_ne_zero (palindromicRat_two_ne_zero hp2)
    palindromicRat_W_ne_zero) palindromicRat_denominator_ne_zero

theorem palindromicRat_invT_sub_F_div_T {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (palindromicRatT p)⁻¹ - palindromicRatF p / palindromicRatT p =
      palindromicRatW p := by
  unfold palindromicRatT palindromicRatF
  field_simp [palindromicRat_W_ne_zero (p := p), palindromicRat_two_ne_zero hp2,
    palindromicRat_denominator_ne_zero (p := p)]
  ring

theorem palindromicRat_F_div_T_sq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (palindromicRatF p / palindromicRatT p) ^ 2 =
      ((palindromicRatT p)⁻¹) ^ 2 - 1 := by
  rw [div_pow, palindromicRat_F_sq]
  field_simp [palindromicRat_T_ne_zero hp2]

theorem palindromicRat_chebyshev_signed {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (m : ℤ) :
    palindromicRatT p *
        (Chebyshev.T ℤ m).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
          (palindromicRatT p)⁻¹ -
      palindromicRatF p *
        (Chebyshev.U ℤ (m - 1)).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
          (palindromicRatT p)⁻¹ =
      palindromicRatT p * palindromicRatW p ^ m := by
  have heval := chebyshev_signed_laurent_eval
    (Int.castRingHom (RatFunc (ZMod p))) ((palindromicRatT p)⁻¹)
    (palindromicRatF p / palindromicRatT p) (palindromicRatW p)
    palindromicRat_W_ne_zero (palindromicRat_invT_sub_F_div_T hp2)
    (palindromicRat_F_div_T_sq hp2) m
  calc
    _ = palindromicRatT p *
        ((Chebyshev.T ℤ m).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
            (palindromicRatT p)⁻¹ -
          (palindromicRatF p / palindromicRatT p) *
            (Chebyshev.U ℤ (m - 1)).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
              (palindromicRatT p)⁻¹) := by
      field_simp [palindromicRat_T_ne_zero hp2]
    _ = _ := congrArg (fun z => palindromicRatT p * z) heval

end InternalCatalan





namespace InternalCatalan

open Polynomial

theorem palindromicRat_inverse_denominator_ne_zero {p : ℕ} [Fact p.Prime] :
    (1 + ((palindromicRatW p)⁻¹) ^ 2 : RatFunc (ZMod p)) ≠ 0 := by
  have heq : 1 + ((palindromicRatW p)⁻¹) ^ 2 =
      (1 + palindromicRatW p ^ 2) / palindromicRatW p ^ 2 := by
    field_simp [palindromicRat_W_ne_zero (p := p)]
    ring
  rw [heq]
  exact div_ne_zero palindromicRat_denominator_ne_zero
    (pow_ne_zero _ palindromicRat_W_ne_zero)

@[simp] theorem palindromicRatStar_T {p : ℕ} [Fact p.Prime] :
    palindromicRatStar p (palindromicRatT p) = palindromicRatT p := by
  simp only [palindromicRatT, map_div₀, map_mul, map_ofNat, map_add,
    map_one, map_pow, palindromicRatStar_W]
  field_simp [palindromicRat_W_ne_zero (p := p),
    palindromicRat_denominator_ne_zero (p := p),
    palindromicRat_inverse_denominator_ne_zero (p := p)]
  linear_combination 2 *
    (mul_inv_cancel₀ (palindromicRat_denominator_ne_zero (p := p)))

@[simp] theorem palindromicRatStar_F {p : ℕ} [Fact p.Prime] :
    palindromicRatStar p (palindromicRatF p) = -palindromicRatF p := by
  simp only [palindromicRatF, map_div₀, map_sub, map_add,
    map_one, map_pow, palindromicRatStar_W]
  field_simp [palindromicRat_W_ne_zero (p := p),
    palindromicRat_denominator_ne_zero (p := p),
    palindromicRat_inverse_denominator_ne_zero (p := p)]
  linear_combination (palindromicRatW p ^ 2 - 1) *
    (mul_inv_cancel₀ (palindromicRat_denominator_ne_zero (p := p)))

@[simp] theorem palindromicRatStar_E {p : ℕ} [Fact p.Prime] :
    palindromicRatStar p (palindromicRatE p) = palindromicRatE p := by
  simp only [palindromicRatE, map_pow, map_sub, map_one, palindromicRatStar_T]

@[simp] theorem palindromicRatStar_F_pow {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    palindromicRatStar p (palindromicRatF p ^ p) = -palindromicRatF p ^ p := by
  rw [← palindromicRat_F_mul_E hp2, map_mul, palindromicRatStar_F,
    palindromicRatStar_E, neg_mul, palindromicRat_F_mul_E hp2]

@[simp] theorem palindromicRatStar_eval₂ {p : ℕ} [Fact p.Prime]
    (P : (ZMod p)[X]) :
    palindromicRatStar p
        (P.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p)) =
      P.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p) := by
  simp only [eval₂_eq_sum, sum_def, map_sum, map_mul, palindromicRatStar_scalar,
    map_pow, palindromicRatStar_T]

@[simp] theorem palindromicRatStar_eval₂_int {p : ℕ} [Fact p.Prime]
    (P : ℤ[X]) :
    palindromicRatStar p
        (P.eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p)) =
      P.eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p) := by
  have hcast (z : ℤ) : palindromicRatStar p
      ((Int.castRingHom (RatFunc (ZMod p))) z) =
      (Int.castRingHom (RatFunc (ZMod p))) z := by
    change palindromicRatStar p (z : RatFunc (ZMod p)) = z
    exact map_intCast (palindromicRatStar p) z
  simp only [eval₂_eq_sum, sum_def, map_sum, map_mul, hcast,
    map_pow, palindromicRatStar_T]

theorem palindromicRat_F_ne_zero {p : ℕ} [Fact p.Prime] :
    palindromicRatF p ≠ 0 := by
  apply div_ne_zero _ palindromicRat_denominator_ne_zero
  simpa only [map_sub, map_one, map_pow, palindromicRatW] using
    RatFunc.algebraMap_ne_zero (palindromic_one_sub_X_sq_ne_zero (p := p))

end InternalCatalan

end

end OAI
