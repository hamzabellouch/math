import Mathlib

namespace OAI

/-! Divided binomial polynomials, cocycle identities and cyclic sums. -/

noncomputable section
open Finset
namespace LowerSphereCyclic

def dividedBinomial {R : Type*} [CommRing R] (p : ℕ) (x y : R) : R :=
  ∑ i ∈ Finset.Ioo 0 p, ((p.choose i / p : ℕ) : R) * x ^ i * y ^ (p - i)

lemma map_dividedBinomial {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : ℕ) (x y : R) :
    f (dividedBinomial p x y) = dividedBinomial p (f x) (f y) := by
  simp [dividedBinomial]

lemma mul_dividedBinomial {R : Type*} [CommRing R] {p : ℕ}
    (hp : p.Prime) (x y : R) :
    (p : R) * dividedBinomial p x y = (x + y) ^ p - x ^ p - y ^ p := by
  have hcoeff (i : ℕ) (hi : i ∈ Finset.Ioo 0 p) :
      (p : R) * ((p.choose i / p : ℕ) : R) = (p.choose i : R) := by
    rw [← Nat.cast_mul]
    congr 1
    exact Nat.mul_div_cancel' (hp.dvd_choose_self (by simpa using (Finset.mem_Ioo.mp hi).1.ne')
      (Finset.mem_Ioo.mp hi).2)
  calc
    (p : R) * dividedBinomial p x y =
        ∑ i ∈ Finset.Ioo 0 p, x ^ i * y ^ (p - i) * (p.choose i : R) := by
      rw [dividedBinomial, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      calc
        (p : R) * (((p.choose i / p : ℕ) : R) * x ^ i * y ^ (p - i)) =
            ((p : R) * ((p.choose i / p : ℕ) : R)) * (x ^ i * y ^ (p - i)) := by ring
        _ = _ := by rw [hcoeff i hi]; ring
    _ = (x + y) ^ p - x ^ p - y ^ p := by
      have hinterval : Finset.Ioo 0 p = Finset.Ico 1 p := by
        ext i
        simp only [Finset.mem_Ioo, Finset.mem_Ico]
        omega
      rw [hinterval, Finset.sum_Ico_eq_sub _ hp.one_lt.le, Finset.sum_range_one]
      have hpow := add_pow x y p
      rw [Finset.sum_range_succ] at hpow
      simp only [Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one, mul_one] at hpow
      rw [hpow]
      simp only [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul]
      ring

lemma dividedBinomial_cocycle {R : Type*} [CommRing R] {p : ℕ}
    (hp : p.Prime) (x y z : R) :
    dividedBinomial p (x + y) z + dividedBinomial p x y =
      dividedBinomial p y z + dividedBinomial p x (y + z) := by
  let Q := MvPolynomial (Fin 3) ℤ
  let X : Fin 3 → Q := MvPolynomial.X
  have h : dividedBinomial p (X 0 + X 1) (X 2) + dividedBinomial p (X 0) (X 1) =
      dividedBinomial p (X 1) (X 2) + dividedBinomial p (X 0) (X 1 + X 2) := by
    apply mul_left_cancel₀ (show (p : Q) ≠ 0 from Nat.cast_ne_zero.mpr hp.ne_zero)
    simp only [mul_add, mul_dividedBinomial (R := Q) hp, add_assoc]
    ring
  let f : Q →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) ![x, y, z]
  have hf := congrArg f h
  have h0 : f (X 0) = x :=
    MvPolynomial.eval₂Hom_X' (Int.castRingHom R) ![x, y, z] 0
  have h1 : f (X 1) = y :=
    MvPolynomial.eval₂Hom_X' (Int.castRingHom R) ![x, y, z] 1
  have h2 : f (X 2) = z :=
    MvPolynomial.eval₂Hom_X' (Int.castRingHom R) ![x, y, z] 2
  simpa only [map_add, map_dividedBinomial f p, h0, h1, h2] using hf

lemma dividedBinomial_smul {R : Type*} [CommRing R]
    (p : ℕ) (a x y : R) :
    dividedBinomial p (a * x) (a * y) = a ^ p * dividedBinomial p x y := by
  simp only [dividedBinomial, mul_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hip : i ≤ p := (Finset.mem_Ioo.mp hi).2.le
  have ha : a ^ i * a ^ (p - i) = a ^ p := by
    rw [← pow_add, Nat.add_sub_of_le hip]
  calc
    _ = (a ^ i * a ^ (p - i)) * (((p.choose i / p : ℕ) : R) * x ^ i * y ^ (p - i)) := by ring
    _ = _ := by rw [ha]

lemma dividedBinomial_sum_int {p : ℕ} (hp : p.Prime) :
    (∑ j ∈ Finset.range p, dividedBinomial p (1 : ℤ) (j : ℤ)) =
      (p : ℤ) ^ (p - 1) - 1 := by
  apply mul_left_cancel₀ (show (p : ℤ) ≠ 0 from Nat.cast_ne_zero.mpr hp.ne_zero)
  rw [Finset.mul_sum]
  simp only [mul_dividedBinomial hp, one_pow]
  have hsum : (∑ j ∈ Finset.range p, ((1 + (j : ℤ)) ^ p - 1 - (j : ℤ) ^ p)) =
      (p : ℤ) ^ p - p := by
    calc
      _ = (∑ j ∈ Finset.range p, ((((j + 1 : ℕ) : ℤ) ^ p) - (j : ℤ) ^ p)) -
          ∑ _j ∈ Finset.range p, (1 : ℤ) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [Nat.cast_add, Nat.cast_one]
        rw [add_comm (j : ℤ) 1]
        ring
      _ = (p : ℤ) ^ p - p := by
        rw [Finset.sum_range_sub (fun j : ℕ => (j : ℤ) ^ p) p]
        simp [hp.ne_zero]
  rw [hsum]
  have hpow : (p : ℤ) ^ p = (p : ℤ) * (p : ℤ) ^ (p - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hp.one_lt.le]
  rw [hpow]
  ring

lemma dividedBinomial_sum_charP {R : Type*} [CommRing R] {p : ℕ}
    (hp : p.Prime) [CharP R p] :
    (∑ j ∈ Finset.range p, dividedBinomial p (1 : R) (j : R)) = -1 := by
  have hmap := congrArg (Int.castRingHom R) (dividedBinomial_sum_int hp)
  have hpos : p - 1 ≠ 0 := by have := hp.two_le; omega
  simpa only [map_sum, map_dividedBinomial (Int.castRingHom R) p,
    map_sub, map_pow, map_natCast, map_one, CharP.cast_eq_zero R p,
    zero_pow hpos, zero_sub] using hmap
end LowerSphereCyclic
end

end OAI
