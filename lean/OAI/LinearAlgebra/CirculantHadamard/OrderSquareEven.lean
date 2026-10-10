import OAI.LinearAlgebra.CirculantHadamard.CyclicNorm
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.NormNum

namespace OAI

universe uIota

/-!
# Square and even order from actual circulant sign rows

Augmentation of the cyclic norm identity gives an integer square. A
nonidentity correlation is a zero sum of signs; reduction modulo two makes
its number of summands even. Both conclusions follow from the actual real
circulant Hadamard matrix predicate.
-/

namespace CirculantHadamard

open scoped BigOperators

private theorem positive_nat_square_of_int_square {n : ℕ} (hn : 0 < n)
    (z : ℤ) (hz : z ^ 2 = (n : ℤ)) :
    ∃ m : ℕ, 0 < m ∧ n = m ^ 2 := by
  have hsq : z.natAbs ^ 2 = n := by
    simpa only [Int.natAbs_pow, Int.natAbs_natCast] using congrArg Int.natAbs hz
  have hm : z.natAbs ≠ 0 := by
    intro hm
    have hzero : n = 0 := by simpa only [hm, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hsq.symm
    exact (Nat.ne_of_gt hn) hzero
  exact ⟨z.natAbs, Nat.pos_of_ne_zero hm, hsq.symm⟩

private theorem even_card_of_sign_sum_zero {ι : Type uIota} [Fintype ι]
    (f : ι → ℤ) (hsign : ∀ i, IsSign (f i)) (hsum : ∑ i, f i = 0) :
    Even (Fintype.card ι) := by
  classical
  let φ : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)
  have hcast (i : ι) : φ (f i) = 1 := by
    rcases hsign i with h | h
    · rw [h, map_one]
    · rw [h, map_neg, map_one]
      exact ZMod.neg_eq_self_mod_two (1 : ZMod 2)
  have hcard : (Fintype.card ι : ZMod 2) = 0 := by
    have h := congrArg φ hsum
    simpa only [map_sum, hcast, map_zero, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one] using h
  exact even_iff_two_dvd.mpr ((ZMod.natCast_eq_zero_iff _ _).mp hcard)

/-- A nonidentity norm coefficient is a zero sum of exactly `n` signs. -/
theorem order_even_of_sign_norm {n : ℕ} [NeZero n] (hn : 1 < n)
    (f : CyclicRing.Elem ℤ n) (hsign : CyclicSignRow f)
    (hnorm : f * CyclicRing.ringStar f = CyclicRing.scalar n (n : ℤ)) :
    Even n := by
  classical
  let : Fact (1 < n) := ⟨hn⟩
  have hcorr : (∑ a : ZMod n, f.coeff a * f.coeff (a - 1)) = 0 := by
    have h := congrArg (fun g : CyclicRing.Elem ℤ n => g.coeff 1) hnorm
    simpa only [CyclicRing.mul_ringStar_apply, star_trivial, CyclicRing.scalar_apply,
      ite_eq_right (one_ne_zero : (1 : ZMod n) ≠ 0)] using h
  have heven := even_card_of_sign_sum_zero (fun a : ZMod n => f.coeff a * f.coeff (a - 1))
    (fun a => by
      rcases hsign a with ha | ha <;> rcases hsign (a - 1) with hb | hb <;>
        simp [IsSign, ha, hb]) hcorr
  simpa only [ZMod.card] using heven

/-- Square and even order from the actual integer sign norm equation. -/
theorem order_square_even_of_sign_norm {n : ℕ} [NeZero n] (hn : 1 < n)
    (f : CyclicRing.Elem ℤ n) (hsign : CyclicSignRow f)
    (hnorm : f * CyclicRing.ringStar f = CyclicRing.scalar n (n : ℤ)) :
    (∃ m : ℕ, 0 < m ∧ n = m ^ 2) ∧ Even n := by
  constructor
  · exact positive_nat_square_of_int_square (lt_trans Nat.zero_lt_one hn)
      (CyclicRing.augmentation n f) (CyclicRing.augmentation_norm f (n : ℤ) hnorm)
  · exact order_even_of_sign_norm hn f hsign hnorm

/-- A nontrivial actual real circulant sign Hadamard matrix has positive
square order and even order. The integer row and its norm identity are
obtained from the proved matrix correspondence. -/
theorem order_square_even {n : ℕ} (hn : 1 < n)
    (h : ExistsRealCirculantHadamard n) :
    (∃ m : ℕ, 0 < m ∧ n = m ^ 2) ∧ Even n := by
  let : NeZero n := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn)⟩
  obtain ⟨f, hsign, hnorm⟩ := exists_cyclicSignRow_iff_real.mpr h
  exact order_square_even_of_sign_norm hn f hsign hnorm

end CirculantHadamard

end OAI
