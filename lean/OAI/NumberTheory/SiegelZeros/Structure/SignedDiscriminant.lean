import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import OAI.NumberTheory.SiegelZeros.Determinants.ThetaDivisibility

namespace OAI

namespace SiegelZeros


namespace Awei.W39

def signedOddDiscriminant (m : ℕ) : ℤ := ZMod.χ₄ m * (m : ℤ)

theorem signedOddDiscriminant_one_mod_four (m : ℕ) (hm : m % 4 = 1) :
    signedOddDiscriminant m = (m : ℤ) := by
  simp only [signedOddDiscriminant, ZMod.χ₄_nat_one_mod_four hm, one_mul]

theorem signedOddDiscriminant_three_mod_four (m : ℕ) (hm : m % 4 = 3) :
    signedOddDiscriminant m = -(m : ℤ) := by
  simp only [signedOddDiscriminant, ZMod.χ₄_nat_three_mod_four hm, neg_one_mul]

theorem legendre_signedOddDiscriminant (p m : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (hm : Odd m) :
    legendreSym p (signedOddDiscriminant m) = jacobiSym (p : ℤ) m := by
  rw [signedOddDiscriminant, legendreSym.mul,
    jacobiSym.legendreSym.to_jacobiSym p (ZMod.χ₄ m), jacobiSym.legendreSym.to_jacobiSym p (m : ℤ)]
  exact (jacobiSym.quadratic_reciprocity'
    ((Fact.out : p.Prime).odd_of_ne_two hp) hm).symm

theorem legendre_remove_square_factor (p : ℕ) [Fact p.Prime]
    (D d t : ℤ) (hD : D = d * t ^ 2) (hgood : (D : ZMod p) ≠ 0) :
    legendreSym p D = legendreSym p d := by
  have ht : (t : ZMod p) ≠ 0 := by
    intro hz
    apply hgood
    simp only [hD, Int.cast_mul, Int.cast_pow, hz, zero_pow (by decide : 2 ≠ 0), mul_zero]
  rw [hD, legendreSym.mul, legendreSym.sq_one' p ht, mul_one]

theorem legendre_four_mul (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (D : ℤ) :
    legendreSym p (4 * D) = legendreSym p D := by
  have ht : ((2 : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by
      simpa only [Int.cast_ofNat, Nat.cast_ofNat] using hz)
    exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hd)
  have hs : legendreSym p 4 = 1 := by
    simpa only [show (2 : ℤ) ^ 2 = 4 by decide] using legendreSym.sq_one' p ht
  rw [legendreSym.mul, hs, one_mul]

theorem legendre_neg_four_signedOddDiscriminant (p m : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (hm : Odd m) :
    legendreSym p (-4 * signedOddDiscriminant m) =
      ZMod.χ₄ p * jacobiSym (p : ℤ) m := by
  rw [show -4 * signedOddDiscriminant m = 4 * ((-1) * signedOddDiscriminant m) by
    simp only [neg_mul, one_mul, mul_neg]]
  rw [legendre_four_mul p hp, legendreSym.mul, legendreSym.at_neg_one hp,
    legendre_signedOddDiscriminant p m hp hm]

theorem legendre_eight_signedOddDiscriminant (p m : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (hm : Odd m) :
    legendreSym p (8 * signedOddDiscriminant m) =
      ZMod.χ₈ p * jacobiSym (p : ℤ) m := by
  rw [show 8 * signedOddDiscriminant m = 4 * (2 * signedOddDiscriminant m) by
    rw [← mul_assoc]; rfl]
  rw [legendre_four_mul p hp, legendreSym.mul, legendreSym.at_two hp,
    legendre_signedOddDiscriminant p m hp hm]

theorem legendre_neg_eight_signedOddDiscriminant (p m : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (hm : Odd m) :
    legendreSym p (-8 * signedOddDiscriminant m) =
      ZMod.χ₈' p * jacobiSym (p : ℤ) m := by
  rw [show -8 * signedOddDiscriminant m = 4 * ((-2) * signedOddDiscriminant m) by
    rw [← mul_assoc]; rfl]
  rw [legendre_four_mul p hp, legendreSym.mul, legendreSym.at_neg_two hp,
    legendre_signedOddDiscriminant p m hp hm]

end Awei.W39


end SiegelZeros

end OAI
