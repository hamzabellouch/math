import OAI.NumberTheory.JointDickman.Arithmetic.PrimeDigitDecomposition

namespace OAI

/-! # Arithmetic reconstruction of prime-square digit tests -/

namespace JointDickman

theorem primeDigits_first {p : ℕ} [NeZero p] (u : ℕ) :
    (primeDigits p (u : ZMod (p^2))).1 = (u : ZMod p) := by
  change (((u : ZMod (p^2)).val : ℕ) : ZMod p) = (u : ZMod p)
  rw [ZMod.val_natCast,← ZMod.natCast_mod _ p,← ZMod.natCast_mod u p]
  congr 1
  exact Nat.mod_mod_of_dvd u (dvd_pow_self _ (by omega : 2 ≠ 0))

theorem prime_square_affine_digits {p : ℕ} [NeZero p] (u : ℕ) (c b i : ℤ) :
    (p : ℤ)^2 ∣ c*((u : ℤ)+i)-b ↔
    (p : ℤ)^2 ∣ c*((primeDigits p (u : ZMod (p^2))).1.val+
      (p : ℤ)*(primeDigits p (u : ZMod (p^2))).2.val+i)-b := by
  have he := join_primeDigits (u : ZMod (p^2))
  change (((primeDigits p (u : ZMod (p^2))).1.val+
    p*(primeDigits p (u : ZMod (p^2))).2.val : ℕ) : ZMod (p^2)) = (u : ZMod (p^2)) at he
  have hv : ((c*((u : ℤ)+i)-b : ℤ) : ZMod (p^2)) =
      ((c*((primeDigits p (u : ZMod (p^2))).1.val+
        (p : ℤ)*(primeDigits p (u : ZMod (p^2))).2.val+i)-b : ℤ) : ZMod (p^2)) := by
    simp only [Int.cast_sub,Int.cast_mul,Int.cast_add,Int.cast_natCast]
    have he' := he
    push_cast at he'
    conv_lhs => rw [← he']
  have hi (z : ℤ) : (z : ZMod (p^2)) = 0 ↔ (p : ℤ)^2 ∣ z := by
    have heq : ((p^2 : ℕ) : ℤ) = (p : ℤ)^2 := by simp
    rw [← heq]
    exact ZMod.intCast_zmod_eq_zero_iff_dvd z (p^2)
  rw [← hi,← hi,hv]

end JointDickman

end OAI
