import Mathlib.Data.Int.GCD
import OAI.NumberTheory.Jacobsthal.Estimates.PairCollisionCount

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman

theorem stdAddChar_bezout (m n : ℕ) [NeZero m] [NeZero n]
    (A B z : ℤ) (hab : (m : ℤ)*A + (n : ℤ)*B = 1) :
    ZMod.stdAddChar (z : ZMod (m*n)) =
      ZMod.stdAddChar ((B*z : ℤ) : ZMod m) *
        ZMod.stdAddChar ((A*z : ℤ) : ZMod n) := by
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hc : (m : ℂ)*(A : ℂ) + (n : ℂ)*(B : ℂ) = 1 := by exact_mod_cast hab
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  linear_combination -(z : ℂ) * hc

theorem stdAddChar_crt (m n : ℕ) [NeZero m] [NeZero n] (hmn : m.Coprime n) :
    (ZMod.stdAddChar : AddChar (ZMod (m*n)) ℂ) =
      (productChar
        (ZMod.stdAddChar.mulShift (Nat.gcdB m n : ZMod m))
        (ZMod.stdAddChar.mulShift (Nat.gcdA m n : ZMod n))).compAddMonoidHom
          (ZMod.chineseRemainder hmn).toAddMonoidHom := by
  have hab : (m : ℤ)*Nat.gcdA m n + (n : ℤ)*Nat.gcdB m n = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hmn.gcd_eq_one]
    rfl
  ext x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  simpa [productChar, AddChar.compAddMonoidHom_apply, AddChar.mulShift_apply,
    ← Int.cast_mul] using stdAddChar_bezout m n (Nat.gcdA m n) (Nat.gcdB m n) z hab

end ErdosKloosterman

end

end Erdos970

end OAI
