import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.BinaryRationalNormalize

namespace OAI

section

namespace KS.W30.BinaryRational
open KS.W19 KS.W30.BinaryGCD

def normalizeDivisionPair (qr : List Bool × List Bool) : List Bool × List Bool :=
  (trimBits qr.1, trimBits qr.2)

theorem division_values_unique {a d q r : ℕ} (hd : 0 < d)
    (he : a = d * q + r) (hr : r < d) : q = a / d ∧ r = a % d := by
  constructor
  · rw [he, Nat.add_comm (d * q), Nat.add_mul_div_left _ _ hd,
      Nat.div_eq_of_lt hr, Nat.zero_add]
  · rw [he]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hr]

theorem normalizeDivisionPair_eq_divideBits (divisor xs : List Bool)
    (qr : List Bool × List Bool) (hd : 0 < bitsValue divisor)
    (he : bitsValue xs = bitsValue divisor * bitsValue qr.1 + bitsValue qr.2)
    (hr : bitsValue qr.2 < bitsValue divisor) :
    normalizeDivisionPair qr = normalizeDivisionPair (divideBits divisor xs) := by
  obtain ⟨hq, hr'⟩ := division_values_unique hd he hr
  apply Prod.ext
  · apply canonicalBits_injective (trimBits_canonical _) (trimBits_canonical _)
    simpa only [normalizeDivisionPair, trimBits_value, quotient_value _ _ hd] using hq
  · apply canonicalBits_injective (trimBits_canonical _) (trimBits_canonical _)
    simpa only [normalizeDivisionPair, trimBits_value, remainder_value _ _ hd] using hr'

end KS.W30.BinaryRational

end

end OAI
