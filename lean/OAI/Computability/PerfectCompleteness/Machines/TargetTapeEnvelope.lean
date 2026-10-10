import OAI.Computability.PerfectCompleteness.Foundations.SignedCostEnvelope

namespace OAI

section

namespace PerfectCompleteness.TargetTapeEnvelope

def outputBound (q E : Nat) : Nat :=
  2 * E + q + E + 4 + E * (2 * E + 2 * q * q + 2 * q + 2)

def bound (w q T E : Nat) : Nat :=
  T + 1 + CanonicalDictionaryNames.streamBound w T E +
    outputBound q E + (E + 1)

def coeff (w q D : Nat) : Nat :=
  SignedCostEnvelope.streamCoeff w D + 2 * D ^ 2 +
    (2 * q * q + 2 * q + 6) * D + q + 6

private theorem le_scaled (a : Nat) {b : Nat} (hb : 1 ≤ b) : a ≤ a * b := by
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left a hb

theorem bound_le (w q D T E : Nat) (hcount : E ≤ D * (T + 1) ^ w) :
    bound w q T E ≤ coeff w q D * (T + 1) ^ (2 * w + 2) := by
  have hone : 1 ≤ (T + 1) ^ (2 * w + 2) :=
    Nat.one_le_pow (2 * w + 2) (T + 1) (Nat.zero_lt_succ T)
  have hinput : T + 1 ≤ (T + 1) ^ (2 * w + 2) :=
    Nat.le_pow (show 0 < 2 * w + 2 by omega)
  have hcountLinear : E ≤ D * (T + 1) ^ (2 * w + 2) :=
    hcount.trans (Nat.mul_le_mul_left D
      (Nat.pow_le_pow_right (Nat.zero_lt_succ T) (by omega)))
  have hstream : CanonicalDictionaryNames.streamBound w T E ≤
      SignedCostEnvelope.streamCoeff w D * (T + 1) ^ (2 * w + 2) := by
    calc
      CanonicalDictionaryNames.streamBound w T E ≤
          CanonicalDictionaryNames.streamBound w T (D * (T + 1) ^ w) :=
        Nat.mul_le_mul_left _ hcount
      _ ≤ SignedCostEnvelope.streamCoeff w D * (T + 1) ^ (w + 1) :=
        SignedCostEnvelope.streamBound_le w D T
      _ ≤ SignedCostEnvelope.streamCoeff w D * (T + 1) ^ (2 * w + 2) :=
        Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (Nat.zero_lt_succ T) (by omega))
  have hsquare : E ^ 2 ≤ D ^ 2 * (T + 1) ^ (2 * w + 2) := by
    calc
      E ^ 2 ≤ (D * (T + 1) ^ w) ^ 2 := Nat.pow_le_pow_left hcount 2
      _ = D ^ 2 * (T + 1) ^ (w * 2) := by rw [Nat.mul_pow, ← Nat.pow_mul]
      _ ≤ D ^ 2 * (T + 1) ^ (2 * w + 2) :=
        Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (Nat.zero_lt_succ T) (by omega))
  calc
    bound w q T E = (T + 1) + CanonicalDictionaryNames.streamBound w T E +
        2 * E ^ 2 + (2 * q * q + 2 * q + 6) * E + (q + 5) := by
      unfold bound outputBound
      ring
    _ ≤ (T + 1) ^ (2 * w + 2) +
        SignedCostEnvelope.streamCoeff w D * (T + 1) ^ (2 * w + 2) +
        2 * (D ^ 2 * (T + 1) ^ (2 * w + 2)) +
        (2 * q * q + 2 * q + 6) * (D * (T + 1) ^ (2 * w + 2)) +
        (q + 5) * (T + 1) ^ (2 * w + 2) :=
      Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add (Nat.add_le_add hinput hstream) (Nat.mul_le_mul_left 2 hsquare))
          (Nat.mul_le_mul_left (2 * q * q + 2 * q + 6) hcountLinear))
        (le_scaled (q + 5) hone)
    _ = coeff w q D * (T + 1) ^ (2 * w + 2) := by
      unfold coeff
      ring

end PerfectCompleteness.TargetTapeEnvelope

end

end OAI
