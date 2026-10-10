import Mathlib.Tactic.Ring
import OAI.Computability.PerfectCompleteness.Foundations.CanonicalDictionaryNames

namespace OAI

section

namespace PerfectCompleteness.SignedCostEnvelope

def payloadCoeff (w : Nat) : Nat :=
  (1 + 2 ^ (11 ^ w) + 6 * w) * (w + 3) + 1

def streamCoeff (w d : Nat) : Nat := (2 * payloadCoeff w + 2) * d

def endpointBound (w T count : Nat) : Nat :=
  8 * w * (T + 1) + 4 * w + 2 +
    2 * (CanonicalVertexNames.payloadBound w T + 1) +
    3 * (CanonicalDictionaryNames.streamBound w T count) ^ 2 +
    16 * CanonicalDictionaryNames.streamBound w T count + 12

def endpointCoeff (w d : Nat) : Nat :=
  12 * w + 2 * payloadCoeff w + 3 * (streamCoeff w d) ^ 2 +
    16 * streamCoeff w d + 16

def bodyBound (w d T : Nat) : Nat :=
  72 * w * (T + 1) + d * (2 * endpointBound w T (d * (T + 1) ^ w) + 4) +
    7 * w * (T + 2) + 2

def bodyCoeff (w d : Nat) : Nat := 86 * w + d * (2 * endpointCoeff w d + 4) + 2

def degree (w : Nat) : Nat := 2 * w + 2

private theorem le_scaled (a : Nat) {b : Nat} (hb : 1 ≤ b) : a ≤ a * b := by
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left a hb

private theorem one_le_envelope (w T : Nat) : 1 ≤ (T + 1) ^ degree w :=
  Nat.one_le_pow (degree w) (T + 1) (Nat.zero_lt_succ T)

private theorem input_le_envelope (w T : Nat) : T + 1 ≤ (T + 1) ^ degree w :=
  Nat.le_pow (show 0 < degree w by unfold degree; omega)

private theorem streamPower_le_envelope (w T : Nat) :
    (T + 1) ^ (w + 1) ≤ (T + 1) ^ degree w :=
  Nat.pow_le_pow_right (Nat.zero_lt_succ T) (by unfold degree; omega)

theorem payloadBound_le (w T : Nat) :
    CanonicalVertexNames.payloadBound w T ≤ payloadCoeff w * (T + 1) := by
  have hone : 1 ≤ T + 1 := Nat.succ_le_succ (Nat.zero_le T)
  have hmax : max w (max T 2) + 1 ≤ w + (T + 1) + 2 := by omega
  have hfactor : max w (max T 2) + 1 ≤ (w + 3) * (T + 1) := by
    calc
      max w (max T 2) + 1 ≤ w + (T + 1) + 2 := hmax
      _ ≤ w * (T + 1) + (T + 1) + 2 * (T + 1) :=
        Nat.add_le_add (Nat.add_le_add_right (le_scaled w hone) (T + 1))
          (le_scaled 2 hone)
      _ = (w + 3) * (T + 1) := by ring
  calc
    CanonicalVertexNames.payloadBound w T =
        (1 + 2 ^ (11 ^ w) + 6 * w) * (max w (max T 2) + 1) + 1 := rfl
    _ ≤ (1 + 2 ^ (11 ^ w) + 6 * w) * ((w + 3) * (T + 1)) + (T + 1) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hfactor) hone
    _ = payloadCoeff w * (T + 1) := by unfold payloadCoeff; ring

theorem streamBound_le (w d T : Nat) :
    CanonicalDictionaryNames.streamBound w T (d * (T + 1) ^ w) ≤
      streamCoeff w d * (T + 1) ^ (w + 1) := by
  have hone : 1 ≤ T + 1 := Nat.succ_le_succ (Nat.zero_le T)
  have hfactor : 2 * CanonicalVertexNames.payloadBound w T + 2 ≤
      (2 * payloadCoeff w + 2) * (T + 1) := by
    calc
      2 * CanonicalVertexNames.payloadBound w T + 2 ≤
          2 * (payloadCoeff w * (T + 1)) + 2 * (T + 1) :=
        Nat.add_le_add (Nat.mul_le_mul_left 2 (payloadBound_le w T)) (le_scaled 2 hone)
      _ = (2 * payloadCoeff w + 2) * (T + 1) := by ring
  calc
    CanonicalDictionaryNames.streamBound w T (d * (T + 1) ^ w) =
        (2 * CanonicalVertexNames.payloadBound w T + 2) * (d * (T + 1) ^ w) := rfl
    _ ≤ ((2 * payloadCoeff w + 2) * (T + 1)) * (d * (T + 1) ^ w) :=
      Nat.mul_le_mul_right _ hfactor
    _ = streamCoeff w d * (T + 1) ^ (w + 1) := by
      rw [Nat.pow_succ]
      unfold streamCoeff
      ring

theorem endpointBound_le (w d T : Nat) :
    endpointBound w T (d * (T + 1) ^ w) ≤
      endpointCoeff w d * (T + 1) ^ degree w := by
  have hone := one_le_envelope w T
  have hinput := input_le_envelope w T
  have hpayload : CanonicalVertexNames.payloadBound w T ≤
      payloadCoeff w * (T + 1) ^ degree w :=
    (payloadBound_le w T).trans (Nat.mul_le_mul_left _ hinput)
  have hstream := streamBound_le w d T
  have hstreamLinear : CanonicalDictionaryNames.streamBound w T (d * (T + 1) ^ w) ≤
      streamCoeff w d * (T + 1) ^ degree w :=
    hstream.trans (Nat.mul_le_mul_left _ (streamPower_le_envelope w T))
  have hsquare : (CanonicalDictionaryNames.streamBound w T (d * (T + 1) ^ w)) ^ 2 ≤
      (streamCoeff w d) ^ 2 * (T + 1) ^ degree w := by
    calc
      (CanonicalDictionaryNames.streamBound w T (d * (T + 1) ^ w)) ^ 2 ≤
          (streamCoeff w d * (T + 1) ^ (w + 1)) ^ 2 :=
        Nat.pow_le_pow_left hstream 2
      _ = (streamCoeff w d) ^ 2 * (T + 1) ^ degree w := by
        rw [Nat.mul_pow, ← Nat.pow_mul]
        have hexp : (w + 1) * 2 = degree w := by unfold degree; omega
        rw [hexp]
  have hstart : 8 * w * (T + 1) + 4 * w + 2 ≤
      (12 * w + 2) * (T + 1) ^ degree w := by
    calc
      8 * w * (T + 1) + 4 * w + 2 ≤
          (8 * w) * (T + 1) ^ degree w + (4 * w) * (T + 1) ^ degree w +
            2 * (T + 1) ^ degree w :=
        Nat.add_le_add
          (Nat.add_le_add (Nat.mul_le_mul_left (8 * w) hinput) (le_scaled (4 * w) hone))
          (le_scaled 2 hone)
      _ = (12 * w + 2) * (T + 1) ^ degree w := by ring
  have hpayloadTerm : 2 * (CanonicalVertexNames.payloadBound w T + 1) ≤
      (2 * payloadCoeff w + 2) * (T + 1) ^ degree w := by
    calc
      2 * (CanonicalVertexNames.payloadBound w T + 1) ≤
          2 * (payloadCoeff w * (T + 1) ^ degree w + (T + 1) ^ degree w) :=
        Nat.mul_le_mul_left 2 (Nat.add_le_add hpayload hone)
      _ = (2 * payloadCoeff w + 2) * (T + 1) ^ degree w := by ring
  calc
    endpointBound w T (d * (T + 1) ^ w) ≤
        (12 * w + 2) * (T + 1) ^ degree w +
          (2 * payloadCoeff w + 2) * (T + 1) ^ degree w +
          3 * ((streamCoeff w d) ^ 2 * (T + 1) ^ degree w) +
          16 * (streamCoeff w d * (T + 1) ^ degree w) + 12 * (T + 1) ^ degree w :=
      Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add (Nat.add_le_add hstart hpayloadTerm) (Nat.mul_le_mul_left 3 hsquare))
          (Nat.mul_le_mul_left 16 hstreamLinear))
        (le_scaled 12 hone)
    _ = endpointCoeff w d * (T + 1) ^ degree w := by unfold endpointCoeff; ring

theorem bodyBound_le (w d T : Nat) :
    bodyBound w d T ≤ bodyCoeff w d * (T + 1) ^ degree w := by
  have hone := one_le_envelope w T
  have hinput := input_le_envelope w T
  have hendpoint := endpointBound_le w d T
  have hbody : d * (2 * endpointBound w T (d * (T + 1) ^ w) + 4) ≤
      (d * (2 * endpointCoeff w d + 4)) * (T + 1) ^ degree w := by
    calc
      d * (2 * endpointBound w T (d * (T + 1) ^ w) + 4) ≤
          d * (2 * (endpointCoeff w d * (T + 1) ^ degree w) + 4 * (T + 1) ^ degree w) :=
        Nat.mul_le_mul_left d
          (Nat.add_le_add (Nat.mul_le_mul_left 2 hendpoint) (le_scaled 4 hone))
      _ = (d * (2 * endpointCoeff w d + 4)) * (T + 1) ^ degree w := by ring
  have hcleanup : 7 * w * (T + 2) ≤ (14 * w) * (T + 1) ^ degree w := by
    calc
      7 * w * (T + 2) = (7 * w) * ((T + 1) + 1) := rfl
      _ ≤ (7 * w) * ((T + 1) ^ degree w + (T + 1) ^ degree w) :=
        Nat.mul_le_mul_left (7 * w) (Nat.add_le_add hinput hone)
      _ = (14 * w) * (T + 1) ^ degree w := by ring
  calc
    bodyBound w d T ≤ (72 * w) * (T + 1) ^ degree w +
        (d * (2 * endpointCoeff w d + 4)) * (T + 1) ^ degree w +
        (14 * w) * (T + 1) ^ degree w + 2 * (T + 1) ^ degree w :=
      Nat.add_le_add
        (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left (72 * w) hinput) hbody) hcleanup)
        (le_scaled 2 hone)
    _ = bodyCoeff w d * (T + 1) ^ degree w := by unfold bodyCoeff; ring

end PerfectCompleteness.SignedCostEnvelope

end

end OAI
