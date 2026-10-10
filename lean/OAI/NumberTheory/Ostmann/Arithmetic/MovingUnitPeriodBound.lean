import OAI.NumberTheory.Ostmann.Arithmetic.MovingSignedUnits
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSamplePeriod

namespace OAI

/-! # Size of the full giant-unit period, including regular and outside slots -/

namespace Ostmann
open scoped Classical

/-- Bounds the current regular product at every actual state of the tree. -/
def MovingSlotData.RegularBound {σ : Type*} (value : σ → ℕ) (B : ℕ) :
    {n : ℕ} → MovingSlotData σ n → Prop
  | _, T@(.leaf _ _) => MovingSlotReversal.naturalProduct value T.regularSlots ≤ B
  | _, T@(.node _ _ _ _ left right) =>
      MovingSlotReversal.naturalProduct value T.regularSlots ≤ B ∧
        left.RegularBound value B ∧ right.RegularBound value B

def movingGiantUnitExponent : ℕ → ℕ
  | 0 => 3
  | n + 1 => (2 ^ (n + 2) - 1) + 4 + 2 * movingGiantUnitExponent n

theorem MovingSlotData.frequencyProduct_bound {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) (B : ℕ)
    (hfreq : T.Frequencies (fun s => s.natAbs ≤ B)) :
    T.frequencyProduct.natAbs ≤ B ^ (2 ^ (n + 1) - 1) := by
  induction T with
  | leaf s regular => simpa [frequencyProduct, Frequencies] using hfreq
  | @node n s CL CR u left right ihL ihR =>
    have he : 1 + (2 ^ (n + 1) - 1) + (2 ^ (n + 1) - 1) = 2 ^ (n + 1 + 1) - 1 := by
      have hp : 1 ≤ 2 ^ (n + 1) := Nat.one_le_pow _ _ (by omega)
      rw [pow_succ]
      omega
    simp only [frequencyProduct, Int.natAbs_mul]
    calc
      _ ≤ B * B ^ (2 ^ (n + 1) - 1) * B ^ (2 ^ (n + 1) - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul hfreq.1 (ihL hfreq.2.1)) (ihR hfreq.2.2)
      _ = B ^ (1 + (2 ^ (n + 1) - 1) + (2 ^ (n + 1) - 1)) := by
        simp only [pow_add, pow_one]
      _ = _ := congrArg (B ^ ·) he

theorem MovingSlotData.frequencyProduct_ne_zero {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) : T.frequencyProduct ≠ 0 := by
  induction T with
  | leaf => exact hf
  | node s CL CR u left right ihL ihR =>
    exact mul_ne_zero (mul_ne_zero hf.1 (ihL hf.2.1)) (ihR hf.2.2)

theorem movingGiantUnitPeriod_ne_zero {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (hout : outside.prod ≠ 0)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) :
    movingGiantUnitPeriod value outside T ≠ 0 := by
  induction T with
  | leaf s regular =>
    exact mul_ne_zero (mul_ne_zero hf (by exact_mod_cast
      MovingSlotReversal.naturalProduct_ne_zero value hvalue regular)) (by exact_mod_cast hout)
  | node s CL CR u left right ihL ihR =>
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · exact mul_ne_zero (mul_ne_zero
            (MovingSlotData.frequencyProduct_ne_zero _ hf)
            (by exact_mod_cast MovingSlotReversal.naturalProduct_ne_zero value hvalue (CL ++ CR)))
            (by exact_mod_cast hout)
        · exact mul_ne_zero hf.1 (by exact_mod_cast MovingSlotReversal.naturalProduct_ne_zero value hvalue u)
      · exact ihL hf.2.1
    · exact ihR hf.2.2

theorem movingGiantUnitPeriod_bound {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (B : ℕ)
    (hfreq : T.Frequencies (fun s => s.natAbs ≤ B))
    (hcomp : T.CompensationBound value B) (hregular : T.RegularBound value B)
    (hout : outside.prod ≤ B) :
    (movingGiantUnitPeriod value outside T).natAbs ≤ B ^ movingGiantUnitExponent n := by
  induction T with
  | leaf s regular =>
    simp only [movingGiantUnitPeriod, MovingSlotData.frequencyProduct, Int.natAbs_mul, Int.natAbs_natCast]
    have h := Nat.mul_le_mul (Nat.mul_le_mul hfreq hregular) hout
    simpa [movingGiantUnitExponent, pow_succ] using h
  | @node n s CL CR u left right ihL ihR =>
    have hfp := MovingSlotData.frequencyProduct_bound (MovingSlotData.node s CL CR u left right) B hfreq
    have hl := ihL hfreq.2.1 hcomp.2.1 hregular.2.1
    have hr := ihR hfreq.2.2 hcomp.2.2 hregular.2.2
    simp only [movingGiantUnitPeriod, Int.natAbs_mul, Int.natAbs_natCast]
    calc
      _ ≤ (B ^ (2 ^ (n + 2) - 1) * B * B) * (B * B) *
          B ^ movingGiantUnitExponent n * B ^ movingGiantUnitExponent n :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
          (Nat.mul_le_mul (Nat.mul_le_mul hfp hregular.1) hout)
          (Nat.mul_le_mul hfreq.1 hcomp.1)) hl) hr
      _ = B ^ movingGiantUnitExponent (n + 1) := by
        rw [movingGiantUnitExponent, two_mul]
        simp only [pow_add]
        ring

end Ostmann

end OAI
