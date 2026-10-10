import Mathlib.Algebra.Field.ZMod

namespace OAI

namespace PeriodicTilingThree

def primeDifferencePairs (q m : ℕ) [Fact q.Prime]
    (hq : q = 2 * m + 1) (d : ZMod q) (hd : d ≠ 0) :
    (Fin m × Fin 2) ↪ ZMod q where
  toFun p := ((2 * p.1.val + p.2.val : ℕ) : ZMod q) * d
  inj' := by
    rintro ⟨j, b⟩ ⟨k, c⟩ h
    have hj := j.isLt
    have hk := k.isLt
    have hb := b.isLt
    have hc := c.isLt
    have hjb : 2 * j.val + b.val < q := by omega
    have hkc : 2 * k.val + c.val < q := by omega
    have hcast : ((2 * j.val + b.val : ℕ) : ZMod q) =
        ((2 * k.val + c.val : ℕ) : ZMod q) :=
      mul_right_cancel₀ hd h
    have hindices := congrArg ZMod.val hcast
    rw [ZMod.val_natCast_of_lt hjb, ZMod.val_natCast_of_lt hkc] at hindices
    apply Prod.ext
    · apply Fin.ext
      change j.val = k.val
      omega
    · apply Fin.ext
      change b.val = c.val
      omega

@[simp]
theorem primeDifferencePairs_apply (q m : ℕ) [Fact q.Prime]
    (hq : q = 2 * m + 1) (d : ZMod q) (hd : d ≠ 0)
    (j : Fin m) (b : Fin 2) :
    primeDifferencePairs q m hq d hd (j, b) =
      ((2 * j.val + b.val : ℕ) : ZMod q) * d := rfl

theorem primeDifferencePairs_step (q m : ℕ) [Fact q.Prime]
    (hq : q = 2 * m + 1) (d : ZMod q) (hd : d ≠ 0) (j : Fin m) :
    primeDifferencePairs q m hq d hd (j, 1) -
      primeDifferencePairs q m hq d hd (j, 0) = d := by
  change ((2 * j.val + 1 : ℕ) : ZMod q) * d -
    ((2 * j.val : ℕ) : ZMod q) * d = d
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_sub_cancel_left]

end PeriodicTilingThree

end OAI
