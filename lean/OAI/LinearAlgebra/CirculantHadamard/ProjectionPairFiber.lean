import Mathlib.Data.ZMod.Basic
import Lean.Elab.Tactic.Omega

namespace OAI

/-!
# The two fibers of reduction modulo half the order

Reduction from `ZMod (2 * m)` to `ZMod m` has exactly the two usual lifts
of each element when `m` is positive.
-/

namespace CirculantHadamard

/-- The fiber of reduction modulo `m` consists of its two canonical lifts. -/
theorem zmod_double_cast_eq_iff {m : ℕ} (hm : 0 < m) (h : m ∣ 2 * m)
    (x : ZMod (2 * m)) (j : ZMod m) :
    ZMod.castHom h (ZMod m) x = j ↔
      x = (j.val : ZMod (2 * m)) ∨ x = ((j.val + m : ℕ) : ZMod (2 * m)) := by
  let : NeZero m := ⟨by omega⟩
  let : NeZero (2 * m) := ⟨by omega⟩
  have hxlt : x.val < 2 * m := ZMod.val_lt x
  have hjlt : j.val < m := ZMod.val_lt j
  constructor
  · intro hx
    have hmod : x.val % m = j.val := by
      simpa only [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast] using
        congrArg ZMod.val hx
    by_cases hsmall : x.val < m
    · left
      have hval : x.val = j.val := by
        simpa only [Nat.mod_eq_of_lt hsmall] using hmod
      rw [← hval, ZMod.natCast_zmod_val]
    · right
      have hmle : m ≤ x.val := by omega
      have hsub : x.val - m < m := by omega
      rw [Nat.mod_eq_sub_mod hmle, Nat.mod_eq_of_lt hsub] at hmod
      have hval : x.val = j.val + m := by omega
      rw [← hval, ZMod.natCast_zmod_val]
  · rintro (rfl | rfl)
    · simp only [map_natCast, ZMod.natCast_zmod_val]
    · rw [map_natCast]
      simp only [Nat.cast_add, ZMod.natCast_self, add_zero, ZMod.natCast_zmod_val]

/-- The two canonical lifts into the group of twice the order are distinct. -/
theorem zmod_double_lifts_ne {m : ℕ} (hm : 0 < m) (j : ZMod m) :
    (j.val : ZMod (2 * m)) ≠ ((j.val + m : ℕ) : ZMod (2 * m)) := by
  let : NeZero m := ⟨by omega⟩
  have hjlt : j.val < m := ZMod.val_lt j
  intro h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast, ZMod.val_natCast,
    Nat.mod_eq_of_lt (show j.val < 2 * m by omega),
    Nat.mod_eq_of_lt (show j.val + m < 2 * m by omega)] at hv
  omega

end CirculantHadamard

end OAI
