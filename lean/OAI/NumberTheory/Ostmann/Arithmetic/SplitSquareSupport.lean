import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Group
import OAI.NumberTheory.Ostmann.Arithmetic.SimultaneousSquares
import OAI.NumberTheory.Ostmann.Arithmetic.ReducedFrequencySum

namespace OAI

/-! # From the actual split relation to its reduced square equation -/

namespace Ostmann

open scoped BigOperators Classical

theorem split_relation_gcd_eq {s v w x y : ℕ}
    (hx : x.Coprime s) (hy : y.Coprime s)
    (h : Nat.ModEq s (v * x) (w * y)) : v.gcd s = w.gcd s := by
  simpa only [hx.gcd_mul_right_cancel, hy.gcd_mul_right_cancel] using h.gcd_eq

theorem split_relation_common_gcd {s v w x y : ℕ}
    (hx : x.Coprime s) (hy : y.Coprime s)
    (h : Nat.ModEq s (v * x) (w * y)) : (v.gcd w).gcd s = v.gcd s := by
  rw [Nat.gcd_assoc, ← split_relation_gcd_eq hx hy h, ← Nat.gcd_assoc, Nat.gcd_self]

theorem split_relation_divide_gcd {s v w x y : ℕ} (hs : s ≠ 0)
    (hgcd : v.gcd s = w.gcd s) :
    Nat.ModEq s (v * x) (w * y) ↔
      Nat.ModEq (s / v.gcd s) ((v / v.gcd s) * x) ((w / v.gcd s) * y) := by
  have hd : v.gcd s ≠ 0 := Nat.gcd_ne_zero_right hs
  have hdv : v.gcd s ∣ v := Nat.gcd_dvd_left v s
  have hdw : v.gcd s ∣ w := hgcd ▸ Nat.gcd_dvd_left w s
  have hds : v.gcd s ∣ s := Nat.gcd_dvd_right v s
  simpa only [← Nat.mul_assoc, Nat.mul_div_cancel' hds,
    Nat.mul_div_cancel' hdv, Nat.mul_div_cancel' hdw] using
    (Nat.ModEq.mul_left_cancel_iff' (a := (v / v.gcd s) * x)
      (b := (w / v.gcd s) * y) (m := s / v.gcd s) hd)

theorem reduced_split_coefficients_coprime {s v w : ℕ} (hs : s ≠ 0)
    (hgcd : v.gcd s = w.gcd s) :
    (v / v.gcd s).Coprime (s / v.gcd s) ∧
      (w / v.gcd s).Coprime (s / v.gcd s) := by
  have hv := Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right v (Nat.pos_of_ne_zero hs))
  have hw := Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right w (Nat.pos_of_ne_zero hs))
  exact ⟨hv, hgcd ▸ hw⟩

theorem unit_coefficient_equation_iff {s : ℕ} [NeZero s]
    (v w : ℕ) (x y : (ZMod s)ˣ) :
    (v : ZMod s) * x = (w : ZMod s) * y ↔
      Nat.ModEq s (v * (x : ZMod s).val) (w * (y : ZMod s).val) := by
  simpa only [Nat.cast_mul, ZMod.natCast_zmod_val] using
    ZMod.natCast_eq_natCast_iff (v * (x : ZMod s).val) (w * (y : ZMod s).val) s

theorem unit_coefficient_gcd_eq {s : ℕ} [NeZero s]
    (v w : ℕ) (x y : (ZMod s)ˣ)
    (h : (v : ZMod s) * x = (w : ZMod s) * y) : v.gcd s = w.gcd s :=
  split_relation_gcd_eq (ZMod.val_coe_unit_coprime x) (ZMod.val_coe_unit_coprime y)
    ((unit_coefficient_equation_iff v w x y).mp h)

theorem unit_coefficient_reduce {s : ℕ} [NeZero s]
    (v w : ℕ) (hgcd : v.gcd s = w.gcd s) (x y : (ZMod s)ˣ) :
    (v : ZMod s) * x = (w : ZMod s) * y ↔
      (v / v.gcd s : ZMod (s / v.gcd s)) *
          ZMod.unitsMap (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right v s)) x =
        (w / v.gcd s : ZMod (s / v.gcd s)) *
          ZMod.unitsMap (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right v s)) y := by
  rw [unit_coefficient_equation_iff,
    split_relation_divide_gcd (NeZero.ne s) hgcd]
  have hcast (u : (ZMod s)ˣ) :
      (ZMod.unitsMap (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right v s)) u :
          ZMod (s / v.gcd s)) = ((u : ZMod s).val : ZMod (s / v.gcd s)) := by
    change ZMod.castHom (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right v s)) _ (u : ZMod s) = _
    nth_rw 1 [← ZMod.natCast_zmod_val (u : ZMod s)]
    exact map_natCast _ _
  rw [hcast, hcast]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).symm.trans (by simp only [Nat.cast_mul])

/-- The parent product is already exposed. The child product remains the
uniform variable, and the split relation specifies its square. -/
theorem split_relation_iff_square {G : Type*} [CommGroup G]
    (A B P x : G) : A * (P / x) = B * x ↔ x ^ 2 = A * P / B := by
  constructor
  · intro h
    have hm := congrArg (fun y => y * x / B) h
    calc
      x ^ 2 = B * x * x / B := by rw [mul_assoc, mul_div_cancel_left, pow_two]
      _ = A * (P / x) * x / B := hm.symm
      _ = A * P / B := by rw [mul_assoc A, div_mul_cancel]
  · intro h
    have hm := congrArg (fun y => B * y / x) h
    calc
      A * (P / x) = B * (A * P / B) / x := by
        rw [mul_div_cancel, mul_div_assoc]
      _ = B * x ^ 2 / x := hm.symm
      _ = B * x := by rw [pow_two, ← mul_assoc, mul_div_cancel_right]

noncomputable def splitSquareTarget {s : ℕ} [NeZero s]
    (v w : ℕ) (hgcd : v.gcd s = w.gcd s) (A B P : (ZMod s)ˣ) :
    (ZMod (s / v.gcd s))ˣ :=
  let f := ZMod.unitsMap (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right v s))
  let h := reduced_split_coefficients_coprime (NeZero.ne s) hgcd
  (ZMod.unitOfCoprime (v / v.gcd s) h.1 * f A) * f P /
    (ZMod.unitOfCoprime (w / v.gcd s) h.2 * f B)

theorem unit_split_iff_square {s : ℕ} [NeZero s]
    (v w : ℕ) (hgcd : v.gcd s = w.gcd s) (A B P x : (ZMod s)ˣ) :
    (v : ZMod s) * (A * (P / x) : (ZMod s)ˣ) =
        (w : ZMod s) * (B * x : (ZMod s)ˣ) ↔
      (ZMod.unitsMap (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right v s)) x) ^ 2 =
        splitSquareTarget v w hgcd A B P := by
  let f := ZMod.unitsMap (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right v s))
  let h := reduced_split_coefficients_coprime (NeZero.ne s) hgcd
  have heq := split_relation_iff_square
    (ZMod.unitOfCoprime (v / v.gcd s) h.1 * f A)
    (ZMod.unitOfCoprime (w / v.gcd s) h.2 * f B) (f P) (f x)
  rw [← Units.val_inj] at heq
  apply (unit_coefficient_reduce v w hgcd (A * (P / x)) (B * x)).trans
  simpa only [f, splitSquareTarget, map_mul, map_div, Units.val_mul,
    Units.val_div_eq_div_val, ZMod.coe_unitOfCoprime, mul_assoc] using heq

end Ostmann

end OAI
