import Mathlib

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

private theorem lcm_div_first {d e : ℕ} (hd : 0 < d) :
    Nat.lcm d e / d = e / Nat.gcd d e := by
  rw [Nat.lcm_eq_mul_div, Nat.mul_div_assoc d (Nat.gcd_dvd_right d e),
    Nat.mul_div_cancel_left _ hd]

private theorem lcm_div_second {d e : ℕ} (he : 0 < e) :
    Nat.lcm d e / e = d / Nat.gcd d e := by
  rw [Nat.lcm_comm, lcm_div_first he, Nat.gcd_comm]

theorem local_frequency_fiber_card_le_gcd {d e : ℕ} [NeZero d] [NeZero e]
    (h : ZMod (Nat.lcm d e)) :
    ((Finset.univ : Finset (ZMod d × ZMod e)).filter (fun z =>
      ((Nat.lcm d e / d : ℕ) : ZMod (Nat.lcm d e)) * (z.1.val : ZMod (Nat.lcm d e)) -
      ((Nat.lcm d e / e : ℕ) : ZMod (Nat.lcm d e)) * (z.2.val : ZMod (Nat.lcm d e)) = h)).card ≤
      Nat.gcd d e := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have he : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
  let q := Nat.lcm d e
  let g := Nat.gcd d e
  let A := q / d
  let B := q / e
  have hg : 0 < g := Nat.gcd_pos_of_pos_left e hd
  have hB : B = d / g := lcm_div_second he
  have hA : A = e / g := lcm_div_first hd
  have hBd : g * B = d := by rw [hB]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_left d e)
  have hBe : B * e = q := Nat.div_mul_cancel (Nat.dvd_lcm_right d e)
  have hBpos : 0 < B := by nlinarith
  have hBq : B ∣ q := ⟨e, hBe.symm⟩
  have hcop : B.Coprime A := by
    rw [hB, hA]
    exact Nat.coprime_div_gcd_div_gcd hg
  let R := (Finset.univ : Finset (ZMod d × ZMod e)).filter (fun z =>
    (A : ZMod q) * (z.1.val : ZMod q) - (B : ZMod q) * (z.2.val : ZMod q) = h)
  change R.card ≤ g
  have hc := Finset.card_le_card_of_injOn (s := R) (t := Finset.range g)
    (fun z : ZMod d × ZMod e => z.1.val / B) ?_ ?_
  · simpa only [Finset.card_range] using hc
  · intro z hz
    apply Finset.mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul hBpos).mpr
    simpa only [hBd] using z.1.val_lt
  · intro x hx y hy hquot
    change x.1.val / B = y.1.val / B at hquot
    have hxf := (Finset.mem_filter.mp hx).2
    have hyf := (Finset.mem_filter.mp hy).2
    have hxy : (A : ZMod q) * (x.1.val : ZMod q) - (B : ZMod q) * (x.2.val : ZMod q) =
        (A : ZMod q) * (y.1.val : ZMod q) - (B : ZMod q) * (y.2.val : ZMod q) :=
      hxf.trans hyf.symm
    have hmB : (A : ZMod B) * (x.1.val : ZMod B) =
        (A : ZMod B) * (y.1.val : ZMod B) := by
      simpa only [map_sub, map_mul, map_natCast, ZMod.natCast_self, zero_mul, sub_zero] using
        congrArg (ZMod.castHom hBq (ZMod B)) hxy
    have hxmod : Nat.ModEq B x.1.val y.1.val := by
      apply Nat.ModEq.cancel_left_of_coprime hcop
      exact (ZMod.natCast_eq_natCast_iff (A * x.1.val) (A * y.1.val) B).mp
        (by simpa only [Nat.cast_mul] using hmB)
    have hxval : x.1.val = y.1.val := by
      have hxx := Nat.mod_add_div x.1.val B
      have hyy := Nat.mod_add_div y.1.val B
      change x.1.val % B = y.1.val % B at hxmod
      rw [hxmod, hquot] at hxx
      exact hxx.symm.trans hyy
    have hx1 : x.1 = y.1 := ZMod.val_injective d hxval
    have hyq : (B : ZMod q) * (x.2.val : ZMod q) =
        (B : ZMod q) * (y.2.val : ZMod q) := by
      rw [hx1] at hxy
      linear_combination -hxy
    have hymod : Nat.ModEq e x.2.val y.2.val := by
      apply Nat.ModEq.mul_left_cancel' hBpos.ne'
      rw [hBe]
      exact (ZMod.natCast_eq_natCast_iff (B * x.2.val) (B * y.2.val) q).mp
        (by simpa only [Nat.cast_mul] using hyq)
    have hyval : x.2.val = y.2.val := by
      change x.2.val % e = y.2.val % e at hymod
      simpa only [Nat.mod_eq_of_lt x.2.val_lt, Nat.mod_eq_of_lt y.2.val_lt] using hymod
    exact Prod.ext hx1 (ZMod.val_injective e hyval)

end Ostmann.QuadraticCenter

end OAI
