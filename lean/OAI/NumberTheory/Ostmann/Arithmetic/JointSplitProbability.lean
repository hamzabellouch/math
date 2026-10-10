import OAI.NumberTheory.Ostmann.Arithmetic.SplitSquareSupport

namespace OAI

/-! # The joint support bound for two genuine arithmetic history splits -/

namespace Ostmann

open scoped BigOperators Classical

theorem reduced_modulus_pos {s v : ℕ} (hs : s ≠ 0) : 0 < s / v.gcd s :=
  Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hs) (Nat.gcd_dvd_right v s))
    (Nat.gcd_pos_of_pos_right v (Nat.pos_of_ne_zero hs))

/-- The two histories share the random child product but may have different
parent products, pivots, and frequencies. No complete-history validity event
has been conditioned on in this average. -/
theorem joint_split_probability_le {s t Q : ℕ} [NeZero s] [NeZero t] [NeZero Q]
    (hs : s ∣ Q) (ht : t ∣ Q) (v w v' w' : ℕ)
    (hgcd : v.gcd s = w.gcd s) (hgcd' : v'.gcd t = w'.gcd t)
    (A B P : (ZMod s)ˣ) (A' B' P' : (ZMod t)ˣ) :
    (Fintype.card (ZMod Q)ˣ : ℝ)⁻¹ * (∑ x : (ZMod Q)ˣ,
      if (v : ZMod s) * (A * (P / ZMod.unitsMap hs x) : (ZMod s)ˣ) =
          (w : ZMod s) * (B * ZMod.unitsMap hs x : (ZMod s)ˣ) ∧
        (v' : ZMod t) * (A' * (P' / ZMod.unitsMap ht x) : (ZMod t)ˣ) =
          (w' : ZMod t) * (B' * ZMod.unitsMap ht x : (ZMod t)ˣ)
      then (1 : ℝ) else 0) ≤
      2 * (((s / v.gcd s).lcm (t / v'.gcd t)).divisors.card : ℝ) ^ 2 /
        (s / v.gcd s).lcm (t / v'.gcd t) := by
  let a := s / v.gcd s
  let b := t / v'.gcd t
  let _ : NeZero a := ⟨Nat.ne_of_gt (reduced_modulus_pos (v := v) (NeZero.ne s))⟩
  let _ : NeZero b := ⟨Nat.ne_of_gt (reduced_modulus_pos (v := v') (NeZero.ne t))⟩
  have ha : a ∣ s := Nat.div_dvd_of_dvd (Nat.gcd_dvd_right v s)
  have hb : b ∣ t := Nat.div_dvd_of_dvd (Nat.gcd_dvd_right v' t)
  have hleft (x : (ZMod Q)ˣ) :
      ZMod.unitsMap ha (ZMod.unitsMap hs x) = ZMod.unitsMap (ha.trans hs) x :=
    DFunLike.congr_fun (ZMod.unitsMap_comp ha hs) x
  have hright (x : (ZMod Q)ˣ) :
      ZMod.unitsMap hb (ZMod.unitsMap ht x) = ZMod.unitsMap (hb.trans ht) x :=
    DFunLike.congr_fun (ZMod.unitsMap_comp hb ht) x
  simp_rw [unit_split_iff_square v w hgcd, unit_split_iff_square v' w' hgcd',
    hleft, hright]
  exact reduced_simultaneous_square_probability_le (ha.trans hs) (hb.trans ht)
    (splitSquareTarget v w hgcd A B P) (splitSquareTarget v' w' hgcd' A' B' P')

end Ostmann

end OAI
