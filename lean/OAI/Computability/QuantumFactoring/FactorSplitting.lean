import Mathlib

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

/-- Strictly smaller 2-adic level makes a divisor divide the half-order. -/
theorem dvd_half_of_level_lt {d r : ℕ} (hr : r ≠ 0) (hdr : d ∣ r)
    (hlevel : padicValNat 2 d < padicValNat 2 r) : d ∣ r / 2 := by
  rcases hdr with ⟨k, rfl⟩
  have hd : d ≠ 0 := left_ne_zero_of_mul hr
  have hk : k ≠ 0 := right_ne_zero_of_mul hr
  rw [padicValNat.mul hd hk] at hlevel
  have htwo : 2 ∣ k := dvd_of_one_le_padicValNat (by omega : 1 ≤ padicValNat 2 k)
  rcases htwo with ⟨t, rfl⟩
  use t
  rw [show d * (2 * t) = (d * t) * 2 by ring, Nat.mul_div_cancel _ (by decide)]

/-- Divisibility cannot increase the 2-adic valuation. -/
theorem level_le_of_dvd {d r : ℕ} (hr : r ≠ 0) (hdr : d ∣ r) :
    padicValNat 2 d ≤ padicValNat 2 r := by
  rcases hdr with ⟨k, rfl⟩
  rw [padicValNat.mul (left_ne_zero_of_mul hr) (right_ne_zero_of_mul hr)]
  omega

/-- The actual representative used by bounded modular gcd arithmetic. -/
noncomputable def halfOrderResidue {m : ℕ} (a : (ZMod m)ˣ) : ℕ :=
  ((a ^ (orderOf a / 2) : (ZMod m)ˣ) : ZMod m).val

noncomputable def splitGcd {m : ℕ} (a : (ZMod m)ˣ) : ℕ :=
  Nat.gcd (halfOrderResidue a + m - 1) m

/-- A single lower-level component suffices for a proper nontrivial split.
The largest-level component is not assumed to have a chosen generator. -/
theorem splitGcd_proper_of_lower_component {m d : ℕ} (hm : 2 ≤ m) (hd : 2 ≤ d)
    (hdm : d ∣ m) (a : (ZMod m)ˣ)
    (hlevel : padicValNat 2 (orderOf (Units.map (ZMod.castHom hdm (ZMod d)).toMonoidHom a))
      < padicValNat 2 (orderOf a)) :
    1 < splitGcd a ∧ splitGcd a < m ∧ splitGcd a ∣ m := by
  let : NeZero m := ⟨by omega⟩
  let : NeZero d := ⟨by omega⟩
  let f : (ZMod m)ˣ →* (ZMod d)ˣ := Units.map (ZMod.castHom hdm (ZMod d)).toMonoidHom
  have hr : 0 < orderOf a := orderOf_pos a
  have hhalf : orderOf (f a) ∣ orderOf a / 2 :=
    dvd_half_of_level_lt hr.ne' (orderOf_map_dvd f a) hlevel
  have hreduce : f a ^ (orderOf a / 2) = 1 := orderOf_dvd_iff_pow_eq_one.mp hhalf
  have htwo : 2 ∣ orderOf a := dvd_of_one_le_padicValNat (by omega)
  have hhalfnz : orderOf a / 2 ≠ 0 := by
    have : 2 ≤ orderOf a := Nat.le_of_dvd hr htwo
    omega
  have hglobal : a ^ (orderOf a / 2) ≠ 1 :=
    pow_ne_one_of_lt_orderOf hhalfnz (Nat.div_lt_self hr (by decide))
  have hle : 1 ≤ halfOrderResidue a + m := by omega
  have hcastm : ((halfOrderResidue a + m - 1 : ℕ) : ZMod m) =
      ((a ^ (orderOf a / 2) : (ZMod m)ˣ) : ZMod m) - 1 := by
    rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, add_zero]
    exact congrArg (fun x : ZMod m => x - 1) (ZMod.natCast_zmod_val _)
  have hcastd : ((halfOrderResidue a + m - 1 : ℕ) : ZMod d) = 0 := by
    have heq : (ZMod.castHom hdm (ZMod d))
        ((a ^ (orderOf a / 2) : (ZMod m)ˣ) : ZMod m) = 1 := by
      have hv := congrArg (fun x : (ZMod d)ˣ => (x : ZMod d)) hreduce
      change (((f a) ^ (orderOf a / 2) : (ZMod d)ˣ) : ZMod d) = 1 at hv
      rw [← map_pow] at hv
      exact hv
    have hz : (m : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff m d).mpr hdm
    rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_one, hz, add_zero]
    rw [ZMod.castHom_apply, ZMod.cast_eq_val] at heq
    exact sub_eq_zero.mpr heq
  have hdiv : d ∣ halfOrderResidue a + m - 1 :=
    (ZMod.natCast_eq_zero_iff _ _).mp hcastd
  have hnond : ¬ m ∣ halfOrderResidue a + m - 1 := by
    intro h
    have hz := (ZMod.natCast_eq_zero_iff _ m).mpr h
    rw [hcastm] at hz
    exact hglobal (Units.ext (sub_eq_zero.mp hz))
  have hgpos : 0 < splitGcd a := Nat.gcd_pos_of_pos_right _ (by omega)
  have hglower : d ≤ splitGcd a := Nat.le_of_dvd hgpos (Nat.dvd_gcd hdiv hdm)
  have hgupper : splitGcd a ≤ m := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)
  have hgneq : splitGcd a ≠ m := by
    intro h
    exact hnond (Nat.gcd_eq_right_iff_dvd.mp h)
  exact ⟨by omega, by omega, Nat.gcd_dvd_right _ _⟩

/-- Two unequal local levels guarantee that one of them is below the global
level, so the verified order always supplies a nontrivial gcd. -/
theorem splitGcd_proper_of_unequal_components {m d e : ℕ} (hm : 2 ≤ m)
    (hd : 2 ≤ d) (he : 2 ≤ e) (hdm : d ∣ m) (hem : e ∣ m) (a : (ZMod m)ˣ)
    (hne : padicValNat 2 (orderOf (Units.map (ZMod.castHom hdm (ZMod d)).toMonoidHom a)) ≠
      padicValNat 2 (orderOf (Units.map (ZMod.castHom hem (ZMod e)).toMonoidHom a))) :
    1 < splitGcd a ∧ splitGcd a < m ∧ splitGcd a ∣ m := by
  let : NeZero m := ⟨by omega⟩
  have hr : orderOf a ≠ 0 := (orderOf_pos a).ne'
  have hdle := level_le_of_dvd hr
    (orderOf_map_dvd (Units.map (ZMod.castHom hdm (ZMod d)).toMonoidHom) a)
  have hele := level_le_of_dvd hr
    (orderOf_map_dvd (Units.map (ZMod.castHom hem (ZMod e)).toMonoidHom) a)
  rcases lt_or_gt_of_ne hne with h | h
  · exact splitGcd_proper_of_lower_component hm hd hdm a (h.trans_le hele)
  · exact splitGcd_proper_of_lower_component hm he hem a (h.trans_le hdle)

end ExactQuantumFactoring


end

end OAI
