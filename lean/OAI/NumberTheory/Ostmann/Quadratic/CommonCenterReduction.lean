import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import OAI.NumberTheory.Ostmann.Quadratic.CommonCenterCongruences

namespace OAI

/-! # Reducing the common rational center and transporting its congruences -/

namespace Ostmann

theorem exists_reduced_commonCenter (n : ℤ) (a : ℕ) (ha : 0 < a) :
    ∃ h : ℤ, ∃ m : ℕ, 0 < m ∧ m ≤ a ∧ h.natAbs.Coprime m ∧
      |h| ≤ |n| ∧ n * (m : ℤ) = (a : ℤ) * h := by
  let q : ℚ := Rat.divInt n a
  have ha0 : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  obtain ⟨c, hn, hac⟩ := Rat.num_den_mk ha0 (show q = Rat.divInt n a from rfl)
  refine ⟨q.num, q.den, q.pos, ?_, q.reduced, ?_, ?_⟩
  · exact Nat.le_of_dvd ha (Int.natCast_dvd_natCast.mp (Rat.den_dvd n a))
  · have hm : (0 : ℤ) < q.den := by exact_mod_cast q.pos
    have hc : 0 < c := by nlinarith
    have hc1 : (1 : ℤ) ≤ c := hc
    rw [hn, abs_mul, abs_of_pos hc]
    nlinarith [abs_nonneg q.num]
  · rw [hn, hac]
    ring

/-- The common lift gives the same field center after reducing the rational number. -/
theorem reduced_commonCenter_mod_prime (n h : ℤ) (a m p : ℕ)
    [Fact p.Prime] (ha : 0 < a) (hap : a < p) (hm : 0 < m) (hma : m ≤ a)
    (heq : n * (m : ℤ) = (a : ℤ) * h) (t : ℤ)
    (hcong : (p : ℤ) ∣ n - (a : ℤ) * t) :
    (t : ZMod p) = (h : ZMod p) / (m : ZMod p) := by
  have ha0 : (a : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt ha hap
  have hm0 : (m : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hm (hma.trans_lt hap)
  have hn : (n : ZMod p) = (a : ZMod p) * (t : ZMod p) := by
    have hz : ((n - (a : ℤ) * t : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hcong
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, sub_eq_zero] using hz
  have hcross : (n : ZMod p) * (m : ZMod p) = (a : ZMod p) * (h : ZMod p) := by
    simpa only [Int.cast_mul, Int.cast_natCast] using congrArg (fun x : ℤ => (x : ZMod p)) heq
  rw [hn, mul_assoc] at hcross
  exact (eq_div_iff hm0).mpr (mul_left_cancel₀ ha0 hcross)

end Ostmann

end OAI
