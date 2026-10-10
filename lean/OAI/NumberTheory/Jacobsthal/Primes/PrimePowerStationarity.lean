import OAI.NumberTheory.Jacobsthal.Harmonic.StationaryPhase

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosKloosterman.PrimePower

theorem stationary_iff_quadratic {R : Type*} [CommRing R] (q a b : R) (u : Rˣ) :
    q * (a - b * (↑u⁻¹ : R)^2) = 0 ↔ q * (a * (u : R)^2 - b) = 0 := by
  have he : q * (a - b * (↑u⁻¹ : R)^2) * (u : R)^2 =
      q * (a * (u : R)^2 - b) := by
    calc
      _ = q * a * (u : R)^2 - q * b * ((↑u⁻¹ : R) * u)^2 := by ring
      _ = _ := by simp; ring
  rw [← he]
  change _ ↔ _ * ((u^2 : Rˣ) : R) = 0
  exact (Units.mul_left_eq_zero (u^2)).symm

theorem mul_annihilator_iff (n d : ℕ) [NeZero (n*d)] (hn : 0 < n) (x : ZMod (n*d)) :
    (n : ZMod (n*d)) * x = 0 ↔ (x.val : ZMod d) = 0 := by
  nth_rw 1 [← x.natCast_zmod_val]
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff, ZMod.natCast_eq_zero_iff]
  exact Nat.mul_dvd_mul_iff_left hn

theorem power_shift_square_zero (p r s : ℕ) (hsr : s ≤ r) :
    ((p^r : ℕ) : ZMod (p^(r+s)))^2 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff, ← pow_mul]
  exact pow_dvd_pow p (by omega)

theorem standard_stationary_identity (p r s : ℕ) [NeZero (p^(r+s))] (hsr : s ≤ r)
    (h k : ℤ) :
    standardSum (p^(r+s)) h k =
      ∑ u ∈ stationaryUnits ((p^r : ℕ) : ZMod (p^(r+s))) (h : ZMod (p^(r+s))) k,
        ZMod.stdAddChar ((h : ZMod (p^(r+s))) * (u : ZMod (p^(r+s))) +
          (k : ZMod (p^(r+s))) * (↑u⁻¹ : ZMod (p^(r+s)))) := by
  exact stationary_phase_identity (R := ZMod (p^(r+s)))
    (ZMod.stdAddChar (N := p^(r+s))) (ZMod.isPrimitive_stdAddChar (p^(r+s)))
    (h : ZMod (p^(r+s))) (k : ZMod (p^(r+s))) ((p^r : ℕ) : ZMod (p^(r+s))) (power_shift_square_zero p r s hsr)

theorem standard_norm_le_stationary_card (p r s : ℕ) [NeZero (p^(r+s))] (hsr : s ≤ r)
    (h k : ℤ) :
    ‖standardSum (p^(r+s)) h k‖ ≤
      (stationaryUnits ((p^r : ℕ) : ZMod (p^(r+s))) (h : ZMod (p^(r+s))) k).card := by
  exact norm_sum_le_stationary_card (R := ZMod (p^(r+s)))
    (ZMod.stdAddChar (N := p^(r+s))) (ZMod.isPrimitive_stdAddChar (p^(r+s)))
    (h : ZMod (p^(r+s))) (k : ZMod (p^(r+s))) ((p^r : ℕ) : ZMod (p^(r+s))) (power_shift_square_zero p r s hsr)

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
