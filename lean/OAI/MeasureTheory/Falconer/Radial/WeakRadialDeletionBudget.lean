import OAI.MeasureTheory.Falconer.Recursion.FrostmanProfiles
import OAI.MeasureTheory.Falconer.Radial.WeakRadialParameters

namespace OAI

/-! # Turning the two actual local incidence losses into a pair deletion bound -/

namespace Falconer
open scoped ENNReal

theorem weak_radial_two_costs {A B u v c : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hu : c < u) (hv : c < v) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      A*((2:ℝ)^N)^(-u)+B*((2:ℝ)^N)^(-v) ≤ ((2:ℝ)^N)^(-c) := by
  let m := min (u-c) (v-c)
  have hm : 0 < m := lt_min (sub_pos.mpr hu) (sub_pos.mpr hv)
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hm (A+B)
  refine ⟨N₀,fun N hN => ?_⟩
  let R : ℝ := (2:ℝ)^N
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hu' : -u ≤ -c-m := by have := min_le_left (u-c) (v-c); dsimp [m]; linarith
  have hv' : -v ≤ -c-m := by have := min_le_right (u-c) (v-c); dsimp [m]; linarith
  calc
    _ ≤ A*R^(-c-m)+B*R^(-c-m) := add_le_add
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR hu') hA)
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR hv') hB)
    _ = (A+B)*R^(-c-m) := by ring
    _ ≤ R^m*R^(-c-m) := mul_le_mul_of_nonneg_right (hN₀ N hN) (Real.rpow_nonneg hRp.le _)
    _ = R^(-c) := by rw [← Real.rpow_add hRp]; congr 1; ring

theorem weak_radial_local_deletion_budget (d : ℕ) (hd : 0 < d)
    {u v c C : ℝ} (hC : 0 ≤ C) (hu : c*(d:ℝ) < u) (hv : c*(d:ℝ) < v) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ I : ℝ≥0∞,
      I^d ≤ ENNReal.ofReal (((2:ℝ)^N)^(-u))+
        (d:ℝ≥0∞)*ENNReal.ofReal (C*((2:ℝ)^N)^(-v)) →
      I ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c)) := by
  obtain ⟨N₀,hN₀⟩ := weak_radial_two_costs (A := 1) (B := (d:ℝ)*C)
    (by norm_num) (mul_nonneg (Nat.cast_nonneg _) hC) hu hv
  refine ⟨N₀,fun N hN I hI => ?_⟩
  apply (ENNReal.pow_le_pow_left_iff hd.ne').mp
  have hR : 0 < (2:ℝ)^N := by positivity
  have he : (((2:ℝ)^N)^(-c))^d = ((2:ℝ)^N)^(-(c*(d:ℝ))) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hR.le]
    congr 1
    ring
  rw [← ENNReal.ofReal_pow (Real.rpow_nonneg hR.le _),he]
  apply hI.trans
  have he' : (d:ℝ≥0∞)*ENNReal.ofReal (C*((2:ℝ)^N)^(-v)) =
      ENNReal.ofReal ((d:ℝ)*C*((2:ℝ)^N)^(-v)) := by
    rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    ring
  rw [he',← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by simpa only [one_mul] using hN₀ N hN)

end Falconer

end OAI
