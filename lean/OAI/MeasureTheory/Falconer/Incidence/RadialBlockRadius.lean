import OAI.MeasureTheory.Falconer.Radial.RadialFreezingScales
import OAI.MeasureTheory.Falconer.Recursion.FrostmanProfiles

namespace OAI

/-! # The actual near-pin radius decays at a fixed reciprocal-scale power -/

namespace Falconer

theorem radial_block_radius_bound {A : ℝ} (hA : 0 ≤ A) (d N J : ℕ) :
    8*(d:ℝ)*A/(2:ℝ)^(radialBlockSize N J) ≤
      16*(d:ℝ)*A*((2:ℝ)^N)^(-1/((J:ℝ)+2)) := by
  have hJ : (0:ℝ) < (J:ℝ)+2 := by positivity
  have hh := Nat.lt_mul_div_succ N (by omega : 0 < J+2)
  have hb : (N:ℝ) < ((J:ℝ)+2)*((radialBlockSize N J:ℝ)+1) := by exact_mod_cast hh
  have hb' : -(radialBlockSize N J:ℝ) ≤ 1-(N:ℝ)/((J:ℝ)+2) := by
    have ht : (N:ℝ)/((J:ℝ)+2) < (radialBlockSize N J:ℝ)+1 :=
      (div_lt_iff₀ hJ).mpr (by simpa only [mul_comm] using hb)
    linarith
  have he : ((2:ℝ)^N)^(-1/((J:ℝ)+2)) = (2:ℝ)^(-(N:ℝ)/((J:ℝ)+2)) := by
    rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  have hp : ((2:ℝ)^(radialBlockSize N J))⁻¹ ≤
      2*((2:ℝ)^N)^(-1/((J:ℝ)+2)) := by
    rw [← Real.rpow_natCast,← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    calc
      _ ≤ (2:ℝ)^(1-(N:ℝ)/((J:ℝ)+2)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hb'
      _ = _ := by
        rw [he,Real.rpow_sub (by norm_num),Real.rpow_one]
        rw [show -(N:ℝ)/((J:ℝ)+2) = -((N:ℝ)/((J:ℝ)+2)) by ring,
          Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
        rfl
  calc
    _ = (8*(d:ℝ)*A)*((2:ℝ)^(radialBlockSize N J))⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ (8*(d:ℝ)*A)*(2*((2:ℝ)^N)^(-1/((J:ℝ)+2))) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

theorem eventually_radial_block_radius_le_one {A : ℝ} (hA : 0 ≤ A) (d J : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 8*(d:ℝ)*A/(2:ℝ)^(radialBlockSize N J) ≤ 1 := by
  have hpow : 0 < (1:ℝ)/((J:ℝ)+2) := by positivity
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hpow (16*(d:ℝ)*A)
  refine ⟨N₀,fun N hN => (radial_block_radius_bound hA d N J).trans ?_⟩
  calc
    _ ≤ (((2:ℝ)^N)^(1/((J:ℝ)+2)))*(((2:ℝ)^N)^(-1/((J:ℝ)+2))) :=
      mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity)
    _ = 1 := by
      rw [← Real.rpow_add (by positivity),show
        (1/((J:ℝ)+2))+(-1/((J:ℝ)+2)) = 0 by ring,Real.rpow_zero]

end Falconer

end OAI
