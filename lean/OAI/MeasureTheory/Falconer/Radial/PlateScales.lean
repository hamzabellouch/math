import OAI.MeasureTheory.Falconer.Estimates.EndpointDyadicScale
import OAI.MeasureTheory.Falconer.Radial.PublishedHeavyPlates

namespace OAI

/-! # Dyadic powers and the earlier scale used by the coarse plate filter -/

namespace Falconer
open Filter
open scoped Topology

noncomputable def plateScale (j : ℕ) : ℝ := (2:ℝ)^(-(j:ℝ))

theorem plateScale_eq (j : ℕ) : plateScale j = 1/(2:ℝ)^j := by
  rw [plateScale,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]

theorem plateScale_pos (j : ℕ) : 0 < plateScale j :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem plateScale_le_one (j : ℕ) : plateScale j ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr (Nat.cast_nonneg _))

theorem plateScale_antitone : Antitone plateScale := by
  intro i j hij
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact neg_le_neg (Nat.cast_le.mpr hij)

theorem plateScale_rpow (j : ℕ) (t : ℝ) :
    (plateScale j)^t = ((2:ℝ)^(-t))^j := by
  rw [plateScale,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

theorem plateScale_tendsto : Tendsto plateScale atTop (𝓝[>] (0:ℝ)) := by
  have he : plateScale = (fun j => 1/(2:ℝ)^j) := funext plateScale_eq
  rw [he]
  exact dyadic_inverse_tendsto

theorem plateScale_power_tendsto {t : ℝ} (ht : 0 < t) :
    Tendsto (fun j => (plateScale j)^t) atTop (𝓝 (0:ℝ)) := by
  simp_rw [plateScale_rpow]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one
    (Real.rpow_nonneg (by norm_num) _) (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos ht))

theorem plateScale_div_lower (j : ℕ) :
    (plateScale j)^(1/32:ℝ) ≤ plateScale (j/32) := by
  rw [plateScale,plateScale,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hnat : (j/32)*32 ≤ j := Nat.div_mul_le_self j 32
  have hreal : ((j/32:ℕ):ℝ)*32 ≤ (j:ℝ) := by exact_mod_cast hnat
  linarith only [hreal]

theorem plateScale_div_upper (j : ℕ) :
    plateScale (j/32) ≤ 2*(plateScale j)^(1/32:ℝ) := by
  have hnat : j < (j/32+1)*32 := by omega
  have hreal : (j:ℝ) < (((j/32:ℕ):ℝ)+1)*32 := by exact_mod_cast hnat
  have hexp : -((j/32:ℕ):ℝ) ≤ 1+(-(j:ℝ))*(1/32:ℝ) := by linarith only [hreal]
  calc
    _ ≤ (2:ℝ)^(1+(-(j:ℝ))*(1/32:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = _ := by
      rw [Real.rpow_add (by norm_num),Real.rpow_one,
        Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      rfl

theorem plateScale_div_power (j : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    (plateScale (j/32))^b ≤ (2:ℝ)^b*(plateScale j)^(b/32) := by
  apply (Real.rpow_le_rpow (plateScale_pos _).le (plateScale_div_upper j) hb).trans_eq
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (plateScale_pos _).le _),
    ← Real.rpow_mul (plateScale_pos _).le]
  congr 1
  ring_nf

theorem plate_exponent_gaps {a : ℝ} (ha : 0 < a) :
    0 < heavyPlateExponent a ∧ a/16 < a/8-2*heavyPlateExponent a ∧
      a/16 < a/8-256*heavyPlateExponent a := by
  unfold heavyPlateExponent
  constructor
  · positivity
  · constructor <;> linarith only [ha]

end Falconer

end OAI
