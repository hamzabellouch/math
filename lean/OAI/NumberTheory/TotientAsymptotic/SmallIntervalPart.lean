import OAI.NumberTheory.TotientAsymptotic.PrimeBandProducts

namespace OAI

/-! The interval part in Ford 4.1 is small enough for the quotient sieve. -/
noncomputable section
namespace TotientAsymptotic

lemma partBetween_le_partBelow (n : ℕ) {S F : ℝ} (hSF : S ≤ F) :
    partBetween n S F ≤ partBelow n F := by
  have hp := partBelow_pos n S
  have he := partBelow_band_split n hSF
  nlinarith

lemma interval_part_log_bound (n : ℕ) {S F K : ℝ} (hSF : S ≤ F) (hF : 1 ≤ F)
    (hΩ : (n.primeFactorsList.length:ℝ) ≤ K) :
    Real.log (partBetween n S F) ≤ K*Real.log F := by
  have hp : (0:ℝ) < partBetween n S F := by exact_mod_cast partBetween_pos n S F
  have hb : (partBetween n S F:ℝ) ≤ F^n.primeFactorsList.length :=
    (Nat.cast_le.mpr (partBetween_le_partBelow n hSF)).trans (partBelow_bound n hF)
  have hl := Real.log_le_log hp hb
  rw [Real.log_pow] at hl
  exact hl.trans (mul_le_mul_of_nonneg_right hΩ (Real.log_nonneg hF))

lemma interval_part_sieve_size {n S X z : ℕ} {K : ℝ}
    (hS : S ≤ z) (hz : 1 ≤ z) (hX : 0 < X)
    (hΩ : (n.primeFactorsList.length:ℝ) ≤ K)
    (hsize : (K+1)*Real.log z ≤ Real.log X) :
    z*partBetween n S z ≤ X := by
  have hz0 : (0:ℝ) < z := by exact_mod_cast (show 0 < z by omega)
  have hp0 : (0:ℝ) < partBetween n S z := by exact_mod_cast partBetween_pos n S z
  have hX0 : (0:ℝ) < X := by exact_mod_cast hX
  have hl := interval_part_log_bound n (S:=(S:ℝ)) (F:=(z:ℝ))
    (by exact_mod_cast hS) (by exact_mod_cast hz) hΩ
  have hprod : Real.log ((z:ℝ)*(partBetween n S z:ℝ)) ≤ Real.log X := by
    rw [Real.log_mul hz0.ne' hp0.ne']
    nlinarith only [hl,hsize]
  have hh := (Real.log_le_log_iff (mul_pos hz0 hp0) hX0).mp hprod
  exact_mod_cast hh

lemma ford_interval_part_sieve_size {n S X z : ℕ}
    (hS : S ≤ z) (hz : 1 ≤ z) (hBX : 1 ≤ B X)
    (hΩ : (n.primeFactorsList.length:ℝ) ≤ 5*B X)
    (hcut : Real.log z ≤ Real.log X/(20*B X)) (hX : 0 < X) :
    z*partBetween n S z ≤ X := by
  apply interval_part_sieve_size hS hz hX hΩ
  have hB : 0 < 20*B X := by positivity
  have hh := (le_div_iff₀ hB).mp hcut
  have hzlog : 0 ≤ Real.log z := Real.log_nonneg (by exact_mod_cast hz)
  have hc : 5*B X+1 ≤ 20*B X := by linarith only [hBX]
  have hm := mul_le_mul_of_nonneg_right hc hzlog
  nlinarith only [hh,hm]

end TotientAsymptotic

end

end OAI
