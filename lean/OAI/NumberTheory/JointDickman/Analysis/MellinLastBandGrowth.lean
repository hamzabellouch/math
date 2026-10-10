import OAI.NumberTheory.JointDickman.Analysis.MellinBandSelection

namespace OAI

/-! # The final selected band lies beyond every fixed logarithmic power -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Topology

lemma next_band_log_le_lower_sq {P Q : ℝ} (hP : 1 ≤ Real.log P)
    (hQ : 1 ≤ Real.log Q) {j : ℕ} (hj : 8 ≤ j) :
    Real.log (mrtBandUpper Q (j+1)) ≤ (Real.log (mrtBandLower P Q j))^2 := by
  have hj4 : (4:ℝ) ≤ j := by exact_mod_cast (show 4 ≤ j by omega)
  have hj0 : 0 ≤ (j:ℝ) := Nat.cast_nonneg j
  have hstep : ((j+1:ℕ):ℝ) ≤ 2*(j:ℝ) := by push_cast; linarith
  have htwo : (2:ℝ)^(4*j+6) ≤ (j:ℝ)^(4*j-6) := by
    calc
      _ ≤ (2:ℝ)^(2*(4*j-6)) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = (4:ℝ)^(4*j-6) := by rw [pow_mul]; norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hj4 _
  have hp : ((j+1:ℕ):ℝ)^(4*(j+1)+2) ≤ (j:ℝ)^(8*j) := by
    calc
      _ = ((j+1:ℕ):ℝ)^(4*j+6) := by congr 1
      _ ≤ (2*(j:ℝ))^(4*j+6) := pow_le_pow_left₀ (by positivity) hstep _
      _ = (2:ℝ)^(4*j+6)*(j:ℝ)^(4*j+6) := mul_pow _ _ _
      _ ≤ (j:ℝ)^(4*j-6)*(j:ℝ)^(4*j+6) :=
        mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = (j:ℝ)^(8*j) := by rw [← pow_add]; congr 1; omega
  have hqpow : (Real.log Q)^(j+1) ≤ (Real.log Q)^(2*(j-1)) :=
    pow_le_pow_right₀ hQ (by omega)
  have hpp : 1 ≤ (Real.log P)^2 := one_le_pow₀ hP
  simp only [mrtBandUpper,mrtBandLower,Real.log_exp]
  rw [mul_pow,mul_pow,← pow_mul,← pow_mul]
  have hprod := mul_le_mul hp hqpow (by positivity) (by positivity)
  have he1 : 4*j*2=8*j := by omega
  rw [he1]
  simpa only [Nat.mul_comm] using hprod.trans
    (le_mul_of_one_le_right
      (show 0 ≤ (j:ℝ)^(8*j)*(Real.log Q)^(2*(j-1)) by positivity) hpp)

/-- Maximality below `exp(sqrt(log X))` and the explicit adjacent-band
formula force the lower endpoint to grow faster than `exp(log X^(1/4))`. -/
theorem last_selected_band_lower (P Q : ℝ) (hP : 1 ≤ Real.log P)
    (hQ : 1 ≤ Real.log Q) :
    ∀ᶠ X : ℝ in atTop, let J := mellinBandCount Q (Real.sqrt (Real.log X)) hQ
      8 ≤ J ∧ (Real.log X)^(1/4:ℝ) ≤ Real.log (mrtBandLower P Q J) := by
  have hJ := (mellinBandCount_tendsto Q hQ).comp
    (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  filter_upwards [hJ.eventually (eventually_ge_atTop 8),eventually_ge_atTop 1]
    with X hXJ hX
  dsimp only
  let J := mellinBandCount Q (Real.sqrt (Real.log X)) hQ
  refine ⟨hXJ,?_⟩
  have hl := (mellinBandCount_next Q (Real.sqrt (Real.log X)) hQ).le.trans
    (next_band_log_le_lower_sq hP hQ hXJ)
  have hL : 0 ≤ Real.log (mrtBandLower P Q J) := by
    simp only [mrtBandLower,Real.log_exp]
    positivity
  have hs : Real.sqrt (Real.sqrt (Real.log X)) ≤ Real.log (mrtBandLower P Q J) :=
    (Real.sqrt_le_iff).mpr ⟨hL,hl⟩
  have he : Real.sqrt (Real.sqrt (Real.log X)) = (Real.log X)^(1/4:ℝ) := by
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul (Real.log_nonneg hX)]
    norm_num
  rwa [he] at hs

end JointDickman

end OAI
