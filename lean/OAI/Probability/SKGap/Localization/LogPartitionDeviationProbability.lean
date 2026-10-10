import Mathlib
import OAI.Probability.SKGap.Localization.CoordinateLipschitz

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
namespace SKGapCutoff
open ProbabilityTheory

lemma log_partition_deviation_probability_le (β : ℝ) (hβ : β ^ 2 < 1)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    (disorderLaw β n) {g | ε < |(Real.log (partition (sampledInteraction g)) -
      Real.log (∫ h, partition (sampledInteraction h) ∂disorderLaw β n)) / n|} ≤
      ENNReal.ofReal (((β ^ 2 + 2 * β ^ 2 / (Real.sqrt (1 - β ^ 2) / 4)) * n +
        2 * (Real.log 2)^2) / (ε^2 * n^2)) := by
  let μ := disorderLaw β n
  let : IsProbabilityMeasure μ := by dsimp [μ, disorderLaw]; infer_instance
  let c := Real.log (∫ g, partition (sampledInteraction g) ∂μ)
  let Y := fun g : GaussianCoordinates n => (Real.log (partition (sampledInteraction g)) - c)^2
  have hY : Integrable Y μ := (memLp_log_partition β n |>.sub (memLp_const c)).integrable_sq
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hhR : 0 < ε^2 * (n : ℝ)^2 := mul_pos (sq_pos_of_pos hε) (sq_pos_of_pos hnR)
  have hs := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := Y) (Filter.Eventually.of_forall (fun g => sq_nonneg _)) hY (ε^2*n^2)
  have hgsub : {g | ε < |(Real.log (partition (sampledInteraction g)) - c) / n|} ⊆
      {g | ε^2*(n : ℝ)^2 ≤ Y g} := by
    intro g hg
    change ε < |(Real.log (partition (sampledInteraction g)) - c) / n| at hg
    rw [abs_div, abs_of_pos hnR, lt_div_iff₀ hnR] at hg
    change _ ≤ (Real.log (partition (sampledInteraction g)) - c)^2
    have hsq := sq_le_sq₀ (by positivity : 0 ≤ ε * (n : ℝ)) (abs_nonneg _) |>.mpr (le_of_lt hg)
    simpa only [mul_pow, sq_abs] using hsq
  have hreal := mul_le_mul_of_nonneg_left (measureReal_mono (μ := μ) hgsub) (le_of_lt hhR)
  have hmoment := second_moment_log_partition_centered_le β hβ hn
  have ht := hreal.trans (hs.trans hmoment)
  rw [mul_comm (ε^2*(n : ℝ)^2), ← le_div_iff₀ hhR] at ht
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  exact ENNReal.ofReal_le_ofReal ht

lemma log_partition_annealed_difference_limit (β : ℝ) (hβ : β ^ 2 < 1) :
    DisorderLimit β (fun n J => (Real.log (partition J) -
      Real.log (∫ h, partition (sampledInteraction h) ∂disorderLaw β n)) / n) 0 := by
  intro ε hε
  let A := β^2 + 2 * β^2 / (Real.sqrt (1-β^2)/4)
  let B := 2 * (Real.log 2)^2
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => (A/ε^2) * (n : ℝ)⁻¹ +
      (B/ε^2) * ((n : ℝ)⁻¹)^2) atTop (nhds 0) := by
    simpa using (hi.const_mul (A/ε^2)).add ((hi.pow 2).const_mul (B/ε^2))
  have heq : ∀ᶠ n : ℕ in atTop, (A * n + B)/(ε^2*(n : ℝ)^2) =
      (A/ε^2) * (n : ℝ)⁻¹ + (B/ε^2) * ((n : ℝ)⁻¹)^2 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    field_simp
  have hlim' : Tendsto (fun n : ℕ => ENNReal.ofReal ((A*n+B)/(ε^2*(n : ℝ)^2)))
      atTop (nhds 0) := by
    have hreal := hlim.congr' (heq.mono fun _ h => h.symm)
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim'
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [eventually_ge_atTop 1] with n hn
  simpa only [sub_zero] using log_partition_deviation_probability_le β hβ (by omega) hε

end SKGapCutoff

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

end

end OAI
