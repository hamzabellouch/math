import OAI.Probability.RadialTransition.PackingBlob

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma core_nonpos_outer {t : ℝ} (ht : 1 ≤ t) :
    ∀ r : ℝ≥0, 2 ≤ (r:ℝ) → corePotential t r ≤ 0 := by
  intro r hr
  have ht0 : 0 < t := by linarith
  have hinv : 1/t ≤ 1 := (div_le_one ht0).mpr ht
  rw [corePotential, coreReal_zero_outer ht0 (by linarith)]

lemma core_finitePressure_upper {t α L β h : ℝ} (hL : 1 ≤ L)
    (ht0 : 0 < t) (ht : 2*((1+(1:ℝ)/1000)*microLength t) < 1)
    (hβ : 0 ≤ β) (hα : 0 ≤ α) (h1 : h ≤ α) (h4 : 4*h-9 ≤ α) :
    finiteGrandPressure (corePotential t) t L β h ≤
      α*((packingNumber L:ℝ)/L^3)+(216*Real.log 15001+Real.exp (t*h-β*t^2/2))/t := by
  have hL0 : 0 < L := by linarith
  have hh := core_grand_upper hL0.le ht0.le ht hβ (mul_nonneg ht0.le hα) h1 h4
  have hp := (grandPartition_bounds (continuous_corePotential t) (bounded_corePotential t)
    (stable_corePotential t) hL0.le hβ t h).1
  have hreal := ENNReal.toReal_mono (by finiteness :
      ENNReal.ofReal (Real.exp (t*α*packingNumber L)) *
        ((15001:ℝ≥0∞)^(cubeCells L).card * ENNReal.ofReal (Real.exp (L^3*Real.exp (t*h-β*t^2/2)))) ≠ ⊤) hh
  simp only [ENNReal.toReal_ofReal (show 0 ≤ grandPartition (corePotential t) t L β h by linarith),
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    ENNReal.toReal_ofNat] at hreal
  have hlog := Real.log_le_log (show 0 < grandPartition (corePotential t) t L β h by linarith) hreal
  rw [Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp,
    Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp] at hlog
  have hc := mul_le_mul_of_nonneg_right (card_cubeCells hL) (show 0 ≤ Real.log (15001:ℝ) from Real.log_nonneg (by norm_num))
  have hden : 0 < t*L^3 := by positivity
  dsimp only [finiteGrandPressure]
  apply (div_le_iff₀ hden).mpr
  have heq : (α*((packingNumber L:ℝ)/L^3)+(216*Real.log 15001+Real.exp (t*h-β*t^2/2))/t)*(t*L^3) =
      t*α*packingNumber L+216*L^3*Real.log 15001+L^3*Real.exp (t*h-β*t^2/2) := by
    field_simp
    ring
  rw [heq]
  linarith

lemma corePressure_upper {t α β h : ℝ} (ht0 : 1 ≤ t)
    (ht : 2*((1+(1:ℝ)/1000)*microLength t) < 1)
    (hβ : 0 ≤ β) (hα : 0 ≤ α) (h1 : h ≤ α) (h4 : 4*h-9 ≤ α) :
    grandPressure (corePotential t) t β h ≤
      α*packingDensity+(216*Real.log 15001+Real.exp (t*h-β*t^2/2))/t := by
  have htpos : 0 < t := by linarith
  have hl := (grandPressure_spec (continuous_corePotential t) (bounded_corePotential t)
    (stable_corePotential t) htpos hβ (core_nonpos_outer ht0) h).1
  have hr := packingDensity_limit.const_mul α |>.add_const ((216*Real.log 15001+Real.exp (t*h-β*t^2/2))/t)
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [eventually_ge_atTop (1:ℝ)] with L hL
  exact core_finitePressure_upper hL htpos ht hβ hα h1 h4

end RadialTransition
end

end OAI
