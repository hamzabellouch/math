import Mathlib
import OAI.Analysis.CoulombIonization.Localization.QuantumRawLaw

namespace OAI

noncomputable section

namespace CoulombObservation

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ObservationScoreMoments_scope

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal NNReal BigOperators

lemma pow_mul_exp_neg_le (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    t^n * Real.exp (-t) ≤ (n : ℝ)^n := by
  have hf : 0 < (Nat.factorial n : ℝ) := by positivity
  have hh := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp t ht n)
  have hh' := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-t)).le
  have he : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  calc
    _ ≤ (Nat.factorial n : ℝ) := by nlinarith [hh']
    _ ≤ _ := by exact_mod_cast Nat.factorial_le_pow n

lemma compactNoiseScore_weight_bound (u : ℝ) (k : ℕ) :
    compactNoiseScore u ^ (2*k) * compactNoiseWeight u ≤ (32*(k:ℝ)^2)^(2*k) := by
  by_cases hk : k = 0
  · subst k
    simpa using compactNoiseWeight_le_one u
  by_cases hu : |u| < 1
  · have hd : 0 < 1-u^2 := by have := abs_lt.mp hu; nlinarith
    let t : ℝ := (1-u^2)⁻¹
    have ht : 0 ≤ t := inv_nonneg.mpr hd.le
    have hs : |compactNoiseScore u| ≤ 2*t^2 := by
      rw [compactNoiseScore, ite_eq_left hu]
      simp only [abs_div, abs_mul, abs_neg, abs_sq]
      norm_num only [abs_of_nonneg (show (0:ℝ) ≤ 2 by norm_num)]
      dsimp [t]
      rw [inv_pow]
      calc
        _ ≤ 2/(1-u^2)^2 := div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
        _ = _ := by rw [div_eq_mul_inv]
    have hp : compactNoiseScore u^(2*k) ≤ (2*t^2)^(2*k) := by
      have hh := pow_le_pow_left₀ (abs_nonneg _) hs (2*k)
      simpa only [pow_mul, sq_abs] using hh
    have hh := pow_mul_exp_neg_le t ht (4*k)
    calc
      _ = compactNoiseScore u^(2*k) * Real.exp (-t) := by rw [compactNoiseWeight, ite_eq_left hu]
      _ ≤ (2*t^2)^(2*k) * Real.exp (-t) := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = 2^(2*k) * (t^(4*k) * Real.exp (-t)) := by
        rw [mul_pow, ← pow_mul]; ring_nf
      _ ≤ 2^(2*k) * ((4*k : ℕ):ℝ)^(4*k) := mul_le_mul_of_nonneg_left hh (by positivity)
      _ = (2 * (4*(k:ℝ))^2)^(2*k) := by
        simp only [Nat.cast_mul, Nat.cast_ofNat]
        symm
        rw [mul_pow]
        congr 1
        rw [← pow_mul, show 2*(2*k) = 4*k by omega]
      _ = _ := by congr 1; ring
  · simp [compactNoiseScore, compactNoiseWeight, hu]

lemma compactNoiseScore_weight_integrable (k : ℕ) :
    Integrable (fun u => compactNoiseScore u^(2*k) * compactNoiseWeight u) := by
  let B : ℝ := (32*(k:ℝ)^2)^(2*k)
  have hi : Integrable ((Icc (-1:ℝ) 1).indicator (fun _ => B)) := by
    apply (integrable_indicator_iff measurableSet_Icc).2
    exact integrableOn_const (by rw [Real.volume_Icc]; finiteness)
  refine hi.mono' ((compactNoiseScore_measurable.pow_const _).mul
    compactNoiseWeight_measurable).aestronglyMeasurable (ae_of_all _ ?_)
  intro u
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by rw [pow_mul]; positivity) (compactNoiseWeight_nonneg u))]
  by_cases hu : |u| < 1
  · rw [indicator_of_mem (by have := abs_lt.mp hu; constructor <;> linarith)]
    exact compactNoiseScore_weight_bound u k
  · simp only [compactNoiseWeight, ite_eq_right hu, mul_zero]
    exact indicator_nonneg (fun _ _ => by dsimp [B]; positivity) _

lemma compactNoiseScore_moment_integrable (k : ℕ) :
    Integrable (fun u => compactNoiseScore u^(2*k)) compactNoiseLaw := by
  rw [compactNoiseLaw, integrable_withDensity_iff
    compactNoiseDensity_measurable.ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (compactNoiseDensity_nonneg _)]
  simpa only [compactNoiseDensity, mul_left_comm, mul_assoc] using
    (compactNoiseScore_weight_integrable k).const_mul compactNoiseNormalizer

def compactScoreConstant : ℝ := 32 * (1 + 2*compactNoiseNormalizer)

lemma compactScoreConstant_pos : 0 < compactScoreConstant := by
  unfold compactScoreConstant
  have := compactNoiseNormalizer_pos
  positivity

lemma compactNoiseScore_moment_le {k : ℕ} (hk : 0 < k) :
    (∫ u, compactNoiseScore u^(2*k) ∂compactNoiseLaw) ≤
      (compactScoreConstant * (k:ℝ)^2)^(2*k) := by
  let B : ℝ := (32*(k:ℝ)^2)^(2*k)
  have hi : Integrable ((Icc (-1:ℝ) 1).indicator (fun _ => B)) := by
    apply (integrable_indicator_iff measurableSet_Icc).2
    exact integrableOn_const (by rw [Real.volume_Icc]; finiteness)
  have hpoint (u : ℝ) : compactNoiseScore u^(2*k) * compactNoiseWeight u ≤
      (Icc (-1:ℝ) 1).indicator (fun _ => B) u := by
    by_cases hu : |u| < 1
    · rw [indicator_of_mem (by have := abs_lt.mp hu; constructor <;> linarith)]
      exact compactNoiseScore_weight_bound u k
    · simp only [compactNoiseWeight, ite_eq_right hu, mul_zero]
      exact indicator_nonneg (fun _ _ => by dsimp [B]; positivity) _
  have hbound := integral_mono (compactNoiseScore_weight_integrable k) hi hpoint
  rw [integral_indicator measurableSet_Icc, integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc] at hbound
  norm_num at hbound
  have hp : 2*compactNoiseNormalizer ≤ (1+2*compactNoiseNormalizer)^(2*k) := by
    have h1 : 1 ≤ 1+2*compactNoiseNormalizer := by linarith [compactNoiseNormalizer_pos]
    calc
      _ ≤ 1+2*compactNoiseNormalizer := by linarith
      _ ≤ _ := by simpa using pow_le_pow_right₀ h1 (by omega : 1 ≤ 2*k)
  calc
    _ = compactNoiseNormalizer * ∫ u, compactNoiseScore u^(2*k) * compactNoiseWeight u := by
      rw [compactNoiseLaw_integral, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      dsimp [compactNoiseDensity]
      ring
    _ ≤ compactNoiseNormalizer * (2*B) := mul_le_mul_of_nonneg_left hbound compactNoiseNormalizer_pos.le
    _ = (2*compactNoiseNormalizer)*B := by ring
    _ ≤ (1+2*compactNoiseNormalizer)^(2*k)*B := mul_le_mul_of_nonneg_right hp (by dsimp [B]; positivity)
    _ = _ := by dsimp [B, compactScoreConstant]; rw [← mul_pow]; congr 1; ring

end Work_ObservationScoreMoments_scope

open MeasureTheory Set
open scoped ENNReal

lemma compactNoiseLaw_neg_preserving :
    MeasurePreserving Neg.neg compactNoiseLaw compactNoiseLaw := by
  refine ⟨measurable_neg, ?_⟩
  ext s hs
  rw [Measure.map_apply measurable_neg hs, compactNoiseLaw,
    withDensity_apply _ (hs.preimage measurable_neg), withDensity_apply _ hs]
  rw [← lintegral_indicator (hs.preimage measurable_neg), ← lintegral_indicator hs]
  have hh := (Measure.measurePreserving_neg (volume : Measure ℝ)).lintegral_comp
    (compactNoiseDensity_measurable.ennreal_ofReal.indicator hs)
  convert hh using 1
  apply lintegral_congr
  intro u
  by_cases hu : -u ∈ s
  · simp only [indicator_of_mem hu, mem_preimage, hu, indicator_of_mem]
    simp [compactNoiseDensity, compactNoiseWeight_even]
  · simp only [indicator_of_notMem hu, mem_preimage, hu, not_false_eq_true, indicator_of_notMem]

end CoulombObservation

end

end OAI
