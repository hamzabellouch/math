import OAI.Combinatorics.BalancedRyser.Probability.BernoulliTail
import OAI.Combinatorics.BalancedRyser.Probability.LogTail

namespace OAI

open Filter Topology

namespace Balanced.BernoulliTail

lemma tendsto_polynomial_mul_ratio_tail (B : ℕ → ℕ)
    (hB : Tendsto (fun q => (B q : ℝ)) atTop atTop)
    (hlog : ∀ᶠ q : ℕ in atTop, Real.log (q : ℝ) ≤ (B q : ℝ))
    (r : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun q : ℕ => (q : ℝ) ^ r * (C / (B q : ℝ)) ^ B q)
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun q => by positivity)
  · filter_upwards [eventually_gt_atTop (0 : ℕ), hlog,
      hB.eventually (eventually_gt_atTop 0),
      hB.eventually (eventually_ge_atTop (C * Real.exp ((r : ℝ) + 1)))]
      with q hq hl hpos hlarge
    have hBn : 0 < B q := by exact_mod_cast hpos
    exact BalancedRyser.polynomial_mul_ratio_pow_le_inv q r (B q) C hq hBn hC hl hlarge
  · exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

noncomputable def thinningCutoff (β : ℝ) (q : ℕ) : ℕ :=
  Nat.floor ((q : ℝ) ^ β) + 1

lemma rpow_lt_thinningCutoff (β : ℝ) (q : ℕ) :
    (q : ℝ) ^ β < (thinningCutoff β q : ℝ) := by
  simpa [thinningCutoff] using Nat.lt_floor_add_one ((q : ℝ) ^ β)

lemma tendsto_thinningCutoff_atTop {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun q : ℕ => (thinningCutoff β q : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (fun q => (rpow_lt_thinningCutoff β q).le)
  exact (tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop

lemma eventually_log_le_thinningCutoff {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ q : ℕ in atTop, Real.log (q : ℝ) ≤ (thinningCutoff β q : ℝ) := by
  have h := ((isLittleO_log_rpow_atTop hβ).comp_tendsto
    tendsto_natCast_atTop_atTop).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [h] with q hq
  have hnorm : |Real.log (q : ℝ)| ≤ (q : ℝ) ^ β := by
    simpa only [Function.comp_apply, Real.norm_eq_abs, one_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg q) β)] using hq
  exact (le_abs_self _).trans (hnorm.trans (rpow_lt_thinningCutoff β q).le)

lemma tendsto_polynomial_mul_thinning_tail {β : ℝ} (hβ : 0 < β)
    (r : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun q : ℕ => (q : ℝ) ^ r *
      (C / (thinningCutoff β q : ℝ)) ^ thinningCutoff β q) atTop (𝓝 0) :=
  tendsto_polynomial_mul_ratio_tail (thinningCutoff β)
    (tendsto_thinningCutoff_atTop hβ) (eventually_log_le_thinningCutoff hβ) r C hC

lemma tendsto_post_step_abort_bound (m : ℝ) (hm : 0 ≤ m) :
    Tendsto (fun q : ℕ => (q : ℝ) ^ 3 *
      (Real.exp 1 * m / (thinningCutoff (1 / 8) q : ℝ)) ^ thinningCutoff (1 / 8) q)
      atTop (𝓝 0) :=
  tendsto_polynomial_mul_thinning_tail (by norm_num : (0 : ℝ) < 1 / 8)
    3 (Real.exp 1 * m) (mul_nonneg (Real.exp_pos 1).le hm)

lemma tendsto_polynomial_mul_factorial_thinning_tail {β : ℝ} (hβ : 0 < β)
    (r : ℕ) (m : ℝ) (hm : 0 ≤ m) :
    Tendsto (fun q : ℕ => (q : ℝ) ^ r *
      (m ^ thinningCutoff β q / (thinningCutoff β q).factorial)) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_
    (tendsto_polynomial_mul_thinning_tail hβ r (Real.exp 1 * m) (by positivity))
  · exact Filter.Eventually.of_forall (fun q => by positivity)
  · apply Filter.Eventually.of_forall
    intro q
    apply mul_le_mul_of_nonneg_left
    · exact Balanced.pow_div_factorial_le_exp_ratio m hm _ (by simp [thinningCutoff])
    · positivity

lemma tendsto_thinning_test_union
    (Ω : ℕ → Type*) (J : ℕ → Type*) [∀ q, MeasurableSpace (Ω q)]
    [∀ q, Fintype (J q)] (μ : (q : ℕ) → MeasureTheory.Measure (Ω q))
    [∀ q, MeasureTheory.IsProbabilityMeasure (μ q)]
    (E : (q : ℕ) → J q → Set (Ω q)) (m C : ℝ) (hm : 0 ≤ m) (_hC : 0 ≤ C)
    (hcard : ∀ᶠ q : ℕ in atTop, (Fintype.card (J q) : ℝ) ≤ C * (q : ℝ) ^ 3)
    (htail : ∀ᶠ q : ℕ in atTop, ∀ j,
      (μ q).real (E q j) ≤
        (Real.exp 1 * m / (thinningCutoff (1 / 8) q : ℝ)) ^ thinningCutoff (1 / 8) q) :
    Tendsto (fun q => (μ q).real (⋃ j, E q j)) atTop (𝓝 0) := by
  have hlimit := (tendsto_post_step_abort_bound m hm).const_mul C
  simp only [mul_zero] at hlimit
  refine squeeze_zero' ?_ ?_ hlimit
  · exact Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)
  · filter_upwards [hcard, htail] with q hc ht
    calc
      (μ q).real (⋃ j, E q j) ≤ ∑ j, (μ q).real (E q j) :=
        MeasureTheory.measureReal_iUnion_fintype_le _
      _ ≤ ∑ _ : J q,
          (Real.exp 1 * m / (thinningCutoff (1 / 8) q : ℝ)) ^ thinningCutoff (1 / 8) q :=
        Finset.sum_le_sum (fun j _ => ht j)
      _ = (Fintype.card (J q) : ℝ) *
          (Real.exp 1 * m / (thinningCutoff (1 / 8) q : ℝ)) ^ thinningCutoff (1 / 8) q := by simp
      _ ≤ C * ((q : ℝ) ^ 3 *
          (Real.exp 1 * m / (thinningCutoff (1 / 8) q : ℝ)) ^ thinningCutoff (1 / 8) q) := by
        rw [← mul_assoc]
        apply mul_le_mul_of_nonneg_right hc
        positivity

end Balanced.BernoulliTail

end OAI
