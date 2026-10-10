import OAI.Probability.SATComputability.AuxiliaryEnergy
import OAI.Probability.SATComputability.PoissonCountBounds
import OAI.Probability.RandomSAT.Main

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology Classical

noncomputable def auxiliaryPoissonProbability (n : ℕ) (a : ℝ≥0) : ℝ :=
  ∫ m : ℕ, auxiliaryProbability n 3 m ∂poissonMeasure (a*n)

theorem auxiliaryPoissonProbability_lower {n : ℕ} (hn : 6 ≤ n) (a : ℝ≥0)
    {b : ℝ} (hb0 : 0 ≤ b) (hbcap : b ≤ capMultiplier 3) :
    transferFactor 3 * properSATProbability n 3 ⌊b*n⌋₊ *
      (1 - ∫ m : ℕ, (if b*n < m then (1 : ℝ) else 0) ∂poissonMeasure (a*n)) ≤
      auxiliaryPoissonProbability n a := by
  have hn0 : 0 < n := by omega
  have h3 : 3 ≤ n := by omega
  have hcap := floor_density_le_cap (n := n) hb0 hbcap
  let c := transferFactor 3 * properSATProbability n 3 ⌊b*n⌋₊
  have hp : ∀ m : ℕ, c * (1 - if b*n < m then (1 : ℝ) else 0) ≤ auxiliaryProbability n 3 m := by
    intro m
    by_cases hm : b*n < m
    · simpa only [ite_eq_left hm, sub_self, mul_zero] using auxiliaryProbability_nonneg n 3 m
    · have hmc : m ≤ ⌊b*n⌋₊ := Nat.le_floor (le_of_not_gt hm)
      have hfac := properFraction_pow_lower hn0 h3
        (by norm_num [repeatPairs]; omega : 2 * repeatPairs 3 ≤ n) (hmc.trans hcap)
      have hsat := properSATProbability_antitone h3 hmc
      have hprod := mul_le_mul hfac hsat (properSATProbability_nonneg n 3 _)
        (pow_nonneg (properFraction_nonneg n 3) m)
      simpa only [ite_eq_right hm, sub_zero, mul_one, c] using
        hprod.trans (proper_scaled_le_auxiliaryProbability hn0 h3 m)
  have hi : Integrable (fun m : ℕ => if b*n < m then (1 : ℝ) else 0)
      (poissonMeasure (a*n)) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact ae_of_all _ (fun m => by split <;> norm_num)
  have ha : Integrable (fun m => auxiliaryProbability n 3 m) (poissonMeasure (a*n)) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact ae_of_all _ (fun m => abs_le.mpr ⟨by linarith [auxiliaryProbability_nonneg n 3 m],
      auxiliaryProbability_le_one hn0 3 m⟩)
  have h := integral_mono ((integrable_const 1).sub hi |>.const_mul c) ha hp
  rw [integral_const_mul] at h
  simp only [Pi.sub_apply] at h
  rw [integral_sub (integrable_const 1) hi] at h
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, c,
    auxiliaryPoissonProbability] using h

theorem auxiliaryPoissonProbability_subcritical {a : ℝ≥0}
    (ha : (a : ℝ) < limitingCenter 3) :
    ∀ᶠ n : ℕ in atTop, transferFactor 3 / 4 ≤ auxiliaryPoissonProbability n a := by
  obtain ⟨b, hab, hb⟩ := exists_between ha
  have hb0 : 0 ≤ b := (show (0 : ℝ) ≤ a from a.property).trans hab.le
  have hbcap : b ≤ capMultiplier 3 := (hb.trans (limitingCenter_lt_cap 3 (by decide))).le
  have hs := (subcritical_limit 3 (by decide) b hb0 hb).eventually
    (Ioi_mem_nhds (by norm_num : (1/2 : ℝ) < 1))
  have ht := (poisson_density_upper_tail_tendsto hab).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [hs, ht, eventually_ge_atTop 6] with n hn ht hn6
  have h := auxiliaryPoissonProbability_lower hn6 a hb0 hbcap
  have hc := transferFactor_pos 3
  have hx : (1/4 : ℝ) ≤ properSATProbability n 3 ⌊b*n⌋₊ *
      (1 - ∫ m : ℕ, (if b*n < m then (1 : ℝ) else 0) ∂poissonMeasure (a*n)) := by
    have hmul := mul_le_mul hn.le (show (1/2 : ℝ) ≤ 1 -
      ∫ m : ℕ, (if b*n < m then (1 : ℝ) else 0) ∂poissonMeasure (a*n) by linarith)
      (by norm_num : (0 : ℝ) ≤ 1/2) (properSATProbability_nonneg n 3 ⌊b*n⌋₊)
    norm_num at hmul
    exact hmul
  have hprod := mul_le_mul_of_nonneg_left hx hc.le
  nlinarith

end FixedClauseThreshold.Computability

end OAI
