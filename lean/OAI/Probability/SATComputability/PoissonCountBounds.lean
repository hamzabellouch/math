import OAI.Probability.DilutedSpin.MarkedPoisson

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

theorem poisson_upper_deviation (r : ℝ≥0) {d : ℝ} (hd : 0 < d) :
    (∫ m : ℕ, (if (r : ℝ) + d < m then (1 : ℝ) else 0) ∂poissonMeasure r) ≤
      (r : ℝ) / d^2 := by
  have hi : Integrable (fun m : ℕ => if (r : ℝ)+d < m then (1 : ℝ) else 0)
      (poissonMeasure r) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact ae_of_all _ (fun m => by split <;> norm_num)
  have hs : Integrable (fun m : ℕ => ((m : ℝ)-(r : ℝ))^2) (poissonMeasure r) :=
    ((memLp_two_iff_integrable_sq (measurable_of_countable
      (fun m : ℕ => (m : ℝ))).aestronglyMeasurable).mpr
      (poisson_integrable_count_sq r) |>.sub (memLp_const (r : ℝ))).integrable_sq
  have h := integral_mono hi (hs.div_const (d^2)) (fun m => show
      (if (r : ℝ)+d < m then (1 : ℝ) else 0) ≤ ((m : ℝ)-(r : ℝ))^2 / d^2 from by
    split_ifs with hm
    · apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
      nlinarith
    · exact div_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [integral_div, poisson_variance] at h
  exact h

theorem poisson_density_upper_tail {a : ℝ≥0} {b : ℝ} (hab : (a : ℝ) < b)
    {n : ℕ} (hn : 0 < n) :
    (∫ m : ℕ, (if b*n < m then (1 : ℝ) else 0) ∂poissonMeasure (a*n)) ≤
      (a : ℝ) / ((b-a)^2*n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : 0 < (b-a)*(n : ℝ) := mul_pos (sub_pos.mpr hab) hn'
  have h := poisson_upper_deviation (a*n) hd
  have he : (a*n : ℝ≥0) + (b-(a : ℝ))*(n : ℝ) = b*n := by
    push_cast
    ring
  rw [he] at h
  convert h using 1
  push_cast
  field_simp

theorem poisson_density_upper_tail_tendsto {a : ℝ≥0} {b : ℝ} (hab : (a : ℝ) < b) :
    Tendsto (fun n : ℕ => ∫ m : ℕ, (if b*n < m then (1 : ℝ) else 0)
      ∂poissonMeasure (a*n)) atTop (nhds 0) := by
  have hlim : Tendsto (fun n : ℕ => (a : ℝ) / ((b-a)^2*n)) atTop (nhds 0) := by
    simpa only [mul_zero] using
      ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul
        ((a : ℝ)/(b-a)^2)).congr
        (fun n => by simp only [Function.comp_apply, div_eq_mul_inv, mul_inv]; ring)
  apply squeeze_zero' (Eventually.of_forall (fun n => integral_nonneg (fun m => by positivity)))
    _ hlim
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact poisson_density_upper_tail hab hn

end FixedClauseThreshold.Computability

end OAI
