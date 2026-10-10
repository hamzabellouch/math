import OAI.Probability.SATComputability.PoissonSATProbability

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

theorem poisson_lower_deviation (r : ℝ≥0) {d : ℝ} (hd : 0 < d) :
    (∫ m : ℕ, (if (m : ℝ) < (r : ℝ)-d then (1 : ℝ) else 0) ∂poissonMeasure r) ≤
      (r : ℝ)/d^2 := by
  have hi : Integrable (fun m : ℕ => if (m : ℝ)<(r : ℝ)-d then (1 : ℝ) else 0)
      (poissonMeasure r) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact ae_of_all _ (fun m => by split <;> norm_num)
  have hs : Integrable (fun m : ℕ => ((m : ℝ)-(r : ℝ))^2) (poissonMeasure r) :=
    ((memLp_two_iff_integrable_sq (measurable_of_countable
      (fun m : ℕ => (m : ℝ))).aestronglyMeasurable).mpr
      (poisson_integrable_count_sq r) |>.sub (memLp_const (r : ℝ))).integrable_sq
  have h := integral_mono hi (hs.div_const (d^2)) (fun m => show
      (if (m : ℝ)<(r : ℝ)-d then (1 : ℝ) else 0) ≤ ((m : ℝ)-(r : ℝ))^2/d^2 from by
    split_ifs with hm
    · apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
      nlinarith
    · exact div_nonneg (sq_nonneg _) (sq_nonneg _))
  rwa [integral_div, poisson_variance] at h

theorem poisson_density_lower_tail_tendsto {a : ℝ≥0} {b : ℝ} (hba : b < (a : ℝ)) :
    Tendsto (fun n : ℕ => ∫ m : ℕ, (if (m : ℝ)<b*n then (1 : ℝ) else 0)
      ∂poissonMeasure (a*n)) atTop (nhds 0) := by
  have hlim : Tendsto (fun n : ℕ => (a : ℝ)/((a-b)^2*n)) atTop (nhds 0) := by
    simpa only [mul_zero] using
      ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul
        ((a : ℝ)/(a-b)^2)).congr
        (fun n => by simp only [Function.comp_apply, div_eq_mul_inv, mul_inv]; ring)
  apply squeeze_zero' (Eventually.of_forall (fun n => integral_nonneg (fun m => by positivity)))
    _ hlim
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : 0 < ((a : ℝ)-b)*(n : ℝ) := mul_pos (sub_pos.mpr hba) hnR
  have h := poisson_lower_deviation (a*n) hd
  have he : ((a*n : ℝ≥0) : ℝ)-((a : ℝ)-b)*(n : ℝ) = b*n := by
    push_cast
    ring
  rw [he] at h
  convert h using 1
  push_cast
  field_simp

theorem auxiliaryPoissonProbability_upper {n : ℕ} (hn : 3 ≤ n) (a : ℝ≥0) (b : ℝ) :
    auxiliaryPoissonProbability n a ≤ properSATProbability n 3 ⌊b*n⌋₊ +
      ∫ m : ℕ, (if (m : ℝ)<b*n then (1 : ℝ) else 0) ∂poissonMeasure (a*n) := by
  have hn0 : 0 < n := by omega
  have hs : Integrable (fun m => auxiliaryProbability n 3 m) (poissonMeasure (a*n)) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact ae_of_all _ (fun m => abs_le.mpr ⟨by linarith [auxiliaryProbability_nonneg n 3 m],
      auxiliaryProbability_le_one hn0 3 m⟩)
  have ht : Integrable (fun m : ℕ => if (m : ℝ)<b*n then (1 : ℝ) else 0)
      (poissonMeasure (a*n)) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact ae_of_all _ (fun m => by split <;> norm_num)
  have h := integral_mono hs ((integrable_const _).add ht) (fun m => show
      auxiliaryProbability n 3 m ≤ properSATProbability n 3 ⌊b*n⌋₊ +
        (if (m : ℝ)<b*n then 1 else 0) from by
    split_ifs with hm
    · exact (auxiliaryProbability_le_one hn0 3 m).trans
        (by linarith [properSATProbability_nonneg n 3 ⌊b*n⌋₊])
    · have hfm : ⌊b*n⌋₊ ≤ m := Nat.floor_le_of_le (le_of_not_gt hm)
      simpa only [add_zero] using (auxiliaryProbability_le_proper hn0 hn m).trans
        (properSATProbability_antitone hn hfm))
  simp only [Pi.add_apply] at h
  simpa only [integral_add (integrable_const _) ht, integral_const, probReal_univ,
    one_smul, auxiliaryPoissonProbability] using h

theorem auxiliaryPoissonProbability_supercritical {a : ℝ≥0}
    (ha : limitingCenter 3 < (a : ℝ)) :
    Tendsto (fun n => auxiliaryPoissonProbability n a) atTop (nhds 0) := by
  obtain ⟨b,hb,hba⟩ := exists_between ha
  have hp := supercritical_limit 3 (by decide) b hb
  have ht := poisson_density_lower_tail_tendsto hba
  have hlim : Tendsto (fun n => properSATProbability n 3 ⌊b*n⌋₊ +
      ∫ m : ℕ, (if (m : ℝ)<b*n then (1 : ℝ) else 0) ∂poissonMeasure (a*n)) atTop (nhds 0) := by
    simpa only [add_zero] using hp.add ht
  apply squeeze_zero' (Eventually.of_forall (fun n =>
    integral_nonneg (fun m => auxiliaryProbability_nonneg n 3 m))) _ hlim
  filter_upwards [eventually_ge_atTop 3] with n hn
  exact auxiliaryPoissonProbability_upper hn a b

end FixedClauseThreshold.Computability

end OAI
