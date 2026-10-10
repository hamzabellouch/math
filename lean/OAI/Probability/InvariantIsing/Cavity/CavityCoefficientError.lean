import OAI.Probability.InvariantIsing.Cavity.CavityContinuousCutoff

namespace OAI

/-! Quantitative replacement of the finite cavity blocks by their limits.
The energy cap keeps the exponential Lipschitz constant independent of the
Gaussian marks; only their second moments enter the remaining error. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_exp_sub_le {u v B : ℝ} (hu : u ≤ B) (hv : v ≤ B) :
    |Real.exp u - Real.exp v| ≤ Real.exp B * |u - v| := by
  have hone {a b : ℝ} (hab : b ≤ a) (ha : a ≤ B) :
      Real.exp a - Real.exp b ≤ Real.exp B * (a - b) := by
    have ht := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (b - a))
      (Real.exp_pos a).le
    have he : Real.exp a * Real.exp (b - a) = Real.exp b := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he] at ht
    have hm := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ha) (sub_nonneg.mpr hab)
    nlinarith
  rcases le_total v u with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact hone h hu
  · rw [abs_sub_comm (Real.exp u), abs_sub_comm u,
      abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact hone h hv

lemma cavity_capped_exp_sub_le (u v T : ℝ) :
    |Real.exp (min u T) - Real.exp (min v T)| ≤ Real.exp T * |u - v| := by
  apply (cavity_exp_sub_le (min_le_right _ _) (min_le_right _ _)).trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos T).le
  simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg (u - v))] using
    abs_min_sub_min_le_max u T v T

lemma cavityLogFactor_sub {d k : ℕ}
    (K K' : Matrix (Fin d) (Fin d) ℝ) (L L' : Matrix (Fin d) (Fin k) ℝ)
    (C C' : Matrix (Fin k) (Fin k) ℝ) (y : Fin d → ℝ) (ε : Spin k) :
    cavityLogFactor K L C y ε - cavityLogFactor K' L' C' y ε =
      cavityLogFactor (K - K') (L - L') (C - C') y ε := by
  simp only [cavityLogFactor, cavityQuadratic_sub, Matrix.sub_apply,
    mul_sub, sub_mul, Finset.sum_sub_distrib]
  ring

theorem cavity_capped_replica_coefficient_error {d k r : ℕ}
    (K K' : Matrix (Fin d) (Fin d) ℝ) (L L' : Matrix (Fin d) (Fin k) ℝ)
    (C C' : Matrix (Fin k) (Fin k) ℝ) (T : ℝ)
    (y : Fin r → EuclideanSpace ℝ (Fin d)) (ε : Fin r → Spin k) :
    |(∏ i, Real.exp (min (cavityLogFactor K L C (y i) (ε i)) T)) -
      ∏ i, Real.exp (min (cavityLogFactor K' L' C' (y i) (ε i)) T)| ≤
      Real.exp ((r : ℝ) * T) * cavityFactorSize (K - K') (L - L') (C - C') *
        ∑ i, (1 + ‖y i‖ ^ 2) := by
  rw [← Real.exp_sum, ← Real.exp_sum]
  have hu : (∑ i, min (cavityLogFactor K L C (y i) (ε i)) T) ≤ (r : ℝ) * T := by
    exact (Finset.sum_le_sum (fun _ _ => min_le_right _ _)).trans_eq (by simp)
  have hv : (∑ i, min (cavityLogFactor K' L' C' (y i) (ε i)) T) ≤ (r : ℝ) * T := by
    exact (Finset.sum_le_sum (fun _ _ => min_le_right _ _)).trans_eq (by simp)
  apply (cavity_exp_sub_le hu hv).trans
  have hs : |(∑ i, min (cavityLogFactor K L C (y i) (ε i)) T) -
      ∑ i, min (cavityLogFactor K' L' C' (y i) (ε i)) T| ≤
      cavityFactorSize (K - K') (L - L') (C - C') * ∑ i, (1 + ‖y i‖ ^ 2) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    have hc : |min (cavityLogFactor K L C (y i) (ε i)) T -
        min (cavityLogFactor K' L' C' (y i) (ε i)) T| ≤
        |cavityLogFactor K L C (y i) (ε i) - cavityLogFactor K' L' C' (y i) (ε i)| := by
      simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg
        (cavityLogFactor K L C (y i) (ε i) - cavityLogFactor K' L' C' (y i) (ε i)))] using
        abs_min_sub_min_le_max (cavityLogFactor K L C (y i) (ε i)) T
          (cavityLogFactor K' L' C' (y i) (ε i)) T
    rw [cavityLogFactor_sub] at hc
    exact hc.trans (cavity_logFactor_growth (K - K') (L - L') (C - C') (y i) (ε i))
  exact (mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le).trans_eq (by ring)

end InvariantIsing

end

end OAI
