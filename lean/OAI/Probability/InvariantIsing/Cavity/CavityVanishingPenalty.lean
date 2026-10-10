import OAI.Probability.InvariantIsing.Cavity.CavityLogL1
import OAI.Probability.InvariantIsing.Cavity.CavityCappedLogLimit
import OAI.Probability.InvariantIsing.Cavity.CavityCoefficientError

namespace OAI

/-! The quadratic error in the geometric cavity increment disappears
after taking the expected logarithm of a capped partition function. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_abs_min_cap {h T : ℝ} (hT : 0 ≤ T) : |min h T| ≤ |h| := by
  by_cases hh : h ≤ T
  · rw [min_eq_left hh]
  · rw [min_eq_right (le_of_not_ge hh), abs_of_nonneg hT,
      abs_of_nonneg (hT.trans (le_of_not_ge hh))]
    exact le_of_not_ge hh

lemma cavity_penalized_exp_bound (h r T δ : ℝ) (hδ : 0 ≤ δ) :
    |Real.exp (min h T) - Real.exp (min h T - δ * (1 + r^2))| ≤
      2 * Real.exp T * δ * (1 + r^4) := by
  have hw : 0 ≤ δ * (1 + r^2) := by positivity
  have hh := cavity_exp_sub_le (min_le_right h T)
    (show min h T - δ * (1 + r^2) ≤ T by linarith [min_le_right h T])
  have he : |min h T - (min h T - δ * (1 + r^2))| = δ * (1 + r^2) := by
    rw [show min h T - (min h T - δ * (1 + r^2)) = δ * (1 + r^2) by ring,
      abs_of_nonneg hw]
  rw [he] at hh
  apply hh.trans
  have hrad : 1 + r^2 ≤ 2 * (1 + r^4) := by nlinarith [sq_nonneg (r^2 - 1)]
  nlinarith [mul_le_mul_of_nonneg_left hrad (mul_nonneg (Real.exp_pos T).le hδ)]

theorem cavity_vanishing_quadratic_penalty
    {Ω X : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (H R : (n : ℕ) → Ω n × X n → ℝ)
    (hH : ∀ n, Measurable (H n)) (hR : ∀ n, Measurable (R n))
    (hi : ∀ n ω, Integrable (fun x => R n (ω,x)^4) (ν n ω))
    (hmi : ∀ n, Integrable (fun ω => ∫ x, R n (ω,x)^4 ∂ν n ω) (P n))
    {D M T : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hg : ∀ n ω x, |H n (ω,x)| ≤ D * (1 + R n (ω,x)^2))
    (hMR : ∀ n, (∫ ω, ∫ x, R n (ω,x)^4 ∂ν n ω ∂P n) ≤ M)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hδ1 : ∀ n, δ n ≤ 1)
    (hδlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n =>
      (∫ ω, Real.log (∫ x, Real.exp (min (H n (ω,x)) T) ∂ν n ω) ∂P n) -
      ∫ ω, Real.log (∫ x, Real.exp (min (H n (ω,x)) T -
        δ n * (1 + R n (ω,x)^2)) ∂ν n ω) ∂P n) atTop (𝓝 0) := by
  let G n p := min (H n p) T - δ n * (1 + R n p ^ 2)
  have hG n : Measurable (G n) :=
    ((hH n).min measurable_const).sub
      (measurable_const.mul (measurable_const.add ((hR n).pow_const 2)))
  have hGcap n ω x : min (G n (ω,x)) T = G n (ω,x) := by
    apply min_eq_left
    dsimp only [G]
    have := min_le_right (H n (ω,x)) T
    have : 0 ≤ δ n * (1 + R n (ω,x)^2) := mul_nonneg (hδ n) (by positivity)
    linarith
  have hGgrowth n ω x : |G n (ω,x)| ≤ (D+1) * (1 + R n (ω,x)^2) := by
    dsimp only [G]
    calc
      _ ≤ |min (H n (ω,x)) T| + |δ n * (1 + R n (ω,x)^2)| := abs_sub _ _
      _ ≤ D * (1 + R n (ω,x)^2) + (1 + R n (ω,x)^2) := by
        apply add_le_add ((cavity_abs_min_cap hT).trans (hg n ω x))
        rw [abs_of_nonneg (mul_nonneg (hδ n) (by positivity : 0 ≤ 1 + R n (ω,x)^2))]
        exact mul_le_of_le_one_left (by positivity) (hδ1 n)
      _ = _ := by ring
  have hHgrowth n ω x : |H n (ω,x)| ≤ (D+1) * (1 + R n (ω,x)^2) :=
    (hg n ω x).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  let Z n ω := ∫ x, Real.exp (min (H n (ω,x)) T) ∂ν n ω
  let W n ω := ∫ x, Real.exp (min (G n (ω,x)) T) ∂ν n ω
  have hZ n : Measurable (Z n) :=
    measurable_cavityWeightNormalizer (ν n) (hν n) _ (((hH n).min measurable_const).exp)
  have hW n : Measurable (W n) :=
    measurable_cavityWeightNormalizer (ν n) (hν n) _ (((hG n).min measurable_const).exp)
  have hZi n ω : Integrable (fun x => Real.exp (min (H n (ω,x)) T)) (ν n ω) :=
    integrable_of_measurable_abs_le ((((hH n).min measurable_const).exp).comp
      measurable_prodMk_left) (fun x => by
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (min_le_right _ _))
  have hWi n ω : Integrable (fun x => Real.exp (min (G n (ω,x)) T)) (ν n ω) :=
    integrable_of_measurable_abs_le ((((hG n).min measurable_const).exp).comp
      measurable_prodMk_left) (fun x => by
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (min_le_right _ _))
  have hZ0 n ω : 0 < Z n ω := integral_exp_pos (hZi n ω)
  have hW0 n ω : 0 < W n ω := integral_exp_pos (hWi n ω)
  have hZb n ω : Z n ω ≤ Real.exp T := by
    exact (integral_mono (hZi n ω) (integrable_const _) (fun x =>
      Real.exp_le_exp.mpr (min_le_right _ _))).trans_eq (by simp)
  have hWb n ω : W n ω ≤ Real.exp T := by
    exact (integral_mono (hWi n ω) (integrable_const _) (fun x =>
      Real.exp_le_exp.mpr (min_le_right _ _))).trans_eq (by simp)
  have hZd n := cavity_capped_negative_log_mean_bound (P n) (ν n) (hν n)
    (H n) (R n) (hH n) (hi n) (hmi n) (by positivity : 0 ≤ D+1) hT
    (hHgrowth n) (hMR n)
  have hWd n := cavity_capped_negative_log_mean_bound (P n) (ν n) (hν n)
    (G n) (R n) (hG n) (hi n) (hmi n) (by positivity : 0 ≤ D+1) hT
    (hGgrowth n) (hMR n)
  have hdist : Tendsto (fun n => ∫ ω, |Z n ω - W n ω| ∂P n) atTop (𝓝 0) := by
    have hpoint n ω : |Z n ω - W n ω| ≤
        2 * Real.exp T * δ n * (1 + ∫ x, R n (ω,x)^4 ∂ν n ω) := by
      dsimp only [Z, W]
      rw [← integral_sub (hZi n ω) (hWi n ω)]
      calc
        _ ≤ ∫ x, |Real.exp (min (H n (ω,x)) T) -
            Real.exp (min (G n (ω,x)) T)| ∂ν n ω := abs_integral_le_integral_abs
        _ ≤ ∫ x, 2 * Real.exp T * δ n * (1 + R n (ω,x)^4) ∂ν n ω := by
          apply integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
            (((integrable_const 1).add (hi n ω)).const_mul _)
          exact ae_of_all _ fun x => by
            change |Real.exp (min (H n (ω,x)) T) - Real.exp (min (G n (ω,x)) T)| ≤
              2 * Real.exp T * δ n * (1 + R n (ω,x)^4)
            rw [hGcap]
            exact cavity_penalized_exp_bound _ _ _ _ (hδ n)
        _ = _ := by
          rw [integral_const_mul, integral_add (integrable_const 1) (hi n ω)]
          simp only [integral_const, probReal_univ, one_smul]
    have hb n : (∫ ω, |Z n ω - W n ω| ∂P n) ≤ 2 * Real.exp T * (1+M) * δ n := by
      calc
        _ ≤ ∫ ω, 2 * Real.exp T * δ n * (1 + ∫ x, R n (ω,x)^4 ∂ν n ω) ∂P n :=
          integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
            (((integrable_const 1).add (hmi n)).const_mul _) (ae_of_all _ (hpoint n))
        _ = 2 * Real.exp T * δ n * (1 + ∫ ω, ∫ x, R n (ω,x)^4 ∂ν n ω ∂P n) := by
          rw [integral_const_mul, integral_add (integrable_const 1) (hmi n)]
          simp only [integral_const, probReal_univ, one_smul]
        _ ≤ 2 * Real.exp T * (1+M) * δ n := by
          calc
            _ ≤ 2 * Real.exp T * δ n * (1+M) :=
              mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) (hMR n))
                (mul_nonneg (by positivity) (hδ n))
            _ = _ := by ring
    exact squeeze_zero (fun n => integral_nonneg fun _ => abs_nonneg _) hb
      (by simpa using hδlim.const_mul (2 * Real.exp T * (1+M)))
  have hout := cavity_log_of_mean_distance P Z W hZ hW (Real.one_le_exp hT)
    (by positivity : 0 ≤ 2 * (D+1)^2 * (1+M)) hZ0 hW0 hZb hWb
    (fun n => (hZd n).1) (fun n => (hWd n).1)
    (fun n => (hZd n).2) (fun n => (hWd n).2) hdist
  simpa only [Z, W, hGcap, G] using hout

end InvariantIsing

end

end OAI
