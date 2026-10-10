import OAI.Probability.InvariantIsing.Cavity.CavityCoefficientError
import OAI.Probability.InvariantIsing.Cavity.CavityCappedLogLimit

namespace OAI

/-! Convergence in probability of a quadratic coefficient error controls
capped normalizers in mean, using the actual prior fourth moment. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

theorem cavity_capped_normalizer_probability_limit
    {Ω X : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (ν : (n : ℕ) → Ω n → Measure (X n)) [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (H G R : (n : ℕ) → Ω n × X n → ℝ)
    (hH : ∀ n, Measurable (H n)) (hG : ∀ n, Measurable (G n))
    (hi : ∀ n ω, Integrable (fun x => R n (ω,x)^4) (ν n ω))
    (hmi : ∀ n, Integrable (fun ω => ∫ x, R n (ω,x)^4 ∂ν n ω) (P n))
    {M : ℝ} (hM : 0 ≤ M) (hMR : ∀ n, (∫ ω, ∫ x, R n (ω,x)^4 ∂ν n ω ∂P n) ≤ M)
    (a : (n : ℕ) → Ω n → ℝ) (ha : ∀ n, Measurable (a n))
    (hchange : ∀ n ω x, |H n (ω,x)-G n (ω,x)| ≤ a n ω*(1+R n (ω,x)^2))
    (hprob : ∀ δ > 0, Tendsto (fun n => (P n).real {ω | δ < a n ω}) atTop (𝓝 0))
    (T : ℝ) :
    Tendsto (fun n => ∫ ω,
      |(∫ x, Real.exp (min (H n (ω,x)) T) ∂ν n ω) -
        ∫ x, Real.exp (min (G n (ω,x)) T) ∂ν n ω| ∂P n) atTop (𝓝 0) := by
  let Z n ω := ∫ x, Real.exp (min (H n (ω,x)) T) ∂ν n ω
  let W n ω := ∫ x, Real.exp (min (G n (ω,x)) T) ∂ν n ω
  have hexp n ω (F : Ω n × X n → ℝ) (hF : Measurable F) :
      Integrable (fun x => Real.exp (min (F (ω,x)) T)) (ν n ω) :=
    integrable_of_measurable_abs_le (((hF.min measurable_const).exp).comp measurable_prodMk_left)
      (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr (min_le_right _ _))
  have hbound n ω : |Z n ω-W n ω| ≤ 2*Real.exp T := by
    have hz : 0 ≤ Z n ω := integral_nonneg (fun _ => (Real.exp_pos _).le)
    have hw : 0 ≤ W n ω := integral_nonneg (fun _ => (Real.exp_pos _).le)
    have hz' : Z n ω ≤ Real.exp T :=
      (integral_mono (hexp n ω (H n) (hH n)) (integrable_const _)
        (fun _ => Real.exp_le_exp.mpr (min_le_right _ _))).trans_eq (by simp)
    have hw' : W n ω ≤ Real.exp T :=
      (integral_mono (hexp n ω (G n) (hG n)) (integrable_const _)
        (fun _ => Real.exp_le_exp.mpr (min_le_right _ _))).trans_eq (by simp)
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg hz, abs_of_nonneg hw]; linarith)
  have hmean (δ : ℝ) (hδ : 0 ≤ δ) (n : ℕ) :
      (∫ ω, |Z n ω-W n ω| ∂P n) ≤
        2*Real.exp T*δ*(1+M)+2*Real.exp T*(P n).real {ω | δ < a n ω} := by
    let bad := {ω : Ω n | δ < a n ω}
    have hbad : MeasurableSet bad := measurableSet_lt measurable_const (ha n)
    have hp ω : |Z n ω-W n ω| ≤
        2*Real.exp T*δ*(1+∫ x, R n (ω,x)^4 ∂ν n ω) +
          2*Real.exp T*bad.indicator (fun _ => (1:ℝ)) ω := by
      by_cases hω : ω ∈ bad
      · rw [indicator_of_mem hω, mul_one]
        exact (hbound n ω).trans (le_add_of_nonneg_left (mul_nonneg (by positivity)
          (by positivity : 0 ≤ 1+∫ x, R n (ω,x)^4 ∂ν n ω)))
      · rw [indicator_of_notMem hω, mul_zero, add_zero]
        dsimp only [Z,W]
        rw [← integral_sub (hexp n ω (H n) (hH n)) (hexp n ω (G n) (hG n))]
        calc
          _ ≤ ∫ x, |Real.exp (min (H n (ω,x)) T)-Real.exp (min (G n (ω,x)) T)| ∂ν n ω :=
            abs_integral_le_integral_abs
          _ ≤ ∫ x, 2*Real.exp T*δ*(1+R n (ω,x)^4) ∂ν n ω := by
            apply integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
              (((integrable_const 1).add (hi n ω)).const_mul _)
            exact ae_of_all _ fun x => by
              change |Real.exp (min (H n (ω,x)) T)-Real.exp (min (G n (ω,x)) T)| ≤
                2*Real.exp T*δ*(1+R n (ω,x)^4)
              have hc := (cavity_capped_exp_sub_le (H n (ω,x)) (G n (ω,x)) T).trans
                (mul_le_mul_of_nonneg_left (hchange n ω x) (Real.exp_pos T).le)
              have hsmall : a n ω ≤ δ := le_of_not_gt hω
              have hrad : 1+R n (ω,x)^2 ≤ 2*(1+R n (ω,x)^4) :=
                by nlinarith [sq_nonneg (R n (ω,x)^2-1)]
              have hb := mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ 1+R n (ω,x)^2)
              have hb' := mul_le_mul_of_nonneg_left hrad hδ
              have hc' := mul_le_mul_of_nonneg_left (hb.trans hb') (Real.exp_pos T).le
              exact hc.trans (hc'.trans_eq (by ring))
          _ = _ := by
            rw [integral_const_mul, integral_add (integrable_const 1) (hi n ω)]
            simp only [integral_const, probReal_univ, one_smul]
    have hiB := (((integrable_const 1).add (hmi n)).const_mul (2*Real.exp T*δ)).add
      (((integrable_const (1:ℝ)).indicator hbad).const_mul (2*Real.exp T))
    calc
      _ ≤ ∫ ω, 2*Real.exp T*δ*(1+∫ x, R n (ω,x)^4 ∂ν n ω) +
          2*Real.exp T*bad.indicator (fun _ => (1:ℝ)) ω ∂P n :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) hiB (ae_of_all _ hp)
      _ = 2*Real.exp T*δ*(1+∫ ω, ∫ x, R n (ω,x)^4 ∂ν n ω ∂P n) +
          2*Real.exp T*(P n).real bad := by
        rw [integral_add, integral_const_mul, integral_add (integrable_const 1) (hmi n),
          integral_const_mul, integral_indicator hbad]
        · simp only [integral_const, smul_eq_mul, mul_one,
            Measure.restrict_apply_univ, measureReal_def, measure_univ, ENNReal.toReal_one]
        · exact ((integrable_const 1).add (hmi n)).const_mul _
        · exact ((integrable_const (1:ℝ)).indicator hbad).const_mul _
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) (hMR n)) (by positivity)) le_rfl
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε/(8*Real.exp T*(1+M))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδeq : 8*Real.exp T*(1+M)*δ = ε := by dsimp only [δ]; field_simp
  have ht : Tendsto (fun n => 2*Real.exp T*(P n).real {ω | δ < a n ω}) atTop (𝓝 0) := by
    simpa only [mul_zero] using (hprob δ hδ).const_mul (2*Real.exp T)
  have htail := ht.eventually
    (gt_mem_nhds (show (0:ℝ) < ε/2 by positivity))
  filter_upwards [htail] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
  have hb := hmean δ hδ.le n
  change 2*Real.exp T*(P n).real {ω | δ < a n ω} < ε/2 at hn
  nlinarith

end InvariantIsing

end

end OAI
