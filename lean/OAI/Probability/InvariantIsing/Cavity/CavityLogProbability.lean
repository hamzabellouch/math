import OAI.Probability.InvariantIsing.Cavity.CavityNormalizerProbability
import OAI.Probability.InvariantIsing.Cavity.CavityLogL1

namespace OAI

/-! A concentrating quadratic coefficient error may be removed from
the expected capped logarithm without an inverse-normalizer assumption. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_capped_log_probability_limit
    {Ω X : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (H G R : (n : ℕ) → Ω n × X n → ℝ)
    (hH : ∀ n, Measurable (H n)) (hG : ∀ n, Measurable (G n))
    (hi : ∀ n ω, Integrable (fun x => R n (ω,x)^4) (ν n ω))
    (hmi : ∀ n, Integrable (fun ω => ∫ x, R n (ω,x)^4 ∂ν n ω) (P n))
    {D M T : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hgH : ∀ n ω x, |H n (ω,x)| ≤ D*(1+R n (ω,x)^2))
    (hgG : ∀ n ω x, |G n (ω,x)| ≤ D*(1+R n (ω,x)^2))
    (hMR : ∀ n, (∫ ω, ∫ x, R n (ω,x)^4 ∂ν n ω ∂P n) ≤ M)
    (a : (n : ℕ) → Ω n → ℝ) (ha : ∀ n, Measurable (a n))
    (hchange : ∀ n ω x, |H n (ω,x)-G n (ω,x)| ≤ a n ω*(1+R n (ω,x)^2))
    (hprob : ∀ δ > 0, Tendsto (fun n => (P n).real {ω | δ < a n ω}) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (∫ ω, Real.log (∫ x, Real.exp (min (H n (ω,x)) T) ∂ν n ω) ∂P n) -
      ∫ ω, Real.log (∫ x, Real.exp (min (G n (ω,x)) T) ∂ν n ω) ∂P n) atTop (𝓝 0) := by
  let Z n ω := ∫ x, Real.exp (min (H n (ω,x)) T) ∂ν n ω
  let W n ω := ∫ x, Real.exp (min (G n (ω,x)) T) ∂ν n ω
  have hZi n := cavity_capped_negative_log_mean_bound (P n) (ν n) (hν n) (H n) (R n)
    (hH n) (hi n) (hmi n) hD hT (hgH n) (hMR n)
  have hWi n := cavity_capped_negative_log_mean_bound (P n) (ν n) (hν n) (G n) (R n)
    (hG n) (hi n) (hmi n) hD hT (hgG n) (hMR n)
  have hexp n ω (F : Ω n × X n → ℝ) (hF : Measurable F) :
      Integrable (fun x => Real.exp (min (F (ω,x)) T)) (ν n ω) :=
    integrable_of_measurable_abs_le (((hF.min measurable_const).exp).comp measurable_prodMk_left)
      (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr (min_le_right _ _))
  have hb n ω (F : Ω n × X n → ℝ) (hF : Measurable F) :
      (∫ x, Real.exp (min (F (ω,x)) T) ∂ν n ω) ≤ Real.exp T :=
    (integral_mono (hexp n ω F hF) (integrable_const _)
      (fun _ => Real.exp_le_exp.mpr (min_le_right _ _))).trans_eq (by simp)
  exact cavity_log_of_mean_distance P Z W
    (fun n => measurable_cavityWeightNormalizer (ν n) (hν n) _ (((hH n).min measurable_const).exp))
    (fun n => measurable_cavityWeightNormalizer (ν n) (hν n) _ (((hG n).min measurable_const).exp))
    (Real.one_le_exp hT) (by positivity : 0 ≤ 2*D^2*(1+M))
    (fun n ω => integral_exp_pos (hexp n ω (H n) (hH n)))
    (fun n ω => integral_exp_pos (hexp n ω (G n) (hG n)))
    (fun n ω => hb n ω (H n) (hH n)) (fun n ω => hb n ω (G n) (hG n))
    (fun n => (hZi n).1) (fun n => (hWi n).1) (fun n => (hZi n).2) (fun n => (hWi n).2)
    (cavity_capped_normalizer_probability_limit P ν H G R hH hG hi hmi hM hMR
      a ha hchange hprob T)

end InvariantIsing

end

end OAI
