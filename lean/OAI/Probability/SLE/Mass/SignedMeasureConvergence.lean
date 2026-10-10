import OAI.Probability.SLE.Mass.RadonKernelIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Normed.Group.FunctionSeries

namespace OAI

/-! Small analytic passages used for the conditional mass kernel. -/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SLEExactGauge

theorem integral_tendsto_of_lintegral_pos_neg
    {X : Type*} [MeasurableSpace X] (μ : ℕ → Measure X) (ν : Measure X)
    (f : X → ℝ) (hμ : ∀ n, Integrable f (μ n)) (hν : Integrable f ν)
    (hpos : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (f x) ∂μ n) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (f x) ∂ν)))
    (hneg : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (-f x) ∂μ n) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (-f x) ∂ν))) :
    Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν)) := by
  have hp := (ENNReal.tendsto_toReal (lintegral_ofReal_lt_top_of_integrable hν).ne).comp hpos
  have hn := (ENNReal.tendsto_toReal (lintegral_ofReal_lt_top_of_integrable hν.neg).ne).comp hneg
  have hh := hp.sub hn
  dsimp only [Function.comp_def,Pi.neg_apply] at hh
  rw [← integral_eq_lintegral_pos_part_sub_lintegral_neg_part hν] at hh
  exact hh.congr' (Eventually.of_forall (fun n =>
    (integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hμ n)).symm))

theorem real_convex_tail_tendsto (f : ℕ → ℝ) {a : ℝ}
    (hf : Tendsto f atTop (𝓝 a)) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (hw₀ : ∀ n i, i ∈ s n → 0 ≤ w n i) (hw₁ : ∀ n, ∑ i ∈ s n, w n i = 1) :
    Tendsto (fun n => ∑ i ∈ s n, w n i * f (n+i)) atTop (𝓝 a) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hf (ε/2) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have he : (∑ i ∈ s n, w n i * f (n+i)) - a =
      ∑ i ∈ s n, w n i * (f (n+i)-a) := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hw₁ n,one_mul]
  calc
    dist (∑ i ∈ s n, w n i * f (n+i)) a =
        ‖∑ i ∈ s n, w n i * (f (n+i)-a)‖ := by rw [dist_eq_norm,he]
    _ ≤ ∑ i ∈ s n, ‖w n i * (f (n+i)-a)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s n, w n i * (ε/2) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul,Real.norm_of_nonneg (hw₀ n i hi)]
      exact mul_le_mul_of_nonneg_left (le_of_lt (hN (n+i) (by omega))) (hw₀ n i hi)
    _ = ε/2 := by rw [← Finset.sum_mul,hw₁ n,one_mul]
    _ < ε := by linarith


lemma integral_indicator_one_mul
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (E : Set Ω)
    (hE : MeasurableSet E) (f : Ω → ℝ) :
    (∫ ω, E.indicator (fun _ => (1 : ℝ)) ω * f ω ∂P) = ∫ ω in E, f ω ∂P := by
  rw [← integral_indicator hE]
  congr 1
  funext ω
  by_cases hω : ω ∈ E
  · simp only [indicator_of_mem hω,one_mul]
  · simp only [indicator_of_notMem hω,zero_mul]

theorem setIntegral_tendsto_of_L2_pairings
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (F : ℕ → Ω → ℝ) (f : Ω → ℝ)
    (hp : ∀ a : Ω → ℝ, MemLp a 2 P →
      Tendsto (fun n => ∫ ω, a ω * F n ω ∂P) atTop (𝓝 (∫ ω, a ω * f ω ∂P)))
    (E : Set Ω) (hE : MeasurableSet E) :
    Tendsto (fun n => ∫ ω in E, F n ω ∂P) atTop (𝓝 (∫ ω in E, f ω ∂P)) := by
  have ha : MemLp (E.indicator (fun _ => (1 : ℝ))) 2 P := (memLp_const 1).indicator hE
  have hh := hp (E.indicator (fun _ => 1)) ha
  simpa only [integral_indicator_one_mul P E hE] using hh


theorem mean_test_tendsto_of_L2_pairings
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsFiniteMeasure P] (μ : ℕ → Ω → Measure X) (ν : Ω → Measure X)
    (hμ : ∀ n, Measurable (μ n)) (hν : Measurable ν) (f : X → ℝ) (hf : Measurable f)
    (hμi : ∀ n ω, Integrable f (μ n ω)) (hνi : ∀ ω, Integrable f (ν ω))
    (E : Set Ω) (hE : MeasurableSet E)
    (hμP : ∀ n, Integrable f ((P.restrict E).bind (μ n)))
    (hνP : Integrable f ((P.restrict E).bind ν))
    (hp : ∀ a : Ω → ℝ, MemLp a 2 P →
      Tendsto (fun n => ∫ ω, a ω * (∫ x, f x ∂μ n ω) ∂P) atTop
        (𝓝 (∫ ω, a ω * (∫ x, f x ∂ν ω) ∂P))) :
    Tendsto (fun n => ∫ x, f x ∂(P.restrict E).bind (μ n)) atTop
      (𝓝 (∫ x, f x ∂(P.restrict E).bind ν)) := by
  have he (n : ℕ) := integral_bind_of_integrable_sections (P.restrict E) (μ n) (hμ n) f hf
    (hμi n) (hμP n)
  have hev := integral_bind_of_integrable_sections (P.restrict E) ν hν f hf hνi hνP
  simpa only [he,hev] using setIntegral_tendsto_of_L2_pairings P
    (fun n ω => ∫ x, f x ∂μ n ω) (fun ω => ∫ x, f x ∂ν ω) hp E hE

end SLEExactGauge

end

end OAI
