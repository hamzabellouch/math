import Mathlib

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Problem336AdditiveD139.ContinuousModification

variable {Ω : Type u_1} {E : Type u_2} [MeasurableSpace Ω] {μ : Measure Ω}

theorem ae_cauchySeq_of_summable_bad_increments [MetricSpace E]
    (f : ℕ → Ω → E) (r : ℕ → ℝ) (hr : Summable r)
    (hbad : (∑' n, μ {ω | r n < dist (f n ω) (f (n + 1) ω)}) ≠ ∞) :
    ∀ᵐ ω ∂μ, CauchySeq (fun n => f n ω) := by
  filter_upwards [ae_eventually_notMem hbad] with ω hω
  apply cauchySeq_of_summable_dist
  apply hr.of_norm_bounded_eventually_nat
  filter_upwards [hω] with n hn
  simpa only [Set.mem_ofPred_eq, not_lt, Real.norm_eq_abs, abs_of_nonneg dist_nonneg]
    using hn

theorem exists_measurable_limit_of_summable_bad_increments
    [MetricSpace E] [CompleteSpace E] [Nonempty E]
    [MeasurableSpace E] [BorelSpace E]
    (f : ℕ → Ω → E) (hf : ∀ n, AEMeasurable (f n) μ)
    (r : ℕ → ℝ) (hr : Summable r)
    (hbad : (∑' n, μ {ω | r n < dist (f n ω) (f (n + 1) ω)}) ≠ ∞) :
    ∃ g : Ω → E, Measurable g ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) := by
  let g : Ω → E := fun ω => limUnder atTop (fun n => f n ω)
  have hg : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) := by
    filter_upwards [ae_cauchySeq_of_summable_bad_increments f r hr hbad] with ω hω
    exact hω.tendsto_limUnder
  have hgm : AEMeasurable g μ := aemeasurable_of_tendsto_metrizable_ae atTop hf hg
  refine ⟨hgm.mk g, hgm.measurable_mk, ?_⟩
  filter_upwards [hg, hgm.ae_eq_mk] with ω hω heq
  simpa only [← heq] using hω

theorem ae_eq_of_ae_tendsto_of_tendstoInMeasure [MetricSpace E]
    {f : ℕ → Ω → E} {g h : Ω → E}
    (hg : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hh : TendstoInMeasure μ f atTop h) : g =ᵐ[μ] h := by
  obtain ⟨ns, hns, hlim⟩ := hh.exists_seq_tendsto_ae
  filter_upwards [hg, hlim] with ω hω hω'
  exact tendsto_nhds_unique (hω.comp hns.tendsto_atTop) hω'

theorem exists_measurable_limit_with_modifications
    [MetricSpace E] [CompleteSpace E] [Nonempty E]
    [MeasurableSpace E] [BorelSpace E]
    {T : Type u_3} {V : Type u_4} [MetricSpace V]
    (f : ℕ → Ω → E) (hf : ∀ n, AEMeasurable (f n) μ)
    (r : ℕ → ℝ) (hr : Summable r)
    (hbad : (∑' n, μ {ω | r n < dist (f n ω) (f (n + 1) ω)}) ≠ ∞)
    (eval : T → E → V) (heval : ∀ t, Continuous (eval t))
    (X : T → Ω → V)
    (hX : ∀ t, TendstoInMeasure μ (fun n ω => eval t (f n ω)) atTop (X t)) :
    ∃ g : Ω → E, Measurable g ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) ∧
      ∀ t, (fun ω => eval t (g ω)) =ᵐ[μ] X t := by
  obtain ⟨g, hgm, hg⟩ := exists_measurable_limit_of_summable_bad_increments
    f hf r hr hbad
  refine ⟨g, hgm, hg, fun t => ?_⟩
  apply ae_eq_of_ae_tendsto_of_tendstoInMeasure _ (hX t)
  filter_upwards [hg] with ω hω
  exact ((heval t).tendsto (g ω)).comp hω

end Problem336AdditiveD139.ContinuousModification

end

end OAI
