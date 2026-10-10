import OAI.Probability.InvariantIsing.Spectral.MeasureSpectralContinuity

namespace OAI

/-! Uniform transform convergence and continuity of the variational value
for the compact spectral laws in manuscript Lemma `gen:R-continuity`. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical

namespace InvariantIsing

theorem measureR_tendsto_weak_nonneg
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (es : ℕ → ℝ) (e : ℝ) (hweak : Tendsto μs atTop (𝓝 μ))
    (hedge : Tendsto es atTop (𝓝 e))
    {K : ℝ} (hK : 0 < K) (he : e ≤ K) (hes : ∀ k, es k ≤ K)
    (hs : ∀ k, ∀ᵐ y ∂(μs k : Measure ℝ), y ∈ Icc (-K) (es k))
    (hμ : ∀ᵐ y ∂(μ : Measure ℝ), y ∈ Icc (-K) e)
    (xs : ℕ → ℝ) {x : ℝ} (hxs : Tendsto xs atTop (𝓝 x)) (hx : 0 ≤ x) :
    Tendsto (fun k => measureR (μs k : Measure ℝ) (es k) (xs k)) atTop
      (𝓝 (measureR (μ : Measure ℝ) e x)) := by
  rcases hx.eq_or_lt with hx | hx
  · subst x
    exact measureR_tendsto_weak_zero μs μ es e hweak hK he hes hs hμ xs hxs
  · exact measureR_tendsto_weak_pos μs μ es e hweak hedge
      (fun k => (hs k).mono fun _ h => h.2) (hμ.mono fun _ h => h.2) xs hxs hx

theorem measureR_uniform_weak
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (es : ℕ → ℝ) (e : ℝ) (hweak : Tendsto μs atTop (𝓝 μ))
    (hedge : Tendsto es atTop (𝓝 e))
    {K : ℝ} (hK : 0 < K) (he : e ≤ K) (hes : ∀ k, es k ≤ K)
    (hs : ∀ k, ∀ᵐ y ∂(μs k : Measure ℝ), y ∈ Icc (-K) (es k))
    (hμ : ∀ᵐ y ∂(μ : Measure ℝ), y ∈ Icc (-K) e) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ Icc (0 : ℝ) 1,
      |measureR (μs k : Measure ℝ) (es k) x - measureR (μ : Measure ℝ) e x| < ε := by
  intro ε hε
  by_contra hbad
  have hbad' : ∃ᶠ k in atTop, ∃ x ∈ Icc (0 : ℝ) 1,
      ε ≤ |measureR (μs k : Measure ℝ) (es k) x - measureR (μ : Measure ℝ) e x| := by
    simpa only [Filter.not_eventually, not_forall, not_imp, not_lt, exists_prop] using hbad
  obtain ⟨φ, hφ, hφbad⟩ := extraction_of_frequently_atTop hbad'
  choose xs hxs herr using hφbad
  obtain ⟨x, hx, ψ, hψ, hlim⟩ := isCompact_Icc.tendsto_subseq hxs
  have hR := measureR_tendsto_weak_nonneg (fun k => μs (φ (ψ k))) μ
    (fun k => es (φ (ψ k))) e (hweak.comp (hφ.comp hψ).tendsto_atTop)
    (hedge.comp (hφ.comp hψ).tendsto_atTop) hK he (fun k => hes (φ (ψ k)))
    (fun k => hs (φ (ψ k))) hμ (fun k => xs (ψ k)) hlim hx.1
  have hfixed := (continuous_measureR (μ : Measure ℝ) hK he hμ).continuousAt.tendsto.comp hlim
  have hzero : Tendsto (fun k =>
      |measureR (μs (φ (ψ k)) : Measure ℝ) (es (φ (ψ k))) (xs (ψ k)) -
        measureR (μ : Measure ℝ) e (xs (ψ k))|) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self, abs_zero] using (hR.sub hfixed).abs
  obtain ⟨k, hk⟩ := (hzero.eventually (Iio_mem_nhds hε)).exists
  exact (not_le_of_gt hk) (herr (ψ k))

theorem measureVariational_ne_top_bot (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {K e : ℝ} (hK : 0 < K) (he : e ≤ K) (hμ : ∀ᵐ y ∂μ, y ∈ Icc (-K) e) :
    variationalFunctional (measureR μ e) ≠ ⊤ ∧ variationalFunctional (measureR μ e) ≠ ⊥ := by
  have hR := continuous_measureR μ hK he hμ
  have hb x : |measureR μ e x - 0| ≤ K := by
    have h := measureR_bounds_all μ hμ x
    rw [sub_zero, abs_le]
    exact ⟨h.1, h.2.trans he⟩
  have hspec p : |spectralFunctional (measureR μ e) p| ≤ K / 2 := by
    simpa only [spectralFunctional_constant, zero_div, sub_zero] using
      abs_spectralFunctional_sub_le (measureR μ e) (fun _ => 0) hR continuous_const
        K (fun x _ => hb x) p
  have hupper : variationalFunctional (measureR μ e) ≤ (K / 2 : ℝ) := by
    let p := constantPath 0 (by constructor <;> norm_num)
    have hi := iInf_le (fun p : OverlapPath => entropyFunctional p +
      (spectralFunctional (measureR μ e) p : EReal)) p
    simp only [p, entropyFunctional_zero, zero_add] at hi
    exact hi.trans (by exact_mod_cast (abs_le.mp (hspec p)).2)
  have hlower : ((-(K / 2) : ℝ) : EReal) ≤ variationalFunctional (measureR μ e) := by
    apply le_iInf
    intro p
    have hl : ((-(K / 2) : ℝ) : EReal) ≤ (spectralFunctional (measureR μ e) p : EReal) := by
      exact_mod_cast (abs_le.mp (hspec p)).1
    have hnonneg := add_le_add (entropyFunctional_nonneg p)
      (le_rfl : (spectralFunctional (measureR μ e) p : EReal) ≤ _)
    exact hl.trans (by simpa only [zero_add] using hnonneg)
  exact ⟨ne_top_of_le_ne_top (EReal.coe_ne_top _) hupper,
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlower⟩

theorem measureVariational_tendsto_weak
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (es : ℕ → ℝ) (e : ℝ) (hweak : Tendsto μs atTop (𝓝 μ))
    (hedge : Tendsto es atTop (𝓝 e))
    {K : ℝ} (hK : 0 < K) (he : e ≤ K) (hes : ∀ k, es k ≤ K)
    (hs : ∀ k, ∀ᵐ y ∂(μs k : Measure ℝ), y ∈ Icc (-K) (es k))
    (hμ : ∀ᵐ y ∂(μ : Measure ℝ), y ∈ Icc (-K) e) :
    Tendsto (fun k => (variationalFunctional (measureR (μs k : Measure ℝ) (es k))).toReal)
      atTop (𝓝 (variationalFunctional (measureR (μ : Measure ℝ) e)).toReal) := by
  have hf := measureVariational_ne_top_bot (μ : Measure ℝ) hK he hμ
  have hR := continuous_measureR (μ : Measure ℝ) hK he hμ
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [measureR_uniform_weak μs μ es e hweak hedge hK he hes hs hμ ε hε] with k hk
  have hfk := measureVariational_ne_top_bot (μs k : Measure ℝ) hK (hes k) (hs k)
  have hRk := continuous_measureR (μs k : Measure ℝ) hK (hes k) (hs k)
  have hl := variationalFunctional_le_add _ _ hRk hR ε (fun x hx => (hk x hx).le)
  have hr := variationalFunctional_le_add _ _ hR hRk ε
    (fun x hx => by simpa only [abs_sub_comm] using (hk x hx).le)
  rw [← EReal.coe_toReal hfk.1 hfk.2, ← EReal.coe_toReal hf.1 hf.2,
    ← EReal.coe_add, EReal.coe_le_coe_iff] at hl hr
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end InvariantIsing

end

end OAI
