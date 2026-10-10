import OAI.Probability.InvariantIsing.Spectral.MeasureWeakResolvent

namespace OAI

/-! Spectral-transform continuity for compactly supported laws, including
the zero argument and the upper-edge branch. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical BoundedContinuousFunction

namespace InvariantIsing

theorem spectralMean_tendsto_weak
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hweak : Tendsto μs atTop (𝓝 μ)) {K : ℝ} (hK : 0 ≤ K)
    (hs : ∀ k, ∀ᵐ y ∂(μs k : Measure ℝ), y ∈ Icc (-K) K)
    (hμ : ∀ᵐ y ∂(μ : Measure ℝ), y ∈ Icc (-K) K) :
    Tendsto (fun k => ∫ y, y ∂(μs k : Measure ℝ)) atTop
      (𝓝 (∫ y, y ∂(μ : Measure ℝ))) := by
  let f : ℝ → ℝ := fun y => max (-K) (min K y)
  have hf : Continuous f := continuous_const.max (continuous_const.min continuous_id)
  have hb y : |f y| ≤ K := by
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  let F : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ (2 * K) (by
    intro y z
    rw [Real.dist_eq]
    exact (abs_sub _ _).trans ((add_le_add (hb y) (hb z)).trans_eq (by ring)))
  have heq (ν : Measure ℝ) (hν : ∀ᵐ y ∂ν, y ∈ Icc (-K) K) :
      (∫ y, F y ∂ν) = ∫ y, y ∂ν := by
    apply integral_congr_ae
    filter_upwards [hν] with y hy
    change max (-K) (min K y) = y
    rw [min_eq_right hy.2, max_eq_right hy.1]
  have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak) F
  rw [heq (μ : Measure ℝ) hμ] at ht
  exact ht.congr' (Eventually.of_forall fun k => heq (μs k : Measure ℝ) (hs k))

theorem measureR_tendsto_weak_pos
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (es : ℕ → ℝ) (e : ℝ) (hweak : Tendsto μs atTop (𝓝 μ))
    (hedge : Tendsto es atTop (𝓝 e))
    (hs : ∀ k, ∀ᵐ y ∂(μs k : Measure ℝ), y ≤ es k)
    (hμ : ∀ᵐ y ∂(μ : Measure ℝ), y ≤ e)
    (xs : ℕ → ℝ) {x : ℝ} (hxs : Tendsto xs atTop (𝓝 x)) (hx : 0 < x) :
    Tendsto (fun k => measureR (μs k : Measure ℝ) (es k) (xs k)) atTop
      (𝓝 (measureR (μ : Measure ℝ) e x)) := by
  have hi := measureInverse_tendsto_weak μs μ es e hweak hedge hs hμ xs hxs hx
  have hrecip : Tendsto (fun k => 1 / xs k) atTop (𝓝 (1 / x)) :=
    tendsto_const_nhds.div hxs hx.ne'
  have ht : Tendsto
      (fun k => measureInverse (μs k : Measure ℝ) (es k) (xs k) - 1 / xs k)
      atTop (𝓝 (measureR (μ : Measure ℝ) e x)) := by
    simpa only [measureR, ite_eq_left hx] using hi.sub hrecip
  apply ht.congr'
  filter_upwards [hxs.eventually (Ioi_mem_nhds hx)] with k hk
  simp only [measureR, ite_eq_left (show 0 < xs k from hk)]

theorem measureR_tendsto_weak_zero
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (es : ℕ → ℝ) (e : ℝ) (hweak : Tendsto μs atTop (𝓝 μ))
    {K : ℝ} (hK : 0 < K) (he : e ≤ K) (hes : ∀ k, es k ≤ K)
    (hs : ∀ k, ∀ᵐ y ∂(μs k : Measure ℝ), y ∈ Icc (-K) (es k))
    (hμ : ∀ᵐ y ∂(μ : Measure ℝ), y ∈ Icc (-K) e)
    (xs : ℕ → ℝ) (hxs : Tendsto xs atTop (𝓝 0)) :
    Tendsto (fun k => measureR (μs k : Measure ℝ) (es k) (xs k)) atTop
      (𝓝 (measureR (μ : Measure ℝ) e 0)) := by
  have hm := spectralMean_tendsto_weak μs μ hweak hK.le
    (fun k => (hs k).mono fun y hy => ⟨hy.1, hy.2.trans (hes k)⟩)
    (hμ.mono fun y hy => ⟨hy.1, hy.2.trans he⟩)
  have herr : ∀ᶠ k in atTop,
      ‖measureR (μs k : Measure ℝ) (es k) (xs k) - ∫ y, y ∂(μs k : Measure ℝ)‖ ≤
        8 * K ^ 2 * |xs k| := by
    filter_upwards [hxs.eventually (Iio_mem_nhds
      (show (0 : ℝ) < 1 / (4 * K) by positivity))] with k hk
    by_cases hxk : 0 < xs k
    · have hsmall : 4 * K * xs k ≤ 1 := by
        have := (lt_div_iff₀ (show (0 : ℝ) < 4 * K by positivity)).mp hk
        nlinarith
      have hb := measureR_sub_mean_bound (μs k : Measure ℝ) hK (hes k) (hs k) hxk hsmall
      simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1, abs_of_pos hxk] using hb.2
    · simp only [measureR, ite_eq_right hxk, sub_self, norm_zero]
      positivity
  have hb : Tendsto (fun k => 8 * K ^ 2 * |xs k|) atTop (𝓝 0) := by
    simpa using hxs.abs.const_mul (8 * K ^ 2)
  have ht := (squeeze_zero_norm' herr hb).add hm
  simpa only [sub_add_cancel, zero_add, measureR, lt_self_iff_false, ite_false] using ht

end InvariantIsing

end

end OAI
