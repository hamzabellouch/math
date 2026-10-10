import OAI.Probability.InvariantIsing.Spectral.MeasureRBounds

namespace OAI

/-! Resolvent continuity under weak convergence and convergence of upper
edges. Bounded continuous test functions avoid the pole outside the supports. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical BoundedContinuousFunction

namespace InvariantIsing

theorem measureResolvent_tendsto_weak
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (es : ℕ → ℝ) (e : ℝ) (hweak : Tendsto μs atTop (𝓝 μ))
    (hedge : Tendsto es atTop (𝓝 e))
    (hsupport : ∀ k, ∀ᵐ y ∂(μs k : Measure ℝ), y ≤ es k)
    (hsupport0 : ∀ᵐ y ∂(μ : Measure ℝ), y ≤ e)
    {b : ℝ} (hb : e < b) :
    Tendsto (fun k => measureResolvent (μs k : Measure ℝ) b) atTop
      (𝓝 (measureResolvent (μ : Measure ℝ) b)) := by
  let c := (e + b) / 2
  let d := b - c
  have hec : e < c := by dsimp only [c]; linarith
  have hcb : c < b := by dsimp only [c]; linarith
  have hd : 0 < d := sub_pos.mpr hcb
  let f : ℝ → ℝ := fun y => 1 / max d (b - y)
  have hf : Continuous f := continuous_const.div
    (continuous_const.max (continuous_const.sub continuous_id))
    (fun y => ne_of_gt (hd.trans_le (le_max_left _ _)))
  have hfb y : |f y| ≤ 1 / d := by
    dsimp only [f]
    rw [abs_of_pos (one_div_pos.mpr (hd.trans_le (le_max_left _ _)))]
    exact one_div_le_one_div_of_le hd (le_max_left _ _)
  let F : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ (2 / d) (by
    intro y z
    rw [Real.dist_eq]
    calc
      |f y - f z| ≤ |f y| + |f z| := abs_sub _ _
      _ ≤ 1 / d + 1 / d := add_le_add (hfb y) (hfb z)
      _ = 2 / d := by ring)
  have heq (ν : Measure ℝ) (hν : ∀ᵐ y ∂ν, y ≤ c) :
      (∫ y, F y ∂ν) = measureResolvent ν b := by
    apply integral_congr_ae
    filter_upwards [hν] with y hy
    change 1 / max d (b - y) = 1 / (b - y)
    rw [max_eq_right (by dsimp only [d]; linarith)]
  have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak) F
  rw [heq (μ : Measure ℝ) (hsupport0.mono fun y hy => hy.trans hec.le)] at ht
  apply ht.congr'
  filter_upwards [hedge.eventually (Iio_mem_nhds hec)] with k hk
  exact heq (μs k : Measure ℝ) ((hsupport k).mono fun y hy => hy.trans hk.le)

theorem measureInverse_tendsto_weak
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (es : ℕ → ℝ) (e : ℝ) (hweak : Tendsto μs atTop (𝓝 μ))
    (hedge : Tendsto es atTop (𝓝 e))
    (hsupport : ∀ k, ∀ᵐ y ∂(μs k : Measure ℝ), y ≤ es k)
    (hsupport0 : ∀ᵐ y ∂(μ : Measure ℝ), y ≤ e)
    (xs : ℕ → ℝ) {x : ℝ} (hxs : Tendsto xs atTop (𝓝 x)) (hx : 0 < x) :
    Tendsto (fun k => measureInverse (μs k : Measure ℝ) (es k) (xs k)) atTop
      (𝓝 (measureInverse (μ : Measure ℝ) e x)) := by
  have hbound := (measureInverse_bounds (μ : Measure ℝ) hsupport0 hx).1
  have hxp : ∀ᶠ k in atTop, 0 < xs k := hxs.eventually (Ioi_mem_nhds hx)
  apply tendsto_order.2
  constructor
  · intro l hl
    by_cases hle : l < e
    · filter_upwards [hxp, hedge.eventually (Ioi_mem_nhds hle)] with k hk hek
      exact hek.trans_le (measureInverse_bounds (μs k : Measure ℝ) (hsupport k) hk).1
    · let c := (l + measureInverse (μ : Measure ℝ) e x) / 2
      have hec : e < c := by dsimp only [c]; linarith [le_of_not_gt hle]
      have hlc : l < c := by dsimp only [c]; linarith
      have hci : c < measureInverse (μ : Measure ℝ) e x := by dsimp only [c]; linarith
      have hR : x < measureResolvent (μ : Measure ℝ) c := by
        by_contra hnot
        exact (not_le_of_gt hci)
          ((measureInverse_le_iff (μ : Measure ℝ) hsupport0 hx hec).mpr (le_of_not_gt hnot))
      have hRc := measureResolvent_tendsto_weak μs μ es e hweak hedge hsupport hsupport0 hec
      filter_upwards [hxp, hedge.eventually (Iio_mem_nhds hec), hxs.eventually_lt hRc hR]
        with k hk hek hRk
      apply hlc.trans
      apply lt_of_not_ge
      intro hnot
      exact (not_le_of_gt hRk)
        ((measureInverse_le_iff (μs k : Measure ℝ) (hsupport k) hk hek).mp hnot)
  · intro u hu
    have heu : e < u := hbound.trans_lt hu
    have hR := (measureInverse_lt_iff (μ : Measure ℝ) hsupport0 hx heu).mp hu
    have hRu := measureResolvent_tendsto_weak μs μ es e hweak hedge hsupport hsupport0 heu
    filter_upwards [hxp, hedge.eventually (Iio_mem_nhds heu), hRu.eventually_lt hxs hR]
      with k hk hek hRk
    exact (measureInverse_lt_iff (μs k : Measure ℝ) (hsupport k) hk hek).mpr hRk

end InvariantIsing

end

end OAI
