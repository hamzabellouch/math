import OAI.Analysis.RCDHeat.VolumeComparison

namespace OAI

/-! # Scale-uniform volume comparison from nonnegative curvature

The existing CD support-volume argument gives Euclidean ball-ratio
comparison when K is nonnegative. This removes dependence on |K| at large
radii from the local estimates used to discharge the harmonic gradient input.
-/

open Set Metric MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

private theorem time_le_sigma_of_nonneg_curvature {K N θ t : ℝ}
    (hK : 0 ≤ K) (hN : 1 < N) (hθ : 0 ≤ θ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ENNReal.ofReal t ≤ sigma K N t θ := by
  unfold sigma
  split_ifs with hz hconj hKpos
  · exact le_rfl
  · exact le_top
  · have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm (not_or.mp hz).1)
    have hNm : 0 < N - 1 := sub_pos.mpr hN
    have hroot : 0 < Real.sqrt (K / (N - 1)) := Real.sqrt_pos.mpr (div_pos hKpos hNm)
    have ha : 0 < θ * Real.sqrt (K / (N - 1)) := mul_pos hθpos hroot
    have hsquare : (θ * Real.sqrt (K / (N - 1))) ^ 2 = K * θ ^ 2 / (N - 1) := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg hK hNm.le)]
      ring
    have hsquareLt : (θ * Real.sqrt (K / (N - 1))) ^ 2 < Real.pi ^ 2 := by
      rw [hsquare, div_lt_iff₀ hNm]
      nlinarith only [lt_of_not_ge hconj]
    have haPi : θ * Real.sqrt (K / (N - 1)) < Real.pi := by
      nlinarith only [hsquareLt, Real.pi_pos]
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_assoc] using sin_mul_div_sin_ge ha haPi ht ht1
  · exact False.elim ((not_or.mp hz).2 (le_antisymm (le_of_not_gt hKpos) hK))

private theorem time_le_tau_of_nonneg_curvature {K N θ t : ℝ}
    (hK : 0 ≤ K) (hN : 1 < N) (hθ : 0 ≤ θ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ENNReal.ofReal t ≤ tau K N t θ := by
  have hN0 : 0 < N := zero_lt_one.trans hN
  have hα : 0 ≤ 1 - 1 / N := by
    rw [sub_nonneg, div_le_one hN0]
    exact hN.le
  unfold tau
  split_ifs with htzero htone
  · simp [htzero]
  · simp [htone]
  · calc
      ENNReal.ofReal t = (ENNReal.ofReal t) ^ (1 / N + (1 - 1 / N)) := by
        rw [show 1 / N + (1 - 1 / N) = 1 by ring, ENNReal.rpow_one]
      _ = (ENNReal.ofReal t) ^ (1 / N) * (ENNReal.ofReal t) ^ (1 - 1 / N) :=
        ENNReal.rpow_add_of_nonneg _ _ (by positivity) hα
      _ ≤ _ := mul_le_mul' le_rfl (ENNReal.rpow_le_rpow
        (time_le_sigma_of_nonneg_curvature hK hN hθ ht ht1) hα)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

private theorem tau_zero_curvature {N t θ : ℝ} (hN : 1 < N) :
    tau 0 N t θ = ENNReal.ofReal t := by
  unfold tau
  split_ifs with ht0 ht1
  · simp [ht0]
  · simp [ht1]
  · simp only [sigma, or_true, ite_true]
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity)
      (by rw [sub_nonneg, div_le_one (by linarith)]; linarith)]
    simp

omit [BorelSpace X] in
/-- The nonnegative-curvature CD condition also supplies its zero-curvature
specialization. This keeps the compression constants uniform when the
original positive curvature is arbitrarily large. -/
theorem FullCD.zero_of_nonneg_curvature {μ : Measure X} {K : ℝ} {n : ℕ}
    (hcd : FullCD μ K n) (hn : 2 ≤ n) (hK : 0 ≤ K) : FullCD μ 0 n := by
  intro ν₀ ν₁ hν₀ hν₁ hac₀ hac₁ hm₀ hm₁
  obtain ⟨π, hπ, hgeo, hopt, hbound⟩ := hcd ν₀ ν₁ hν₀ hν₁ hac₀ hac₁ hm₀ hm₁
  refine ⟨π, hπ, hgeo, hopt, ?_⟩
  intro N hN t
  have hN1 : 1 < N := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  apply le_trans (lintegral_mono fun γ => ?_) (hbound N hN t)
  rw [tau_zero_curvature hN1, tau_zero_curvature hN1]
  apply add_le_add
  · exact mul_le_mul' (time_le_tau_of_nonneg_curvature hK hN1 dist_nonneg
      (sub_nonneg.mpr t.2.2) (by linarith [t.2.1])) le_rfl
  · exact mul_le_mul' (time_le_tau_of_nonneg_curvature hK hN1 dist_nonneg t.2.1 t.2.2) le_rfl

/-- Preserve the metric measure structure while lowering a nonnegative
curvature bound to zero. -/
theorem NoncollapsedRCD.zero_of_nonneg_curvature {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (hK : 0 ≤ K) :
    NoncollapsedRCD 0 n X where
  complete := hX.complete
  separable := hX.separable
  geodesic := hX.geodesic
  fullSupport := hX.fullSupport
  finiteOnBounded := hX.finiteOnBounded
  cd := hX.cd.zero_of_nonneg_curvature hn hK
  quadratic := hX.quadratic

theorem FullCD.nonneg_ball_ratio_at_time
    (μ : Measure X) [SigmaFinite μ] (K : ℝ) (n : ℕ) (hcd : FullCD μ K n)
    (hpos : ∀ x : X, ∀ r : ℝ, 0 < r → 0 < μ (Metric.ball x r))
    (hfin : ∀ s : Set X, Bornology.IsBounded s → μ s < ∞)
    (hn : 2 ≤ n) (hK : 0 ≤ K) (p : X) (r R t : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (ht0 : 0 ≤ t) (htr : t*R < r) :
    ENNReal.ofReal t ^ n * μ (Metric.ball p R) ≤ μ (Metric.ball p r) := by
  have hR : 0 < R := hr.trans_le hrR
  have ht1 : t < 1 := by nlinarith
  have hn1 : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0:ℝ) < n := lt_trans zero_lt_one hn1
  let δ := (r-t*R)/(1+t)
  have hδ0 : 0 < δ := div_pos (sub_pos.mpr htr) (by linarith)
  have hδeq : δ*(1+t) = r-t*R := by dsimp [δ]; exact div_mul_cancel₀ _ (by linarith)
  have hδR : δ ≤ R := by nlinarith
  have hsmall0 : μ (Metric.ball p δ) ≠ 0 := (hpos p δ hδ0).ne'
  have hlarge0 : μ (Metric.ball p R) ≠ 0 := (hpos p R hR).ne'
  have hsmalltop : μ (Metric.ball p δ) ≠ ∞ := (hfin _ Metric.isBounded_ball).ne
  have hlargetop : μ (Metric.ball p R) ≠ ∞ := (hfin _ Metric.isBounded_ball).ne
  let T : Time := ⟨t, ht0, ht1.le⟩
  have hroot := hcd.support_volume_bound μ K n
    (Metric.ball p δ) (Metric.ball p R) (Metric.ball p r)
    Metric.isOpen_ball.measurableSet Metric.isOpen_ball.measurableSet Metric.isOpen_ball.measurableSet
    hsmall0 hsmalltop hlarge0 hlargetop
    (uniformOn_finiteSecondMoment μ _ Metric.isOpen_ball.measurableSet hsmall0 hsmalltop p δ
      (fun _ hx => le_of_lt hx))
    (uniformOn_finiteSecondMoment μ _ Metric.isOpen_ball.measurableSet hlarge0 hlargetop p R
      (fun _ hx => le_of_lt hx))
    n le_rfl hn1 T (ENNReal.ofReal t)
    (by
      intro x hx y hy
      exact time_le_tau_of_nonneg_curvature hK hn1 dist_nonneg ht0 ht1.le)
    (by
      intro γ hγ h₀ h₁
      have he : dist (γ T) (γ 0) = t*dist (γ 0) (γ 1) := by
        rw [hγ]
        change |t - 0| * dist (γ 0) (γ 1) = t * dist (γ 0) (γ 1)
        rw [sub_zero, abs_of_nonneg ht0]
      have htri := dist_triangle (γ T) (γ 0) p
      have hend := dist_triangle (γ 0) p (γ 1)
      rw [dist_comm p (γ 1)] at hend
      rw [he] at htri
      change dist (γ 0) p < δ at h₀
      change dist (γ 1) p < R at h₁
      change dist (γ T) p < r
      have hmul := mul_le_mul_of_nonneg_left hend ht0
      have hmul' := mul_le_mul_of_nonneg_left h₁.le ht0
      nlinarith)
  have hpow := ENNReal.rpow_le_rpow hroot hn0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hn0.le, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, one_div_mul_cancel hn0.ne', ENNReal.rpow_one,
    ENNReal.rpow_one, ENNReal.rpow_natCast] at hpow
  exact hpow



theorem FullCD.nonneg_ball_ratio
    (μ : Measure X) [SigmaFinite μ] (K : ℝ) (n : ℕ) (hcd : FullCD μ K n)
    (hpos : ∀ x : X, ∀ r : ℝ, 0 < r → 0 < μ (Metric.ball x r))
    (hfin : ∀ s : Set X, Bornology.IsBounded s → μ s < ∞)
    (hn : 2 ≤ n) (hK : 0 ≤ K) (p : X) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    ENNReal.ofReal (r/R) ^ n * μ (Metric.ball p R) ≤ μ (Metric.ball p r) := by
  have hR : 0 < R := hr.trans_le hrR
  have ht : 0 < r/R := div_pos hr hR
  have hc : Continuous (fun t : ℝ => ENNReal.ofReal t ^ n * μ (Metric.ball p R)) := by
    apply (ENNReal.continuous_mul_const (hfin _ Metric.isBounded_ball).ne).comp
    simpa only [ENNReal.rpow_natCast, Function.comp_def] using
      (ENNReal.continuous_rpow_const (y := (n : ℝ))).comp ENNReal.continuous_ofReal
  apply le_of_tendsto (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
    Tendsto _ (𝓝[<] (r/R)) (𝓝 _))
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioi_mem_nhds ht)] with t htr ht0
  exact hcd.nonneg_ball_ratio_at_time μ K n hpos hfin hn hK p r R t hr hrR ht0.le
    ((lt_div_iff₀ hR).mp htr)


end RegularPointCoordinates

end

end OAI
