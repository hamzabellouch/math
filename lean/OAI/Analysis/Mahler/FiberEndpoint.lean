import OAI.Analysis.Mahler.FiberHeight

namespace OAI

/-! Endpoints of the selected global angular fibers. -/

noncomputable section
open Real Complex Set Filter Metric
open scoped Topology
namespace SymmetricMahler
open MahlerConformal

lemma eventually_fiberDomain {q r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hr₁ : r₀ < 1)
    (hq : radialMap r₀ = |q|) : ∀ᶠ r in 𝓝[>] r₀, r ∈ fiberDomain q := by
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hr₁).filter_mono nhdsWithin_le_nhds]
    with r hr hr1
  exact mem_fiberDomain_of_basepoint hr₀ hq ⟨hr,hr1⟩

lemma fiberAngle_neg {q r : ℝ} (hr : r ∈ fiberDomain q) :
    fiberAngle (-q) r = Real.pi - fiberAngle q r := by
  have hn : r ∈ fiberDomain (-q) := by simpa [fiberDomain, abs_neg] using hr
  have hs := fiberAngle_spec hr
  have ht := fiberAngle_spec hn
  apply (Q_strictAntiOn hr.1 hr.2.1).injOn ⟨ht.1.1.le,ht.1.2.le⟩
    ⟨by linarith [hs.1.2],by linarith [hs.1.1]⟩
  rw [ht.2, Q_pi_sub, hs.2]

lemma fiberHeight_neg {q r : ℝ} (hr : r ∈ fiberDomain q) :
    fiberHeight (-q) r = fiberHeight q r := by
  rw [fiberHeight, fiberAngle_neg hr]
  simp only [S, polar_pi_sub, F_odd, F_conj, Complex.neg_im, Complex.conj_im, neg_neg,
    fiberHeight]

/-- On the actual selected angle, the positive real basepoint has angle limit zero. -/
theorem fiberAngle_tendsto_zero {q r₀ : ℝ} (hr₀ : 0 < r₀) (hr₁ : r₀ < 1)
    (hq0 : 0 ≤ q) (hq : radialMap r₀ = |q|) :
    Tendsto (fiberAngle q) (𝓝[>] r₀) (𝓝 0) := by
  have hd := eventually_fiberDomain hr₀.le hr₁ hq
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [hd] with r hr
    exact ha.trans (fiberAngle_spec hr).1.1
  · intro b hb
    let t := min (b/2) (Real.pi/2)
    have ht : 0 < t := lt_min (by linarith) Real.pi_div_two_pos
    have htπ : t < Real.pi := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
    have htb : t < b := (min_le_left _ _).trans_lt (by linarith)
    have hQ : Q r₀ t < q := by
      have h := Q_strictAntiOn hr₀ hr₁
        (show 0 ∈ Icc (0 : ℝ) Real.pi from ⟨le_rfl,Real.pi_pos.le⟩) ⟨ht.le,htπ.le⟩ ht
      rw [Q_zero] at h
      change Q r₀ t < radialMap r₀ at h
      simpa only [hq, abs_of_nonneg hq0] using h
    have hc : ContinuousAt (fun r : ℝ => Q r t) r₀ := by
      have hp : ContinuousAt (fun r : ℝ => polar r t) r₀ := by
        unfold polar
        fun_prop
      have hf := (hasDerivAt_F_series (w := polar r₀ t)
        (by rwa [norm_polar hr₀.le])).continuousAt
      exact Complex.continuous_re.continuousAt.comp (hf.comp (f := fun r : ℝ => polar r t) hp)
    have he : ∀ᶠ r in 𝓝[>] r₀, Q r t < q := (hc.tendsto.eventually (eventually_lt_nhds hQ)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hd, he] with r hr hQr
    have hs := fiberAngle_spec hr
    have hθ : fiberAngle q r < t := by
      by_contra h
      have hh := (Q_strictAntiOn hr.1 hr.2.1).antitoneOn
        ⟨ht.le,htπ.le⟩ ⟨hs.1.1.le,hs.1.2.le⟩ (le_of_not_gt h)
      rw [hs.2] at hh
      linarith
    exact hθ.trans htb

/-- Zero radius is handled by the norm of the actual polar preimage; no
angle at the origin is imposed. -/
theorem fiberHeight_tendsto_at_zero (q : ℝ) :
    Tendsto (fiberHeight q) (𝓝 0) (𝓝 0) := by
  have hn : Tendsto (fun r : ℝ => ‖polar r (fiberAngle q r)‖) (𝓝 0) (𝓝 0) := by
    simpa [polar, Complex.norm_exp] using (continuous_abs.tendsto (0 : ℝ))
  have hp : Tendsto (fun r : ℝ => polar r (fiberAngle q r)) (𝓝 0) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hn
  have hF := (hasDerivAt_F_series (w := 0) (by simp)).continuousAt.tendsto.comp hp
  change Tendsto (fun r => (F (polar r (fiberAngle q r))).im) (𝓝 0) (𝓝 0)
  simpa only [F_zero, Complex.zero_im, Function.comp_def] using Complex.continuous_im.continuousAt.tendsto.comp hF

/-- The endpoint of the selected fiber, including q=0. -/
theorem fiberHeight_tendsto_basepoint {q r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hr₁ : r₀ < 1)
    (hq : radialMap r₀ = |q|) :
    Tendsto (fiberHeight q) (𝓝[>] r₀) (𝓝 0) := by
  rcases hr₀.eq_or_lt with hzero | hpos
  · subst r₀
    exact (fiberHeight_tendsto_at_zero q).mono_left nhdsWithin_le_nhds
  have hnonneg (p : ℝ) (hp : 0 ≤ p) (he : radialMap r₀ = |p|) :
      Tendsto (fiberHeight p) (𝓝[>] r₀) (𝓝 0) := by
    have ht := fiberAngle_tendsto_zero hpos hr₁ hp he
    have hc := (contDiffAt_S_uncurry (θ := 0) hpos hr₁).continuousAt.tendsto
    have hp : Tendsto (fun r : ℝ => (r, fiberAngle p r)) (𝓝[>] r₀) (𝓝 (r₀,0)) :=
      (show Tendsto (fun r : ℝ => r) (𝓝[>] r₀) (𝓝 r₀) from nhdsWithin_le_nhds).prodMk_nhds ht
    change Tendsto (fun r => S r (fiberAngle p r)) (𝓝[>] r₀) (𝓝 0)
    simpa only [Function.comp_def, S_zero] using hc.comp hp
  by_cases hp : 0 ≤ q
  · exact hnonneg q hp hq
  · have hn := hnonneg (-q) (by linarith) (by simpa using hq)
    apply hn.congr'
    filter_upwards [eventually_fiberDomain hr₀ hr₁ hq] with r hr
    exact fiberHeight_neg hr

end SymmetricMahler

end

end OAI
