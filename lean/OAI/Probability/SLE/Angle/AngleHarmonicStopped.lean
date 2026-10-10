import OAI.Probability.SLE.Angle.AnglePolynomialLogGenerator
import OAI.Probability.SLE.StoppedPower

namespace OAI

/-! Bounded stopping for smooth harmonic tests of the logarithmic Loewner
state and Brownian driver. This supplies the angular eigenfunction moments. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

private lemma compact_harmonic_field
    (Φ : (ℂ × ℝ) × ℝ → ℝ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ φ : (ℂ × ℝ) × ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      (∀ q x, ‖(q, x)‖ ≤ R → φ (q, x) = Φ (q, x)) ∧
      (∀ q x, ‖(q, x)‖ ≤ R → fderiv ℝ φ (q, x) = fderiv ℝ Φ (q, x)) ∧
      (∀ q x, ‖(q, x)‖ ≤ R → iteratedDeriv 2 (fun y => φ (q, y)) x =
        iteratedDeriv 2 (fun y => Φ (q, y)) x) := by
  let b : ContDiffBump (0 : (ℂ × ℝ) × ℝ) := ⟨R + 1, R + 2, by linarith, by linarith⟩
  let φ (z : (ℂ × ℝ) × ℝ) := b z * Φ z
  have hnear (z : (ℂ × ℝ) × ℝ) (hz : ‖z‖ ≤ R) : φ =ᶠ[𝓝 z] Φ := by
    have hb : z ∈ Metric.ball (0 : (ℂ × ℝ) × ℝ) b.rIn := by
      simp only [Metric.mem_ball, dist_zero_right]
      change ‖z‖ < R + 1
      linarith
    filter_upwards [b.eventuallyEq_one_of_mem_ball hb] with w hw
    simp only [φ, hw, Pi.one_apply, one_mul]
  refine ⟨φ, b.contDiff.mul hΦ, b.hasCompactSupport.mul_right,
    (fun q x h => (hnear (q, x) h).eq_of_nhds), ?_, ?_⟩
  · exact fun q x h => (hnear (q, x) h).fderiv_eq
  · intro q x h
    exact ((hnear (q, x) h).comp_tendsto
      ((continuous_const.prodMk continuous_id).tendsto x)).iteratedDeriv_eq 2

private lemma harmonic_pair_directional
    (Φ : (ℂ × ℝ) × ℝ → ℝ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (q v : ℂ × ℝ) (x : ℝ) :
    fderiv ℝ Φ (q, x) (v, 0) = fderiv ℝ (fun r => Φ (r, x)) q v := by
  have hd := (hΦ.differentiable (by simp)) (q, x)
  have hp := (hasFDerivAt_id (𝕜 := ℝ) q).prodMk
    (hasFDerivAt_const (𝕜 := ℝ) (E := ℂ × ℝ) x q)
  have he := congrArg (fun D : (ℂ × ℝ) →L[ℝ] ℝ => D v) (hd.hasFDerivAt.comp q hp).fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, id_eq, zero_apply] using he.symm

lemma ClippedLogSolution.stopped_harmonic_compact
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P) (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (Φ : (ℂ × ℝ) × ℝ → ℝ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hgen : ∀ q x, fderiv ℝ (fun r => Φ (r, x)) q
      (physicalLogLoewnerField (Real.sqrt κ*x) q) +
      (1/2:ℝ)*iteratedDeriv 2 (fun y => Φ (q,y)) x = 0)
    (R : ℝ) (hR : 0 ≤ R) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T)
    (hinside : ∀ ω t, t ≤ τ ω →
      ‖(c.Q t ω, B t ω)‖ ≤ R ∧ (c.Q t ω).1.im ∈ Icc lo hi) :
    Integrable (fun ω => Φ (c.Q (τ ω) ω, B (τ ω) ω)) P ∧
      (∫ ω, Φ (c.Q (τ ω) ω, B (τ ω) ω) ∂P) = Φ (q₀, 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨φ, hφ, hφc, hφeq, hφD, hφ2⟩ := compact_harmonic_field Φ hΦ R hR
  obtain ⟨L₀, K₀, hL₀, _⟩ := clippedLogLoewnerField_bounds lo hi hle
  let V (t : ℝ) (ω : Ω) :=
    clippedLogLoewnerField lo hi hle (Real.sqrt κ * B t.toNNReal ω) (c.Q t ω)
  have hBr : Measurable (fun p : ℝ × Ω => Real.sqrt κ * B p.1.toNNReal p.2) :=
    (hBm.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
      measurable_snd)).const_mul _
  have hpair := hBr.prodMk c.measurable
  have hVm : Measurable (fun p : ℝ × Ω => V p.1 p.2) := by
    change Measurable ((fun p : ℝ × (ℂ × ℝ) => clippedLogLoewnerField lo hi hle p.1 p.2) ∘
      (fun p : ℝ × Ω => (Real.sqrt κ * B p.1.toNNReal p.2, c.Q p.1 p.2)))
    exact (continuous_clippedLogLoewnerField lo hi hle).measurable.comp hpair
  have hVb (t : ℝ) (ω : Ω) : ‖V t ω‖ ≤ (max c.L L₀ : ℝ≥0) :=
    (hL₀ _ _).trans (by exact_mod_cast le_max_right c.L L₀)
  obtain ⟨K, hfield⟩ := compact_state_smooth_brownian_field B hm c.Q V (max c.L L₀)
    c.measurable c.adapted (fun ω => (c.lipschitz ω).weaken (le_max_left _ _)) hVm hVb
    (fun t ω ht => c.derivative ω t ht) φ hφ hφc
  let F (t : ℝ≥0) (ω : Ω) (x : ℝ) := φ (c.Q t ω, x)
  let a (t : ℝ≥0) (ω : Ω) (x : ℝ) := fderiv ℝ φ (c.Q t ω, x) (V t ω, 0)
  have hzero (ω : Ω) (t : ℝ) (ht : t ∈ Icc 0 (τ ω : ℝ)) :
      brownianFieldDrift B F a t ω = 0 := by
    have ht' : t.toNNReal ≤ τ ω := Real.toNNReal_le_iff_le_coe.mpr ht.2
    obtain ⟨hball, hin⟩ := hinside ω t.toNNReal ht'
    have he : (t.toNNReal : ℝ) = t := Real.coe_toNNReal t ht.1
    change fderiv ℝ φ (c.Q (t.toNNReal : ℝ) ω, B t.toNNReal ω)
      (V (t.toNNReal : ℝ) ω, 0) + _ = 0
    dsimp only [V]
    rw [Real.toNNReal_coe, hφD _ _ hball]
    change fderiv ℝ Φ (c.Q (t.toNNReal : ℝ) ω, B t.toNNReal ω)
      (clippedLogLoewnerField lo hi hle (Real.sqrt κ*B t.toNNReal ω)
        (c.Q (t.toNNReal : ℝ) ω), 0) +
      (1/2:ℝ)*iteratedDeriv 2 (fun y => φ (c.Q (t.toNNReal : ℝ) ω,y)) (B t.toNNReal ω)=0
    rw [hφ2 _ _ hball, harmonic_pair_directional Φ hΦ,
      clippedLogLoewnerField_eq_physical lo hi hle _ _ hin]
    exact hgen _ _
  have hopt := brownian_time_field_stopped_dynkin hB hm hBm hBc K F a hfield τ hτ T hb
  have hτm := stopping_time_measurable_nnreal hτ
  have hBmτ := hBm.comp (hτm.prodMk measurable_id)
  have hQmτ := c.measurable.comp
    ((NNReal.continuous_coe.measurable.comp hτm).prodMk measurable_id)
  have hfm := hφ.continuous.measurable.comp (hQmτ.prodMk hBmτ)
  have hfi : Integrable (fun ω => F (τ ω) ω (B (τ ω) ω)) P := by
    apply Integrable.of_bound hfm.aestronglyMeasurable (K : ℝ)
    exact Eventually.of_forall fun ω => by
      change ‖φ (c.Q (τ ω) ω, B (τ ω) ω)‖ ≤ (K : ℝ)
      simpa only [Real.norm_eq_abs, iteratedDeriv_zero] using
        hfield.bound (τ ω) ω (B (τ ω) ω) 0 (by decide)
  have hfeq (ω : Ω) : F (τ ω) ω (B (τ ω) ω) = Φ (c.Q (τ ω) ω,B (τ ω) ω) :=
    hφeq _ _ (hinside ω (τ ω) le_rfl).1
  refine ⟨hfi.congr (Eventually.of_forall hfeq), ?_⟩
  rw [← integral_congr_ae (Eventually.of_forall hfeq),hopt]
  have hz : (fun ω => ∫ t in (0:ℝ)..(τ ω:ℝ), brownianFieldDrift B F a t ω) = 0 := by
    funext ω
    rw [intervalIntegral.integral_congr
      (fun t ht => hzero ω t (by simpa only [uIcc_of_le (τ ω).coe_nonneg] using ht))]
    simp
  rw [hz]
  change (∫ ω, F 0 ω (B 0 ω) ∂P)+(∫ _ : Ω, (0:ℝ) ∂P)=Φ (q₀,0)
  rw [integral_zero,add_zero]
  calc
    _ = ∫ _, Φ (q₀,0) ∂P := by
      apply integral_congr_ae
      filter_upwards [hB.eval_zero_ae_eq_zero] with ω hB0
      change φ (c.Q 0 ω,B 0 ω)=_
      have hh : ‖(c.Q 0 ω,B 0 ω)‖ ≤ R := by
        simpa only [NNReal.coe_zero] using (hinside ω 0 zero_le).1
      rw [hφeq _ _ hh,c.initial ω,hB0]
    _ = _ := by simp

end SLEExactGauge

end

end OAI
