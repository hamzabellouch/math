import OAI.Probability.SLE.Gauge.MomentCoefficientConvergence

namespace OAI

/-! Removing the prescribed integer clipping levels under the proved
integrable terminal-moment bound. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace SLEExactGauge

lemma clip_nat_eventually_eq {x : ℝ} (hx : 0≤x) :
    ∀ᶠ n : ℕ in atTop, Target.clip n x=x := by
  obtain ⟨N,hN⟩ := exists_nat_ge x
  filter_upwards [eventually_ge_atTop N] with n hn
  unfold Target.clip
  rw [max_eq_left hx,min_eq_left (hN.trans (Nat.cast_le.mpr hn))]

lemma weighted_clip_integral_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y Z w : Ω → ℝ) (hY : AEStronglyMeasurable Y P) (hw : AEStronglyMeasurable w P)
    (hdom : ∀ᵐ ω ∂P, 0≤w ω ∧ 0≤Y ω ∧ Y ω≤Z ω)
    (m : ℕ) (hi : Integrable (fun ω => w ω*(Z ω)^m) P) (u : ℝ) (hu : 0≤u) :
    0≤(∫ ω, w ω*(Target.clip u (Y ω))^m ∂P) ∧
      (∫ ω, w ω*(Target.clip u (Y ω))^m ∂P)≤∫ ω, w ω*(Z ω)^m ∂P := by
  have hbound : ∀ᵐ ω ∂P, w ω*(Target.clip u (Y ω))^m≤w ω*(Z ω)^m := by
    filter_upwards [hdom] with ω hω
    apply mul_le_mul_of_nonneg_left _ hω.1
    apply pow_le_pow_left₀ (clip_nonneg hu _)
    exact (min_le_left _ _).trans (by simpa only [max_eq_left hω.2.1] using hω.2.2)
  have hn : 0≤ᵐ[P] (fun ω => w ω*(Target.clip u (Y ω))^m) := by
    filter_upwards [hdom] with ω hω
    exact mul_nonneg hω.1 (pow_nonneg (clip_nonneg hu _) m)
  have hiC : Integrable (fun ω => w ω*(Target.clip u (Y ω))^m) P := by
    apply hi.mono' (hw.mul (((continuous_clip u).comp_aestronglyMeasurable hY).pow m))
    filter_upwards [hn,hbound] with ω hω hb
    change ‖w ω*(Target.clip u (Y ω))^m‖≤w ω*(Z ω)^m
    rwa [Real.norm_of_nonneg hω]
  exact ⟨integral_nonneg_of_ae hn,integral_mono_ae hiC hi hbound⟩

theorem weighted_unclip_pow_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y Z w : Ω → ℝ) (hY : AEStronglyMeasurable Y P) (hw : AEStronglyMeasurable w P)
    (hdom : ∀ᵐ ω ∂P, 0≤w ω ∧ 0≤Y ω ∧ Y ω≤Z ω)
    (m : ℕ) (hi : Integrable (fun ω => w ω*(Z ω)^m) P) :
    Tendsto (fun n : ℕ => ∫ ω, w ω*(Target.clip n (Y ω))^m ∂P) atTop
      (𝓝 (∫ ω, w ω*(Y ω)^m ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun ω => ‖w ω*(Z ω)^m‖)
  · intro n
    exact hw.mul (((continuous_clip n).comp_aestronglyMeasurable hY).pow m)
  · exact hi.norm
  · intro n
    filter_upwards [hdom] with ω hω
    have hZ : 0≤Z ω := hω.2.1.trans hω.2.2
    rw [Real.norm_of_nonneg (mul_nonneg hω.1 (pow_nonneg (clip_nonneg (Nat.cast_nonneg n) _) m)),
      Real.norm_of_nonneg (mul_nonneg hω.1 (pow_nonneg hZ m))]
    apply mul_le_mul_of_nonneg_left _ hω.1
    apply pow_le_pow_left₀ (clip_nonneg (Nat.cast_nonneg n) _)
    exact (min_le_left _ _).trans (by simpa only [max_eq_left hω.2.1] using hω.2.2)
  · filter_upwards [hdom] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [clip_nat_eventually_eq hω.2.1] with n hn
    rw [hn]

end SLEExactGauge

end

end OAI
