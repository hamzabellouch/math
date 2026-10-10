import OAI.Probability.SLE.Stochastic.PlanarCompensated

namespace OAI

/-! Bounded optional stopping for compact smooth planar harmonic tests. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

theorem planar_compact_optional
    (W : WienerLaw) (hW : IsWiener W) (f : ℝ×ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (τ : Driver×Driver → ℝ≥0)
    (hτ : IsStoppingTime planarWienerFiltration (fun b => (τ b : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ b, τ b≤T)
    (hz : ∀ b u, 0≤u → u<(τ b:ℝ) → planarGenerator f (planarWiener u.toNNReal b)=0) :
    (∫ b, f (planarWiener (τ b) b) ∂W.prod W)=∫ b, f (planarWiener 0 b) ∂W.prod W := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  obtain ⟨K,hK,_⟩ := compact_smooth_bounded_lipschitz f hf hc
  obtain ⟨D,hD,_⟩ := planarGenerator_bounded_lipschitz f hf hc
  have hτm := stopping_time_measurable_nnreal hτ
  let V (n : ℕ) (b : Driver×Driver) := f (planarWiener (stopGrid n (τ b)) b)
  let G (u : ℝ) (b : Driver×Driver) := planarGenerator f (planarWiener u.toNNReal b)
  let H (n : ℕ) (b : Driver×Driver) := ∫ u in (0:ℝ)..(stopGrid n (τ b):ℝ), G u b
  have hVm (n : ℕ) : Measurable (V n) :=
    measurable_discrete_eval (fun k b => f (planarWiener (stopGridTime n k) b))
      (fun k => hf.continuous.measurable.comp (measurable_planarWiener _))
      (stopGridIndex_measurable hτm n)
  have hVb (n : ℕ) (b : Driver×Driver) : |V n b|≤K := by
    simpa only [Real.norm_eq_abs] using hK (planarWiener (stopGrid n (τ b)) b)
  have hVi (n : ℕ) : Integrable (V n) (W.prod W) :=
    Integrable.of_bound (hVm n).aestronglyMeasurable K
      (Eventually.of_forall fun b => by simpa only [Real.norm_eq_abs] using hVb n b)
  have hGm : Measurable (Function.uncurry G) := planar_generator_joint_measurable f hf
  have hGb (u b) : |G u b|≤D := hD _
  have hHjoint := cumulative_integral_measurable G hGm
  have hHm (n : ℕ) : Measurable (H n) :=
    measurable_discrete_eval (fun k b => ∫ u in (0:ℝ)..(stopGridTime n k:ℝ), G u b)
      (fun k => hHjoint.comp measurable_prodMk_left) (stopGridIndex_measurable hτm n)
  have hHb (n : ℕ) (b : Driver×Driver) : |H n b|≤(D:ℝ)*(1/((n:ℝ)+1)) :=
    bounded_cumulative_at_grid G hGm D D.coe_nonneg hGb τ hz n b
  have hHi (n : ℕ) : Integrable (H n) (W.prod W) :=
    Integrable.of_bound (hHm n).aestronglyMeasurable _
      (Eventually.of_forall fun b => by simpa only [Real.norm_eq_abs] using hHb n b)
  have hmean (n : ℕ) : (∫ b, V n b ∂W.prod W)-(∫ b, f (planarWiener 0 b) ∂W.prod W)=
      ∫ b, H n b ∂W.prod W := by
    have hh := planar_compensated_grid_integral W hW f hf hc τ hτ T hb n
    change (∫ b, V n b-H n b ∂W.prod W)=_ at hh
    rw [integral_sub (hVi n) (hHi n)] at hh
    linarith
  have herror (n : ℕ) : dist (∫ b, V n b ∂W.prod W) (∫ b, f (planarWiener 0 b) ∂W.prod W)≤
      (D:ℝ)*(1/((n:ℝ)+1)) := by
    rw [Real.dist_eq,hmean]
    have hh := norm_integral_le_of_norm_le_const (μ := W.prod W)
      (f := H n) (C := (D:ℝ)*(1/((n:ℝ)+1)))
      (Eventually.of_forall fun b => by simpa only [Real.norm_eq_abs] using hHb n b)
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh
  have hlim : Tendsto (fun n => ∫ b, V n b ∂W.prod W) atTop
      (𝓝 (∫ b, f (planarWiener (τ b) b) ∂W.prod W)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (K:ℝ))
      (fun n => (hVm n).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun b => by simpa only [Real.norm_eq_abs] using hVb n b)
    exact Eventually.of_forall fun b =>
      (hf.continuous.comp (planarWiener_continuous b)).continuousAt.tendsto.comp (stopGrid_tendsto (τ b))
  have hlim0 : Tendsto (fun n => ∫ b, V n b ∂W.prod W) atTop
      (𝓝 (∫ b, f (planarWiener 0 b) ∂W.prod W)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun n => dist_nonneg) herror
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (D:ℝ)
  exact tendsto_nhds_unique hlim hlim0

end SLEExactGauge

end

end OAI
