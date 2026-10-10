import OAI.Probability.SLE.Stochastic.PlanarSamplingGrid

namespace OAI

/-! Passing finite-grid conditional sampling to bounded stopping times
for compact smooth planar harmonic tests. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

lemma planar_compensated_grid_tendsto
    (W : WienerLaw) (hW : IsWiener W) (f : ℝ×ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (ρ : Driver×Driver → ℝ≥0) (hρ : Measurable ρ) (A : Set (Driver×Driver))
    (hz : ∀ b u, 0 ≤ u → u<(ρ b:ℝ) → planarGenerator f (planarWiener u.toNNReal b)=0) :
    Tendsto (fun n => ∫ b in A, planarCompensated f (stopGrid n (ρ b)) b ∂W.prod W)
      atTop (𝓝 (∫ b in A, f (planarWiener (ρ b) b) ∂W.prod W)) := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  obtain ⟨K,hK,_⟩ := compact_smooth_bounded_lipschitz f hf hc
  obtain ⟨D,hD,_⟩ := planarGenerator_bounded_lipschitz f hf hc
  let V (n : ℕ) (b : Driver×Driver) := f (planarWiener (stopGrid n (ρ b)) b)
  let G (u : ℝ) (b : Driver×Driver) := planarGenerator f (planarWiener u.toNNReal b)
  let H (n : ℕ) (b : Driver×Driver) := ∫ u in (0:ℝ)..(stopGrid n (ρ b):ℝ), G u b
  have hVm (n : ℕ) : Measurable (V n) :=
    measurable_discrete_eval (fun k b => f (planarWiener (stopGridTime n k) b))
      (fun k => hf.continuous.measurable.comp (measurable_planarWiener _))
      (stopGridIndex_measurable hρ n)
  have hVi (n : ℕ) : Integrable (V n) ((W.prod W).restrict A) :=
    Integrable.of_bound (hVm n).aestronglyMeasurable K (Eventually.of_forall fun b => hK _)
  have hVlim : Tendsto (fun n => ∫ b in A, V n b ∂W.prod W) atTop
      (𝓝 (∫ b in A, f (planarWiener (ρ b) b) ∂W.prod W)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (K:ℝ))
      (fun n => (hVm n).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun b => hK _)
    exact Eventually.of_forall fun b =>
      (hf.continuous.comp (planarWiener_continuous b)).continuousAt.tendsto.comp (stopGrid_tendsto (ρ b))
  have hGm : Measurable (Function.uncurry G) := planar_generator_joint_measurable f hf
  have hGb (u b) : |G u b|≤D := hD _
  have hHjoint := cumulative_integral_measurable G hGm
  have hHm (n : ℕ) : Measurable (H n) :=
    measurable_discrete_eval (fun k b => ∫ u in (0:ℝ)..(stopGridTime n k:ℝ), G u b)
      (fun k => hHjoint.comp measurable_prodMk_left) (stopGridIndex_measurable hρ n)
  have hHb (n : ℕ) (b : Driver×Driver) : |H n b|≤(D:ℝ)*(1/((n:ℝ)+1)) :=
    bounded_cumulative_at_grid G hGm D D.coe_nonneg hGb ρ hz n b
  have hHi (n : ℕ) : Integrable (H n) ((W.prod W).restrict A) :=
    Integrable.of_bound (hHm n).aestronglyMeasurable _
      (Eventually.of_forall fun b => by simpa only [Real.norm_eq_abs] using hHb n b)
  have hHbound (n : ℕ) : |∫ b in A, H n b ∂W.prod W|≤(D:ℝ)*(1/((n:ℝ)+1)) := by
    have hh := norm_integral_le_of_norm_le_const (μ := (W.prod W).restrict A)
      (f := H n) (C := (D:ℝ)*(1/((n:ℝ)+1)))
      (Eventually.of_forall fun b => by simpa only [Real.norm_eq_abs] using hHb n b)
    have hm : ((W.prod W).restrict A).real univ≤1 := by
      simpa only [measureReal_def,Measure.restrict_apply_univ] using
        (measureReal_le_one (μ := W.prod W) (s := A))
    have hh' : |∫ b in A, H n b ∂W.prod W| ≤
        (D:ℝ)*(1/((n:ℝ)+1))*((W.prod W).restrict A).real univ := by
      simpa only [Real.norm_eq_abs] using hh
    exact hh'.trans
      (mul_le_of_le_one_right (by positivity) hm)
  have hHlim : Tendsto (fun n => ∫ b in A, H n b ∂W.prod W) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero,Real.norm_eq_abs]
    apply squeeze_zero (fun n => abs_nonneg _) hHbound
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (D:ℝ)
  have he (n) : (∫ b in A, planarCompensated f (stopGrid n (ρ b)) b ∂W.prod W)=
      (∫ b in A, V n b ∂W.prod W)-(∫ b in A, H n b ∂W.prod W) :=
    integral_sub (hVi n) (hHi n)
  simpa only [← he,sub_zero] using hVlim.sub hHlim

theorem planar_compact_optional_between
    (W : WienerLaw) (hW : IsWiener W) (f : ℝ×ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (σ τ : Driver×Driver → ℝ≥0)
    (hσ : IsStoppingTime planarWienerFiltration (fun b => (σ b : WithTop ℝ≥0)))
    (hτ : IsStoppingTime planarWienerFiltration (fun b => (τ b : WithTop ℝ≥0)))
    (hστ : ∀ b, σ b ≤ τ b) (T : ℝ≥0) (hb : ∀ b, τ b ≤ T)
    (A : Set (Driver×Driver)) (hA : MeasurableSet[hσ.measurableSpace] A)
    (hz : ∀ b u, 0 ≤ u → u<(τ b:ℝ) → planarGenerator f (planarWiener u.toNNReal b)=0) :
    (∫ b in A, f (planarWiener (σ b) b) ∂W.prod W)=
      ∫ b in A, f (planarWiener (τ b) b) ∂W.prod W := by
  have hs := planar_compensated_grid_tendsto W hW f hf hc σ
    (stopping_time_measurable_nnreal hσ) A (fun b u hu h => hz b u hu (h.trans_le (hστ b)))
  have ht := planar_compensated_grid_tendsto W hW f hf hc τ
    (stopping_time_measurable_nnreal hτ) A hz
  have he (n) := planar_compensated_grid_sampling W hW f hf hc σ τ hσ hτ hστ T hb A hA n
  have ht' : Tendsto (fun n => ∫ b in A, planarCompensated f (stopGrid n (σ b)) b ∂W.prod W)
      atTop (𝓝 (∫ b in A, f (planarWiener (τ b) b) ∂W.prod W)) := by
    simpa only [he] using ht
  exact tendsto_nhds_unique hs ht'

end SLEExactGauge

end

end OAI
