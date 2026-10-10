import OAI.MeasureTheory.Falconer.Fourier.SmoothKernel
import OAI.MeasureTheory.Falconer.Radial.RadialDensity

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Convolution

theorem sourceMollifier_test_tendsto_at {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) (f : Plane → ℝ)
    (hf : Measurable f) (hc : ContinuousAt f 0) :
    Tendsto (fun n => ∫ x, f x ∂sourceDensityMeasure (sourceMollifier (ε n) (hε n)))
      atTop (𝓝 (f 0)) := by
  have ht : Tendsto (fun x : Plane => f (-x)) (𝓝 0) (𝓝 (f 0)) := by
    exact hc.tendsto.comp (by simpa only [neg_zero] using continuous_neg.tendsto (0 : Plane))
  have h := ContDiffBump.convolution_tendsto_right
    (μ := (volume : Measure Plane)) (φ := fun n => sourceBump (ε n) (hε n))
    (g := fun _ : ℕ => fun x : Plane => f (-x)) (k := fun _ => (0 : Plane))
    hlim (Eventually.of_forall (fun _ => (hf.comp measurable_neg).aestronglyMeasurable))
    (ht.comp tendsto_snd) tendsto_const_nhds
  have he (n : ℕ) : (∫ x, f x ∂sourceDensityMeasure (sourceMollifier (ε n) (hε n))) =
      ∫ x, sourceMollifier (ε n) (hε n) x • f x := by
    rw [sourceDensityMeasure,integral_withDensity_eq_integral_toReal_smul
      (sourceMollifier_smooth _ _).continuous.measurable.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (sourceMollifier_nonneg _ _ _)]
  simp_rw [he]
  simpa only [convolution,ContinuousLinearMap.lsmul_apply,zero_sub,neg_neg,sourceMollifier] using h

theorem sourceMollification_test_tendsto (α : Measure Plane) [IsFiniteMeasure α]
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (f : Plane → ℝ) (hf : Measurable f) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C)
    (hc : ∀ᵐ y ∂α, ContinuousAt f y) :
    Tendsto (fun n => ∫ x, f x ∂(α ∗ sourceDensityMeasure (sourceMollifier (ε n) (hε n))))
      atTop (𝓝 (∫ x, f x ∂α)) := by
  let κ := fun n => sourceDensityMeasure (sourceMollifier (ε n) (hε n))
  have hi (n : ℕ) : Integrable f (α ∗ κ n) :=
    (integrable_const C).mono' hf.aestronglyMeasurable (Eventually.of_forall hb)
  have hm (n : ℕ) : AEStronglyMeasurable (fun y => ∫ z, f (y+z) ∂κ n) α :=
    ((hf.comp measurable_add).aestronglyMeasurable).integral_prod_right'
  have hbound (n : ℕ) : ∀ᵐ y ∂α, ‖∫ z, f (y+z) ∂κ n‖ ≤ C := by
    filter_upwards with y
    simpa using norm_integral_le_of_norm_le_const (μ := κ n)
      (Eventually.of_forall (fun z => hb (y+z)))
  have hpoint : ∀ᵐ y ∂α, Tendsto (fun n => ∫ z, f (y+z) ∂κ n) atTop (𝓝 (f y)) := by
    filter_upwards [hc] with y hy
    have hcont : ContinuousAt (fun z : Plane => f (y+z)) 0 := by
      exact hy.comp_of_eq (continuous_const.add continuous_id).continuousAt (add_zero y)
    simpa only [add_zero] using sourceMollifier_test_tendsto_at hε hlim
      (fun z => f (y+z)) (hf.comp (measurable_const.add measurable_id)) hcont
  have h := tendsto_integral_of_dominated_convergence (fun _ => C) hm (integrable_const C) hbound hpoint
  have he (n : ℕ) : (∫ x, f x ∂(α ∗ κ n)) = ∫ y, ∫ z, f (y+z) ∂κ n ∂α := integral_conv (hi n)
  change Tendsto (fun n => ∫ x, f x ∂(α ∗ κ n)) atTop (𝓝 (∫ x, f x ∂α))
  simp_rw [he]
  exact h

theorem continuousAt_sourceRadialUnit (x y : Plane) (hy : y ≠ x) :
    ContinuousAt (sourceRadialUnit x) y := by
  rw [ContinuousAt,tendsto_subtype_rng]
  change ContinuousAt (sourceRadialVector x) y
  have hd : ContinuousAt (fun z : Plane => z-x) y := (continuous_id.sub continuous_const).continuousAt
  have h := (hd.norm.inv₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy))).smul hd
  apply h.congr_of_eventuallyEq
  have hne : ∀ᶠ z in 𝓝 y, z ≠ x := isClosed_singleton.isOpen_compl.mem_nhds hy
  filter_upwards [hne] with z hz
  simp [sourceRadialVector,hz]

theorem sourceMollification_radial_test_tendsto (α : Measure Plane) [IsFiniteMeasure α]
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (x : Plane) (hx : ∀ᵐ y ∂α, y ≠ x) (F : BoundedContinuousFunction UnitCircle ℝ) :
    Tendsto (fun n => ∫ ω, F ω ∂(α ∗ sourceDensityMeasure (sourceMollifier (ε n) (hε n))).map
      (sourceRadialUnit x)) atTop (𝓝 (∫ ω, F ω ∂α.map (sourceRadialUnit x))) := by
  simp_rw [integral_map (measurable_sourceRadialUnit x).aemeasurable F.continuous.aestronglyMeasurable]
  exact sourceMollification_test_tendsto α hε hlim (fun y => F (sourceRadialUnit x y))
    (F.continuous.measurable.comp (measurable_sourceRadialUnit x))
    (fun y => F.norm_coe_le_norm _) (hx.mono (fun y hy =>
      F.continuous.continuousAt.comp (continuousAt_sourceRadialUnit x y hy)))

end PlanarFalconer

end OAI
