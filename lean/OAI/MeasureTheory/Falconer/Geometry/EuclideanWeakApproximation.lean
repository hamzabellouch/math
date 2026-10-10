import OAI.MeasureTheory.Falconer.Fourier.EuclideanSmoothConvolution
import OAI.MeasureTheory.Falconer.Estimates.Availability

namespace OAI

/-! Weak convergence of the actual radial pushforwards away from the diagonal. -/
namespace Falconer
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Convolution
variable {d : ℕ}

theorem euclideanMollifier_test_tendsto_at {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) (f : (Space d) → ℝ)
    (hf : Measurable f) (hc : ContinuousAt f 0) :
    Tendsto (fun n => ∫ x, f x ∂euclideanDensityMeasure (euclideanMollifier (ε n) (hε n)))
      atTop (𝓝 (f 0)) := by
  have ht : Tendsto (fun x : (Space d) => f (-x)) (𝓝 0) (𝓝 (f 0)) := by
    exact hc.tendsto.comp (by simpa only [neg_zero] using continuous_neg.tendsto (0 : (Space d)))
  have h := ContDiffBump.convolution_tendsto_right
    (μ := (volume : Measure (Space d))) (φ := fun n => euclideanBump (ε n) (hε n))
    (g := fun _ : ℕ => fun x : (Space d) => f (-x)) (k := fun _ => (0 : (Space d)))
    hlim (Eventually.of_forall (fun _ => (hf.comp measurable_neg).aestronglyMeasurable))
    (ht.comp tendsto_snd) tendsto_const_nhds
  have he (n : ℕ) : (∫ x, f x ∂euclideanDensityMeasure (euclideanMollifier (ε n) (hε n))) =
      ∫ x, euclideanMollifier (ε n) (hε n) x • f x := by
    rw [euclideanDensityMeasure,integral_withDensity_eq_integral_toReal_smul
      (euclideanMollifier_smooth _ _).continuous.measurable.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (euclideanMollifier_nonneg _ _ _)]
  simp_rw [he]
  simpa only [convolution,ContinuousLinearMap.lsmul_apply,zero_sub,neg_neg,euclideanMollifier] using h

theorem euclideanMollification_test_tendsto (α : Measure (Space d)) [IsFiniteMeasure α]
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (f : (Space d) → ℝ) (hf : Measurable f) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C)
    (hc : ∀ᵐ y ∂α, ContinuousAt f y) :
    Tendsto (fun n => ∫ x, f x ∂(α ∗ euclideanDensityMeasure (euclideanMollifier (ε n) (hε n))))
      atTop (𝓝 (∫ x, f x ∂α)) := by
  let κ : ℕ → Measure (Space d) := fun n =>
    euclideanDensityMeasure (euclideanMollifier (ε n) (hε n))
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
    have hcont : ContinuousAt (fun z : (Space d) => f (y+z)) 0 := by
      exact hy.comp_of_eq (continuous_const.add continuous_id).continuousAt (add_zero y)
    simpa only [add_zero] using euclideanMollifier_test_tendsto_at hε hlim
      (fun z => f (y+z)) (hf.comp (measurable_const.add measurable_id)) hcont
  have h := tendsto_integral_of_dominated_convergence (fun _ => C) hm (integrable_const C) hbound hpoint
  have he (n : ℕ) : (∫ x, f x ∂(α ∗ κ n)) = ∫ y, ∫ z, f (y+z) ∂κ n ∂α := integral_conv (hi n)
  change Tendsto (fun n => ∫ x, f x ∂(α ∗ κ n)) atTop (𝓝 (∫ x, f x ∂α))
  simp_rw [he]
  exact h

theorem continuousAt_radialDirection (x y : Space d) (hy : y ≠ x) :
    ContinuousAt (radialDirection x) y := by
  have hd : ContinuousAt (fun z : Space d => z-x) y :=
    (continuous_id.sub continuous_const).continuousAt
  exact (hd.norm.inv₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy))).smul hd

theorem euclideanMollification_radial_test_tendsto (α : Measure (Space d)) [IsFiniteMeasure α]
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (x : Space d) (hx : ∀ᵐ y ∂α, y ≠ x) (F : BoundedContinuousFunction (Space d) ℝ) :
    Tendsto (fun n => ∫ w, F w ∂(α ∗ euclideanDensityMeasure
      (euclideanMollifier (d := d) (ε n) (hε n))).map (radialDirection x))
      atTop (𝓝 (∫ w, F w ∂α.map (radialDirection x))) := by
  have hm : Measurable (radialDirection x) := by unfold radialDirection; fun_prop
  simp_rw [integral_map hm.aemeasurable F.continuous.aestronglyMeasurable]
  exact euclideanMollification_test_tendsto α hε hlim (fun y => F (radialDirection x y))
    (F.continuous.measurable.comp hm) (fun y => F.norm_coe_le_norm _)
    (hx.mono (fun y hy => F.continuous.continuousAt.comp (continuousAt_radialDirection x y hy)))

end Falconer

end OAI
