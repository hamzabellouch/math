import OAI.Analysis.CircleDomains.Sobolev.SmoothCurveImage
import OAI.Analysis.CircleDomains.Modulus.HausdorffPayment

namespace OAI

/-! Passing the smooth image estimate to a Sobolev approximation on a
finite-length level. The conclusion holds on every measurable connected
subset simultaneously; no exceptional set of arcs is introduced. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem connected_level_oscillation_of_approximation
    {K : Set ℂ} (hKfin : (μH[1] : Measure ℂ) K < ∞)
    (u : ℕ → ℂ → ℝ) (hu : ∀ n, ContDiff ℝ 1 (u n)) {v : ℂ → ℝ}
    (hv : ∀ z ∈ K, Tendsto (fun n => u n z) atTop (𝓝 (v z)))
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (e : ℕ → ℂ → ℝ≥0∞)
    (hgrad : ∀ n, ∀ᵐ z ∂(μH[1] : Measure ℂ).restrict K,
      ENNReal.ofReal ‖fderiv ℝ (u n) z‖ ≤ g z+e n z)
    (herror : Tendsto (fun n => ∫⁻ z in K, e n z ∂(μH[1] : Measure ℂ)) atTop (𝓝 0))
    {O : Set ℂ} (hO : MeasurableSet O) (hOK : O ⊆ K) (hconn : IsPreconnected O)
    {x y : ℂ} (hx : x ∈ O) (hy : y ∈ O) :
    ENNReal.ofReal |v x-v y| ≤ ∫⁻ z in O, g z ∂(μH[1] : Measure ℂ) := by
  have hpay (n : ℕ) : ENNReal.ofReal |u n x-u n y| ≤
      (∫⁻ z in O, g z ∂(μH[1] : Measure ℂ))+
        ∫⁻ z in K, e n z ∂(μH[1] : Measure ℂ) := by
    have hi := dist_le_hausdorffMeasure_one_of_preconnected
      (hconn.image (u n) (hu n).continuous.continuousOn)
      (mem_image_of_mem (u n) hy) (mem_image_of_mem (u n) hx)
    rw [hausdorffMeasure_real, Real.dist_eq] at hi
    calc
      _ ≤ volume (u n '' O) := hi
      _ ≤ ∫⁻ z in O, ENNReal.ofReal ‖fderiv ℝ (u n) z‖ ∂(μH[1] : Measure ℂ) :=
        smooth_curve_image_bound isOpen_univ hO (subset_univ _)
          ((measure_mono hOK).trans_lt hKfin) (hu n).contDiffOn
      _ ≤ ∫⁻ z in O, g z+e n z ∂(μH[1] : Measure ℂ) := by
        apply lintegral_mono_ae
        exact (hgrad n).filter_mono (ae_mono (Measure.restrict_mono hOK le_rfl))
      _ = (∫⁻ z in O, g z ∂(μH[1] : Measure ℂ))+
          ∫⁻ z in O, e n z ∂(μH[1] : Measure ℂ) := lintegral_add_left hg _
      _ ≤ _ := add_le_add le_rfl (lintegral_mono_set (μ := (μH[1] : Measure ℂ)) (f := e n) hOK)
  have hl := ENNReal.tendsto_ofReal (((hv x (hOK hx)).sub (hv y (hOK hy))).abs)
  have hr := (tendsto_const_nhds (x := ∫⁻ z in O, g z ∂(μH[1] : Measure ℂ))).add herror
  simpa only [add_zero] using
    le_of_tendsto_of_tendsto hl hr (Eventually.of_forall hpay)

end CircleDomainRigidity

end

end OAI
