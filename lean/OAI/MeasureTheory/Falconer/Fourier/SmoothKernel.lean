import OAI.MeasureTheory.Falconer.Graphs.FiberSlice
import OAI.MeasureTheory.Falconer.Fourier.FourierConvolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Convolution

noncomputable def sourceBump (ε : ℝ) (hε : 0 < ε) : ContDiffBump (0 : Plane) where
  rIn := ε/2
  rOut := ε
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

noncomputable def sourceMollifier (ε : ℝ) (hε : 0 < ε) : Plane → ℝ :=
  (sourceBump ε hε).normed volume

theorem sourceMollifier_nonneg (ε : ℝ) (hε : 0 < ε) (x : Plane) :
    0 ≤ sourceMollifier ε hε x := (sourceBump ε hε).nonneg_normed x

theorem sourceMollifier_smooth (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (sourceMollifier ε hε) := (sourceBump ε hε).contDiff_normed

theorem sourceMollifier_compact (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (sourceMollifier ε hε) := (sourceBump ε hε).hasCompactSupport_normed

theorem sourceMollifier_support (ε : ℝ) (hε : 0 < ε) :
    Function.support (sourceMollifier ε hε) = ball (0 : Plane) ε :=
  (sourceBump ε hε).support_normed_eq

theorem sourceMollifier_integral (ε : ℝ) (hε : 0 < ε) :
    (∫ x, sourceMollifier ε hε x) = 1 := (sourceBump ε hε).integral_normed

instance sourceMollifier_probability (ε : ℝ) (hε : 0 < ε) :
    IsProbabilityMeasure (sourceDensityMeasure (sourceMollifier ε hε)) := by
  constructor
  rw [sourceDensityMeasure,withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (f := sourceMollifier ε hε)
      ((sourceBump ε hε).integrable_normed (μ := volume))
      (Eventually.of_forall (sourceMollifier_nonneg ε hε)),sourceMollifier_integral]
  exact ENNReal.ofReal_one

theorem sourceMollifier_ae_ball (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ x ∂sourceDensityMeasure (sourceMollifier ε hε), x ∈ ball (0 : Plane) ε := by
  rw [sourceDensityMeasure,ae_withDensity_iff
    (sourceMollifier_smooth ε hε).continuous.measurable.ennreal_ofReal]
  filter_upwards with x hx
  rw [← sourceMollifier_support ε hε]
  intro hz
  exact hx (by simp [hz])

theorem sourceMollifier_test_tendsto {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : ∀ i, 0 < ε i) (hlim : Tendsto ε l (𝓝 0))
    (f : Plane → ℝ) (hf : Continuous f) :
    Tendsto (fun i => ∫ x, f x ∂sourceDensityMeasure (sourceMollifier (ε i) (hε i)))
      l (𝓝 (f 0)) := by
  have h := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := (volume : Measure Plane)) (φ := fun i => sourceBump (ε i) (hε i))
    hlim (hf.comp continuous_neg) (0 : Plane)
  have he (i : ι) : (∫ x, f x ∂sourceDensityMeasure (sourceMollifier (ε i) (hε i))) =
      ∫ x, sourceMollifier (ε i) (hε i) x • f x := by
    rw [sourceDensityMeasure,integral_withDensity_eq_integral_toReal_smul
      (sourceMollifier_smooth _ _).continuous.measurable.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (sourceMollifier_nonneg _ _ _)]
  simp_rw [he]
  simpa only [convolution,ContinuousLinearMap.lsmul_apply,zero_sub,Function.comp_apply,
    neg_neg,neg_zero,sourceMollifier] using h

theorem sourceMollifier_energy_le (α : Measure Plane) [IsFiniteMeasure α]
    (ε : ℝ) (hε : 0 < ε) {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    rieszEnergy (α ∗ sourceDensityMeasure (sourceMollifier ε hε)) s ≤ rieszEnergy α s :=
  rieszEnergy_convolution_probability_le α _ hs hs2

end PlanarFalconer

end OAI
