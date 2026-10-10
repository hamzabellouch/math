import OAI.MeasureTheory.Falconer.Radial.HyperplaneFourier
import OAI.MeasureTheory.Falconer.Fourier.FourierConvolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

namespace OAI

/-! Normalized compact smooth mollifiers in the source dimension. -/
namespace Falconer
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Convolution
variable {d : ℕ}

noncomputable def euclideanBump (ε : ℝ) (hε : 0 < ε) : ContDiffBump (0 : Space d) where
  rIn := ε/2
  rOut := ε
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

noncomputable def euclideanMollifier (ε : ℝ) (hε : 0 < ε) : Space d → ℝ :=
  (euclideanBump (d := d) ε hε).normed volume

theorem euclideanMollifier_nonneg (ε : ℝ) (hε : 0 < ε) (x : Space d) :
    0 ≤ euclideanMollifier (d := d) ε hε x := (euclideanBump (d := d) ε hε).nonneg_normed x

theorem euclideanMollifier_smooth (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanMollifier (d := d) ε hε) := (euclideanBump (d := d) ε hε).contDiff_normed

theorem euclideanMollifier_compact (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (euclideanMollifier (d := d) ε hε) := (euclideanBump (d := d) ε hε).hasCompactSupport_normed

theorem euclideanMollifier_support (ε : ℝ) (hε : 0 < ε) :
    Function.support (euclideanMollifier (d := d) ε hε) = ball (0 : Space d) ε :=
  (euclideanBump (d := d) ε hε).support_normed_eq

theorem euclideanMollifier_integral (ε : ℝ) (hε : 0 < ε) :
    (∫ x, euclideanMollifier (d := d) ε hε x) = 1 := (euclideanBump (d := d) ε hε).integral_normed

instance euclideanMollifier_probability (ε : ℝ) (hε : 0 < ε) :
    IsProbabilityMeasure (euclideanDensityMeasure (euclideanMollifier (d := d) ε hε)) := by
  constructor
  rw [euclideanDensityMeasure,withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (f := euclideanMollifier (d := d) ε hε)
      ((euclideanBump (d := d) ε hε).integrable_normed (μ := volume))
      (Eventually.of_forall (euclideanMollifier_nonneg ε hε)),euclideanMollifier_integral]
  exact ENNReal.ofReal_one

theorem euclideanMollifier_ae_ball (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ x ∂euclideanDensityMeasure (euclideanMollifier (d := d) ε hε), x ∈ ball (0 : Space d) ε := by
  rw [euclideanDensityMeasure,ae_withDensity_iff
    (euclideanMollifier_smooth ε hε).continuous.measurable.ennreal_ofReal]
  filter_upwards with x hx
  rw [← euclideanMollifier_support ε hε]
  intro hz
  exact hx (by simp [hz])

theorem euclideanMollifier_test_tendsto {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : ∀ i, 0 < ε i) (hlim : Tendsto ε l (𝓝 0))
    (f : Space d → ℝ) (hf : Continuous f) :
    Tendsto (fun i => ∫ x, f x ∂euclideanDensityMeasure (euclideanMollifier (d := d) (ε i) (hε i)))
      l (𝓝 (f 0)) := by
  have h := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := (volume : Measure (Space d))) (φ := fun i => euclideanBump (d := d) (ε i) (hε i))
    hlim (hf.comp continuous_neg) (0 : Space d)
  have he (i : ι) : (∫ x, f x ∂euclideanDensityMeasure (euclideanMollifier (d := d) (ε i) (hε i))) =
      ∫ x, euclideanMollifier (d := d) (ε i) (hε i) x • f x := by
    rw [euclideanDensityMeasure,integral_withDensity_eq_integral_toReal_smul
      (euclideanMollifier_smooth _ _).continuous.measurable.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (euclideanMollifier_nonneg _ _ _)]
  simp_rw [he]
  simpa only [convolution,ContinuousLinearMap.lsmul_apply,zero_sub,Function.comp_apply,
    neg_neg,neg_zero,euclideanMollifier] using h

theorem euclideanMollifier_energy_le (α : Measure (Space d)) [IsFiniteMeasure α]
    (ε : ℝ) (hε : 0 < ε) {s : ℝ} (hs : 0 < s) (hsd : s < d) :
    PlanarFalconer.rieszEnergyOn (α ∗ euclideanDensityMeasure (euclideanMollifier (d := d) ε hε)) s ≤
      PlanarFalconer.rieszEnergyOn α s :=
  PlanarFalconer.rieszEnergyOn_convolution_probability_le α _ hs (by simpa [Space] using hsd)

end Falconer

end OAI
