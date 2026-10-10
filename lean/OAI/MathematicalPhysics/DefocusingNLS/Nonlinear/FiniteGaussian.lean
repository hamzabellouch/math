import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Probability.Distributions.Gaussian.Real

namespace OAI

/-!
# Positivity of finite Gaussian Fourier blocks

A finite list of independent nondegenerate complex Gaussians charges every
nonempty open coefficient set. Multiplication by any nonzero Fourier weights
preserves that property. This is the finite-block ingredient in the Gaussian
support argument for Corollary 1.2 of the stable defocusing NLS manuscript.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DefocusingNLS

/-- A nondegenerate real Gaussian is positive on nonempty open sets. -/
theorem gaussianReal_isOpenPosMeasure (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal m v).IsOpenPosMeasure :=
  (gaussianReal_absolutelyContinuous' m hv).isOpenPosMeasure

/-- Independent centered real and imaginary Gaussian coordinates, each of
variance `v`. The usual standard complex Gaussian takes `v = 1/2`. -/
noncomputable def complexGaussian (v : ℝ≥0) : Measure ℂ :=
  ((gaussianReal 0 v).prod (gaussianReal 0 v)).map
    Complex.equivRealProdCLM.symm

instance complexGaussian_isProbabilityMeasure (v : ℝ≥0) :
    IsProbabilityMeasure (complexGaussian v) := by
  unfold complexGaussian
  infer_instance

/-- Real and imaginary nondegeneracy give full topological support on `ℂ`. -/
theorem complexGaussian_isOpenPosMeasure {v : ℝ≥0} (hv : v ≠ 0) :
    (complexGaussian v).IsOpenPosMeasure := by
  let := gaussianReal_isOpenPosMeasure 0 hv
  exact Complex.equivRealProdCLM.symm.continuous.isOpenPosMeasure_map
    Complex.equivRealProdCLM.symm.surjective

/-- The independent finite Fourier block has full support. -/
theorem finite_complexGaussian_isOpenPosMeasure {ι : Type*} [Fintype ι]
    {v : ℝ≥0} (hv : v ≠ 0) :
    (Measure.pi (fun _ : ι => complexGaussian v)).IsOpenPosMeasure := by
  let := complexGaussian_isOpenPosMeasure hv
  infer_instance

/-- Multiplying each finite Fourier coefficient by a nonzero weight preserves
full support. In particular all polynomial Fourier-decay weights qualify. -/
theorem weighted_finite_complexGaussian_isOpenPosMeasure
    {ι : Type*} [Fintype ι] {v : ℝ≥0} (hv : v ≠ 0)
    (w : ι → ℂ) (hw : ∀ i, w i ≠ 0) :
    ((Measure.pi (fun _ : ι => complexGaussian v)).map
      (fun z : ι → ℂ => fun i => w i * z i)).IsOpenPosMeasure := by
  let := finite_complexGaussian_isOpenPosMeasure (ι := ι) hv
  have hcont : Continuous (fun z : ι → ℂ => fun i => w i * z i) := by
    fun_prop
  apply hcont.isOpenPosMeasure_map
  intro z
  refine ⟨fun i => (w i)⁻¹ * z i, ?_⟩
  funext i
  simp [hw i]

/-- Every prescribed finite coefficient vector can be approximated with
positive probability, including after nonzero Fourier weights are applied. -/
theorem weighted_finite_complexGaussian_ball_pos
    {ι : Type*} [Fintype ι] {v : ℝ≥0} (hv : v ≠ 0)
    (w : ι → ℂ) (hw : ∀ i, w i ≠ 0) (f : ι → ℂ) {r : ℝ} (hr : 0 < r) :
    0 < ((Measure.pi (fun _ : ι => complexGaussian v)).map
      (fun z : ι → ℂ => fun i => w i * z i)) (Metric.ball f r) := by
  let := weighted_finite_complexGaussian_isOpenPosMeasure hv w hw
  exact Metric.isOpen_ball.measure_pos _ (Metric.nonempty_ball.mpr hr)

end DefocusingNLS

end OAI
