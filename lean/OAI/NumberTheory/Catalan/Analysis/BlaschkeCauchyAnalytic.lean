import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import OAI.NumberTheory.Catalan.Estimates.CauchyKernel

namespace OAI

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Topology Interval
namespace InternalCatalan

theorem blaschkeCauchyKernelIntegral_hasDerivAt {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D n : ℕ) (hx : ∀ i ∈ s, x i ≠ 0) {z₀ : ℂ}
    (hz : z₀ ∉ blaschkeCauchySegment n) :
    HasDerivAt
      (fun z : ℂ => ∫ t in -(1 + 2 / (n : ℝ))..(1 + 2 / (n : ℝ)),
        blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z))
      (∫ t in -(1 + 2 / (n : ℝ))..(1 + 2 / (n : ℝ)),
        blaschkeDensity s x D (Complex.I * (t : ℂ)) /
          (Complex.I * (t : ℂ) - z₀) ^ 2) z₀ := by
  let T : ℝ := 1 + 2 / (n : ℝ)
  let μ : Measure ℝ := volume.restrict (Ioc (-T) T)
  let K : ℂ → ℝ → ℂ := fun z t =>
    blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z)
  let K' : ℂ → ℝ → ℂ := fun z t =>
    blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z) ^ 2
  obtain ⟨δ, hδ, hsep⟩ := exists_blaschkeCauchySegment_uniform_separation hz
  let bound : ℝ → ℝ := fun t =>
    ‖blaschkeDensity s x D (Complex.I * (t : ℂ))‖ * (4 / δ ^ 2)
  have hpath : Continuous (fun t : ℝ => Complex.I * (t : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  have hdensity := continuous_blaschkeDensity_imaginary s x D hx
  have hKmeas (z : ℂ) : Measurable (K z) :=
    hdensity.measurable.div (hpath.measurable.sub measurable_const)
  have hK'meas (z : ℂ) : Measurable (K' z) :=
    hdensity.measurable.div ((hpath.measurable.sub measurable_const).pow_const 2)
  have hKint : Integrable (K z₀) μ :=
    (intervalIntegrable_blaschkeCauchyKernel_off_segment s x D n hx hz).1
  have hboundint : Integrable bound μ := by
    have hi : IntervalIntegrable bound volume (-T) T :=
      (hdensity.norm.mul_const (4 / δ ^ 2)).intervalIntegrable _ _
    exact hi.1
  have hae : ∀ᵐ t ∂μ, t ∈ Icc (-T) T := by
    exact (ae_restrict_mem measurableSet_Ioc).mono (fun t ht => ⟨ht.1.le, ht.2⟩)
  have hbound : ∀ᵐ t ∂μ, ∀ z ∈ ball z₀ (δ / 2), ‖K' z t‖ ≤ bound t := by
    apply hae.mono
    intro t ht z hznear
    exact blaschkeCauchyKernel_derivative_norm_le s x D t z hδ (hsep z hznear t ht)
  have hdiff : ∀ᵐ t ∂μ, ∀ z ∈ ball z₀ (δ / 2), HasDerivAt (fun w => K w t) (K' z t) z := by
    apply hae.mono
    intro t ht z hznear
    have hden : Complex.I * (t : ℂ) - z ≠ 0 := by
      apply norm_pos_iff.mp
      exact lt_of_lt_of_le (half_pos hδ) (hsep z hznear t ht)
    exact blaschkeCauchyKernel_hasDerivAt s x D t z hden
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := K) (F' := K') (bound := bound) (x₀ := z₀)
    (s := ball z₀ (δ / 2)) (Metric.ball_mem_nhds z₀ (half_pos hδ))
    (Eventually.of_forall (fun z => (hKmeas z).aestronglyMeasurable)) hKint
    (hK'meas z₀).aestronglyMeasurable hbound hboundint hdiff
  have hT0 : 0 ≤ T := by dsimp only [T]; positivity
  have hT : -T ≤ T := by linarith
  simpa only [intervalIntegral.integral_of_le hT, K, K', μ, T] using hmain.2

theorem blaschkeCauchyTransform_hasDerivAt {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D n : ℕ) (hx : ∀ i ∈ s, x i ≠ 0) {z : ℂ}
    (hz : z ∉ blaschkeCauchySegment n) :
    HasDerivAt (blaschkeCauchyTransform s x D n)
      (((3 / Real.pi : ℝ) : ℂ) *
        ∫ t in -(1 + 2 / (n : ℝ))..(1 + 2 / (n : ℝ)),
          blaschkeDensity s x D (Complex.I * (t : ℂ)) /
            (Complex.I * (t : ℂ) - z) ^ 2) z := by
  have hfun : blaschkeCauchyTransform s x D n =
      fun w : ℂ => ((3 / Real.pi : ℝ) : ℂ) *
        ∫ t in -(1 + 2 / (n : ℝ))..(1 + 2 / (n : ℝ)),
          blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - w) := by
    funext w
    exact blaschkeCauchyTransform_normalized s x D n w
  rw [hfun]
  exact (blaschkeCauchyKernelIntegral_hasDerivAt s x D n hx hz).const_mul
    (((3 / Real.pi : ℝ) : ℂ))

theorem blaschkeCauchyTransform_analyticOnNhd {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D n : ℕ) (hx : ∀ i ∈ s, x i ≠ 0) :
    AnalyticOnNhd ℂ (blaschkeCauchyTransform s x D n) (blaschkeCauchySegment n)ᶜ := by
  have hd : DifferentiableOn ℂ (blaschkeCauchyTransform s x D n)
      (blaschkeCauchySegment n)ᶜ := by
    intro z hz
    exact (blaschkeCauchyTransform_hasDerivAt s x D n hx hz).differentiableAt.differentiableWithinAt
  exact hd.analyticOnNhd (isCompact_blaschkeCauchySegment n).isClosed.isOpen_compl

theorem blaschkeCauchyTransform_analyticAt {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D n : ℕ) (hx : ∀ i ∈ s, x i ≠ 0) {z : ℂ}
    (hz : z ∉ blaschkeCauchySegment n) :
    AnalyticAt ℂ (blaschkeCauchyTransform s x D n) z :=
  blaschkeCauchyTransform_analyticOnNhd s x D n hx z hz

end InternalCatalan

end

end OAI
