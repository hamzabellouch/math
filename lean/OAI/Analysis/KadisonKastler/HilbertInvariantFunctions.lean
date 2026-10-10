import OAI.Analysis.KadisonKastler.ProductInvariantL2
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

namespace OAI

/-! # Hilbert-valued functions on an invariant sigma algebra

Scalar matrix coefficients and separability turn measurable invariance into
simultaneous almost-everywhere equality of the Hilbert-valued functions.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X K : Type*} [MeasurableSpace X] {μ : Measure X} {S : X → X}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [TopologicalSpace.SeparableSpace K]
  [MeasurableSpace K] [BorelSpace K]

theorem hilbert_fixed_of_measurable_shiftInvariantSigma {f : X → K}
    (hf : Measurable[shiftInvariantSigma μ S] f) :
    ∀ᵐ x ∂μ, f (S x) = f x := by
  have hc (c : K) : (fun x => inner ℂ c (f (S x) - f x)) =ᵐ[μ] 0 := by
    have hm : Measurable[shiftInvariantSigma μ S] (fun x => inner ℂ c (f x)) :=
      (continuous_const.inner continuous_id).measurable.comp hf
    filter_upwards [complex_fixed_of_measurable_shiftInvariantSigma hm] with x hx
    simp only [inner_sub_right, hx, sub_self, Pi.zero_apply]
  have hz := ae_eq_zero_of_forall_inner hc
  filter_upwards [hz] with x hx
  exact sub_eq_zero.mp hx

omit [MeasurableSpace K] [BorelSpace K] in
theorem hilbert_fixed_of_aestronglyMeasurable_shiftInvariantSigma
    (hS : Measure.QuasiMeasurePreserving S μ μ) {f : X → K}
    (hf : AEStronglyMeasurable[shiftInvariantSigma μ S] f μ) :
    ∀ᵐ x ∂μ, f (S x) = f x := by
  borelize K
  have hm := hilbert_fixed_of_measurable_shiftInvariantSigma hf.stronglyMeasurable_mk.measurable
  filter_upwards [hf.ae_eq_mk, hS.ae hf.ae_eq_mk, hm] with x hx hs hm
  exact hs.trans (hm.trans hx.symm)

variable {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
  [IsFiniteMeasure μ] [IsFiniteMeasure ν]

omit [MeasurableSpace K] [BorelSpace K] in
theorem firstInvariantSigma_fixed_hilbert (hS : Measure.QuasiMeasurePreserving S μ μ)
    {f : X × Y → K} (hf : AEStronglyMeasurable[firstInvariantSigma μ S] f (μ.prod ν)) :
    ∀ᵐ z ∂μ.prod ν, f (S z.1, z.2) = f z :=
  hilbert_fixed_of_aestronglyMeasurable_shiftInvariantSigma (firstCoordinateShift_quasi hS)
    (hf.mono (firstInvariantSigma_le_shiftInvariantSigma (ν := ν)))

end

end KadisonKastler

end OAI
