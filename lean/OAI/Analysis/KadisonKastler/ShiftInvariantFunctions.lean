import OAI.Analysis.KadisonKastler.ShiftInvariantSigma
import OAI.Analysis.KadisonKastler.ScalarPullbackAlgebra
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable

namespace OAI

/-! # Scalar functions on the invariant sigma algebra

The invariant measurable structure has exactly the essentially bounded
scalar functions fixed by the shift. The countable rational cuts below
turn invariance of measurable sets into simultaneous pointwise equality.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {S : X → X}

theorem real_fixed_of_measurable_shiftInvariantSigma {f : X → ℝ}
    (hf : Measurable[shiftInvariantSigma μ S] f) :
    ∀ᵐ x ∂μ, f (S x) = f x := by
  have hc (q : ℚ) : ∀ᵐ x ∂μ, f (S x) < (q : ℝ) ↔ f x < (q : ℝ) :=
    (hf (measurableSet_Iio (a := (q : ℝ)))).2
  filter_upwards [ae_all_iff.mpr hc] with x hx
  apply le_antisymm
  · by_contra! h
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn h
    exact (not_lt_of_ge hq₂.le) ((hx q).mpr hq₁)
  · by_contra! h
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn h
    exact (not_lt_of_ge hq₂.le) ((hx q).mp hq₁)

theorem complex_fixed_of_measurable_shiftInvariantSigma {f : X → ℂ}
    (hf : Measurable[shiftInvariantSigma μ S] f) :
    ∀ᵐ x ∂μ, f (S x) = f x := by
  have hr := real_fixed_of_measurable_shiftInvariantSigma (Complex.measurable_re.comp hf)
  have hi := real_fixed_of_measurable_shiftInvariantSigma (Complex.measurable_im.comp hf)
  filter_upwards [hr, hi] with x hx hy
  exact Complex.ext hx hy

theorem scalarInfinity_fixed_iff_measurable_shiftInvariantSigma
    (hS : Measure.QuasiMeasurePreserving S μ μ) (f : ScalarLInfinity μ) :
    scalarInfinityPullback S hS f = f ↔ Measurable[shiftInvariantSigma μ S] f := by
  constructor
  · intro he
    apply measurable_shiftInvariantSigma_of_fixed μ S (Lp.stronglyMeasurable f).measurable
    have ha := scalarInfinityPullback_ae S hS f
    rw [he] at ha
    exact ha.symm
  · intro hf
    apply Lp.ext
    exact (scalarInfinityPullback_ae S hS f).trans
      (complex_fixed_of_measurable_shiftInvariantSigma hf)

theorem scalarInfinity_fixed_mem_lpMeas
    (hS : Measure.QuasiMeasurePreserving S μ μ) (f : ScalarLInfinity μ)
    (hf : scalarInfinityPullback S hS f = f) :
    f ∈ lpMeas ℂ ℂ (shiftInvariantSigma μ S) ⊤ μ := by
  rw [mem_lpMeas_iff_aestronglyMeasurable]
  exact ((scalarInfinity_fixed_iff_measurable_shiftInvariantSigma hS f).mp hf).stronglyMeasurable.aestronglyMeasurable

theorem scalarInfinity_fixed_of_aestronglyMeasurable
    (hS : Measure.QuasiMeasurePreserving S μ μ) (f : ScalarLInfinity μ)
    (hf : AEStronglyMeasurable[shiftInvariantSigma μ S] f μ) :
    scalarInfinityPullback S hS f = f := by
  have hm := complex_fixed_of_measurable_shiftInvariantSigma hf.stronglyMeasurable_mk.measurable
  apply Lp.ext
  filter_upwards [scalarInfinityPullback_ae S hS f, hf.ae_eq_mk,
    hS.ae hf.ae_eq_mk, hm] with x hp hx hs hmk
  exact hp.trans (hs.trans (hmk.trans hx.symm))

/-- Descending a fixed scalar class changes neither its values nor its norm. -/
def fixedScalarToInvariant (hS : Measure.QuasiMeasurePreserving S μ μ)
    (f : ScalarLInfinity μ) (hf : scalarInfinityPullback S hS f = f) :
    @Lp X ℂ (shiftInvariantSigma μ S) _ ⊤ (shiftInvariantMeasure μ S) :=
  lpMeasToLpTrim ℂ ℂ ⊤ μ (shiftInvariantSigma_le μ S)
    ⟨f, scalarInfinity_fixed_mem_lpMeas hS f hf⟩

theorem fixedScalarToInvariant_ae (hS : Measure.QuasiMeasurePreserving S μ μ)
    (f : ScalarLInfinity μ) (hf : scalarInfinityPullback S hS f = f) :
    fixedScalarToInvariant hS f hf =ᵐ[μ] f :=
  lpMeasToLpTrim_ae_eq (shiftInvariantSigma_le μ S) _

theorem fixedScalarToInvariant_norm (hS : Measure.QuasiMeasurePreserving S μ μ)
    (f : ScalarLInfinity μ) (hf : scalarInfinityPullback S hS f = f) :
    ‖fixedScalarToInvariant hS f hf‖ = ‖f‖ :=
  lpMeasSubgroupToLpTrim_norm_map (shiftInvariantSigma_le μ S)
    ⟨f, scalarInfinity_fixed_mem_lpMeas hS f hf⟩

end

end KadisonKastler

end OAI
