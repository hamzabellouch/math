import OAI.Analysis.CircleDomains.Probability.CompactMeasureMajorants
import OAI.Analysis.CircleDomains.Probability.CompactFiniteMeasureMeasurability
import Mathlib.MeasureTheory.Measure.GiryMonad

namespace OAI

/-! The actual barycenter measure of a law on a compact family.
Both its finite mass and its nonnegative continuous test integrals follow
from the measurable measure-valued inclusion, not an assumed identity. -/
open Set Filter MeasureTheory
open scoped BoundedContinuousFunction ENNReal
noncomputable section
namespace CircleDomainRigidity

variable {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    {S : Set (FiniteMeasure Z)}

def compactMeasureBarycenter (P : ProbabilityMeasure S) : Measure Z :=
  (P : Measure S).bind (fun v => (v.val : Measure Z))

omit [TopologicalSpace Z] [BorelSpace Z] in
lemma measurable_compactMeasure_inclusion :
    Measurable (fun v : S => (v.val : Measure Z)) :=
  measurable_subtype_coe.comp measurable_subtype_coe

omit [TopologicalSpace Z] [BorelSpace Z] in
lemma compactMeasureBarycenter_apply (P : ProbabilityMeasure S)
    {E : Set Z} (hE : MeasurableSet E) :
    compactMeasureBarycenter P E = ∫⁻ v : S, (v.val : Measure Z) E ∂(P : Measure S) :=
  Measure.bind_apply hE measurable_compactMeasure_inclusion.aemeasurable

lemma compactMeasureBarycenter_finite (hS : IsCompact S) (P : ProbabilityMeasure S) :
    IsFiniteMeasure (compactMeasureBarycenter P) := by
  obtain ⟨C,hC⟩ := (hS.image FiniteMeasure.continuous_mass).bddAbove
  have hb : compactMeasureBarycenter P univ ≤ (C : ℝ≥0∞) := by
    rw [compactMeasureBarycenter_apply P MeasurableSet.univ]
    calc
      (∫⁻ v : S, (v.val : Measure Z) univ ∂(P : Measure S)) ≤
          ∫⁻ _v : S, (C : ℝ≥0∞) ∂(P : Measure S) := by
        apply lintegral_mono
        intro v
        change (v.val : Measure Z) univ ≤ (C : ℝ≥0∞)
        rw [← FiniteMeasure.ennreal_mass]
        exact_mod_cast hC (mem_image_of_mem FiniteMeasure.mass v.property)
      _ = C := by simp
  exact ⟨hb.trans_lt ENNReal.coe_lt_top⟩

omit [TopologicalSpace Z] [BorelSpace Z] in
lemma compactMeasureBarycenter_lintegral (P : ProbabilityMeasure S)
    {f : Z → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f z ∂compactMeasureBarycenter P) =
      ∫⁻ v : S, (∫⁻ z, f z ∂(v.val : Measure Z)) ∂(P : Measure S) :=
  Measure.lintegral_bind measurable_compactMeasure_inclusion.aemeasurable hf.aemeasurable

lemma compactMeasureBarycenter_integral_nonneg [CompactSpace S]
    (P : ProbabilityMeasure S) (f : Z →ᵇ ℝ) (hf : ∀ z, 0 ≤ f z) :
    (∫ z, f z ∂compactMeasureBarycenter P) =
      ∫ v : S, (∫ z, f z ∂(v.val : Measure Z)) ∂(P : Measure S) := by
  have hi (v : S) : 0 ≤ ∫ z, f z ∂(v.val : Measure Z) := integral_nonneg hf
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf)
      f.continuous.measurable.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hi)
      ((measurable_finiteMeasure_integral f).comp measurable_subtype_coe).aestronglyMeasurable]
  apply congrArg ENNReal.toReal
  rw [compactMeasureBarycenter_lintegral P f.continuous.measurable.ennreal_ofReal]
  apply lintegral_congr_ae
  exact Eventually.of_forall fun v =>
    (ofReal_integral_eq_lintegral_ofReal (f.integrable (μ := (v.val : Measure Z))) (Eventually.of_forall hf)).symm

end CircleDomainRigidity

end

end OAI
