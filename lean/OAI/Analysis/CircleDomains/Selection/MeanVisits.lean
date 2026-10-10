import OAI.Analysis.CircleDomains.Selection.VisitCounts
import OAI.Analysis.CircleDomains.Probability.MomentLawBounds
import Mathlib.Probability.Kernel.MeasurableLIntegral

namespace OAI

/-! Actual expected visit counts are jointly measurable and obey the mixture
identity, even when they are infinite. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_meanVisitCount :
    Measurable (fun q : ProbabilityMeasure C(PathTime, X) × X => meanVisitCount q.1 q.2) := by
  let κ : Kernel (ProbabilityMeasure C(PathTime, X) × X) C(PathTime, X) :=
    ⟨fun q => (q.1 : Measure C(PathTime, X)), measurable_subtype_coe.comp measurable_fst⟩
  let : IsMarkovKernel κ := ⟨fun q => q.1.prop⟩
  have hm : Measurable (fun q : (ProbabilityMeasure C(PathTime, X) × X) × C(PathTime, X) =>
      visitCount q.2 q.1.2) :=
    measurable_visitCount.comp (measurable_snd.prodMk measurable_fst.snd)
  exact hm.lintegral_kernel_prod_right' (κ := κ)

theorem meanVisitCount_mixture {Z : Type*} [MeasurableSpace Z]
    (P : ProbabilityMeasure Z) (law : Z → ProbabilityMeasure C(PathTime, X))
    (hlaw : Measurable law) (x : X) :
    meanVisitCount (probabilityMixture P law hlaw) x =
      ∫⁻ z, meanVisitCount (law z) x ∂(P : Measure Z) := by
  exact lintegral_probabilityMixture P law hlaw
    (measurable_visitCount.comp (measurable_id.prodMk measurable_const))

theorem meanVisitCount_finite_ae {Z : Type*} [MeasurableSpace Z]
    (P : ProbabilityMeasure Z) (law : Z → ProbabilityMeasure C(PathTime, X))
    (hlaw : Measurable law) (x : X)
    (h : meanVisitCount (probabilityMixture P law hlaw) x < ∞) :
    ∀ᵐ z ∂(P : Measure Z), meanVisitCount (law z) x < ∞ := by
  rw [meanVisitCount_mixture P law hlaw x] at h
  exact ae_lt_top (measurable_meanVisitCount.comp (hlaw.prodMk measurable_const)) h.ne

end CircleDomainRigidity

end

end OAI
