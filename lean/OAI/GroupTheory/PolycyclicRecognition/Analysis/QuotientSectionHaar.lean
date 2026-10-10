import OAI.GroupTheory.PolycyclicRecognition.Analysis.QuotientSectionMeasure

namespace OAI

/-! # Haar measure in quotient-section coordinates -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory

variable {N Q : Type*} [Group N] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup Q]
  [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [BorelSpace N] [BorelSpace Q]
  (π : N →* Q) (hπ : Continuous π) (s : C(Q, N)) (hs : ∀ q, π (s q) = q)
  (μQ : Measure Q) (μI : Measure π.ker) [SFinite μQ] [SFinite μI]
  [μQ.IsHaarMeasure] [μI.IsHaarMeasure] [μI.IsMulRightInvariant]

/-- The coordinate product is itself Haar: left invariance follows from
the explicit skew action, and the homeomorphism preserves finiteness on
compact sets and positivity on open sets. -/
theorem quotientSection_product_isHaarMeasure
    (hconj : ∀ n : N, MeasurePreserving (quotientKernelConjugate π n) μI μI) :
    (Measure.map (quotientSectionHomeomorph π hπ s hs).symm (μQ.prod μI)).IsHaarMeasure := by
  let e := (quotientSectionHomeomorph π hπ s hs).symm
  exact
    { map_mul_left_eq_self := fun n =>
        (quotientSection_product_left_invariant π hπ s hs μQ μI hconj n).map_eq
      toIsFiniteMeasureOnCompacts := Measure.IsFiniteMeasureOnCompacts.map (μQ.prod μI) e
      toIsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective }

end PolycyclicRecognition

end

end OAI
