import OAI.GroupTheory.PolycyclicRecognition.Analysis.QuotientSectionHaar

namespace OAI

/-! # The product Haar normalization is independent of the section -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory

variable {N Q : Type*} [Group N] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup Q]
  [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [BorelSpace N] [BorelSpace Q]

omit [IsTopologicalGroup Q] in
/-- Changing the continuous quotient section translates each kernel fiber
on the right. Thus one product normalization serves every adapted basis. -/
theorem quotientSection_product_independent
    (π : N →* Q) (hπ : Continuous π)
    (s t : C(Q, N)) (hs : ∀ q, π (s q) = q) (ht : ∀ q, π (t q) = q)
    (μQ : Measure Q) (μI : Measure π.ker) [SFinite μQ] [SFinite μI]
    [μI.IsMulRightInvariant] :
    Measure.map (quotientSectionHomeomorph π hπ s hs).symm (μQ.prod μI) =
      Measure.map (quotientSectionHomeomorph π hπ t ht).symm (μQ.prod μI) := by
  let c : Q → π.ker := fun q => quotientSectionResidual π t ht (s q)
  have hc : Continuous c := by
    exact ((s.continuous.mul (t.continuous.comp (hπ.comp s.continuous)).inv)).subtype_mk _
  let changeSection := fun p : Q × π.ker => (p.1, p.2 * c p.1)
  have hchange : MeasurePreserving changeSection (μQ.prod μI) (μQ.prod μI) := by
    apply (MeasurePreserving.id μQ).skew_product (g := fun q i => i * c q)
    · exact (continuous_snd.mul (hc.comp continuous_fst)).measurable
    · exact Filter.Eventually.of_forall (fun q => map_mul_right_eq_self μI (c q))
  have he : (quotientSectionHomeomorph π hπ s hs).symm =
      (quotientSectionHomeomorph π hπ t ht).symm ∘ changeSection := by
    funext p
    change (p.2 : N) * s p.1 = ((p.2 : N) * (s p.1 * (t (π (s p.1)))⁻¹)) * t p.1
    rw [hs, mul_assoc, inv_mul_cancel_right]
  rw [he, ← Measure.map_map (quotientSectionHomeomorph π hπ t ht).symm.measurable
    hchange.measurable, hchange.map_eq]

end PolycyclicRecognition

end

end OAI
