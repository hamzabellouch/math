import OAI.NumberTheory.DukePrimeDegree.Geometry.IndependentNestedKernel
import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalRectangleProducts

namespace OAI

/-! # The real marginal after restricting an independent physical window -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
variable {S B : Type*} [MeasurableSpace S] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B]

theorem independent_restrict_real_marginal
    (σ : Measure (S × (B × ℝ))) [IsFiniteMeasure σ] (J : Set ℝ) (hJ : MeasurableSet J) :
    let ρ := σ.restrict (univ ×ˢ (univ ×ˢ J))
    (∀ᵐ s ∂ρ.fst, ρ.condKernel s = (ρ.condKernel s).fst.prod (ρ.condKernel s).snd) →
    ∀ᵐ z ∂ρ,
      (σ.map MeasurableEquiv.prodAssoc.symm).condKernel (z.1,z.2.1) J ≠ 0 ∧
      (ρ.condKernel z.1).snd =
        (anchorNormalize ((σ.map MeasurableEquiv.prodAssoc.symm).condKernel (z.1,z.2.1)) J).restrict J := by
  intro ρ hp
  have he : ρ.map MeasurableEquiv.prodAssoc.symm =
      (σ.map MeasurableEquiv.prodAssoc.symm).restrict (univ ×ˢ J) := by
    rw [Measure.restrict_map MeasurableEquiv.prodAssoc.symm.measurable (MeasurableSet.univ.prod hJ)]
    have hs : MeasurableEquiv.prodAssoc.symm ⁻¹' (univ ×ˢ J : Set ((S × B) × ℝ)) =
        univ ×ˢ (univ ×ˢ J) := by
      ext z
      simp only [mem_preimage,mem_prod,mem_univ,true_and]
      rfl
    rw [hs]
  have H := conditional_restrict_normalized (σ.map MeasurableEquiv.prodAssoc.symm)
    (univ ×ˢ J) (MeasurableSet.univ.prod hJ)
  have H' : ∀ᵐ a ∂(ρ.map MeasurableEquiv.prodAssoc.symm).fst,
      (σ.map MeasurableEquiv.prodAssoc.symm).condKernel a J ≠ 0 ∧
      (ρ.map MeasurableEquiv.prodAssoc.symm).condKernel a =
        (anchorNormalize ((σ.map MeasurableEquiv.prodAssoc.symm).condKernel a) J).restrict J := by
    have hfiber (a : S × B) : Prod.mk a ⁻¹' (univ ×ˢ J : Set ((S × B) × ℝ)) = J := by
      ext t
      simp only [mem_preimage,mem_prod,mem_univ,true_and]
    simpa only [hfiber,←he] using H
  have hs := ae_of_ae_map measurable_fst.aemeasurable H'
  have hz := ae_of_ae_map MeasurableEquiv.prodAssoc.symm.measurable.aemeasurable hs
  filter_upwards [hz,independent_nested_kernel_at_sample ρ hp] with z hz hn
  exact ⟨hz.1,hn.symm.trans hz.2⟩

end DukePrimeDegree

end

end OAI
