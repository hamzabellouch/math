import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Restrict

namespace OAI

/-! # Lifting an ambient coupling to the prescribed measurable supports -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] {S T : Set X}

theorem coupling_lift_subtypes (hS : MeasurableSet S) (hT : MeasurableSet T)
    (μ : Measure S) (ν : Measure T) (π : Measure (X × X))
    (hl : π.map Prod.fst=μ.map Subtype.val) (hr : π.map Prod.snd=ν.map Subtype.val) :
    ∃ Q : Measure (S × T), Q.map (Prod.map Subtype.val Subtype.val)=π ∧
      Q.map Prod.fst=μ ∧ Q.map Prod.snd=ν := by
  let inc : S × T → X × X := Prod.map Subtype.val Subtype.val
  have he : MeasurableEmbedding inc :=
    (MeasurableEmbedding.subtype_coe hS).prodMap (MeasurableEmbedding.subtype_coe hT)
  have ha : ∀ᵐ z ∂π, z.1 ∈ S := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [hl]
    exact (MeasurableEmbedding.subtype_coe hS).ae_map_iff.mpr
      (Eventually.of_forall fun x => x.property)
  have hb : ∀ᵐ z ∂π, z.2 ∈ T := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    rw [hr]
    exact (MeasurableEmbedding.subtype_coe hT).ae_map_iff.mpr
      (Eventually.of_forall fun x => x.property)
  have hm : (π.comap inc).map inc=π := by
    rw [he.map_comap]
    apply Measure.restrict_eq_self_of_ae_mem
    filter_upwards [ha,hb] with z hz ht
    exact ⟨(⟨z.1,hz⟩,⟨z.2,ht⟩),rfl⟩
  refine ⟨π.comap inc,hm,?_,?_⟩
  · apply (MeasurableEmbedding.subtype_coe hS).map_injective
    calc
      ((π.comap inc).map Prod.fst).map Subtype.val = ((π.comap inc).map inc).map Prod.fst := by
        rw [Measure.map_map measurable_subtype_coe measurable_fst,
          Measure.map_map measurable_fst he.measurable]
        rfl
      _ = π.map Prod.fst := congrArg (fun m : Measure (X × X) => m.map Prod.fst) hm
      _ = μ.map Subtype.val := hl
  · apply (MeasurableEmbedding.subtype_coe hT).map_injective
    calc
      ((π.comap inc).map Prod.snd).map Subtype.val = ((π.comap inc).map inc).map Prod.snd := by
        rw [Measure.map_map measurable_subtype_coe measurable_snd,
          Measure.map_map measurable_snd he.measurable]
        rfl
      _ = π.map Prod.snd := congrArg (fun m : Measure (X × X) => m.map Prod.snd) hm
      _ = ν.map Subtype.val := hr

end RegularPointCoordinates

end

end OAI
