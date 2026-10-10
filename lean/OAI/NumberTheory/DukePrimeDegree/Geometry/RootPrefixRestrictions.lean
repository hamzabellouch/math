import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixBoxes

namespace OAI

/-! # Ambient restrictions and null sets in the remaining-root quotient boxes -/

noncomputable section
open Matrix MeasureTheory Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    {C : RootPrefixCoordinates n P T} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hfinal : c.finalEntries = allPositiveRoots n} {g : G n}

theorem map_restricted_coordinates (B : RootPrefixBox C c hP hfinal g)
    (μ : Measure (X n)) (S : Set ((UpperRootTransverse n × T) × c.Time))
    (hS : MeasurableSet S) (hSB : S ⊆ B.domain) :
    ((B.coordinateMeasure μ).restrict S).map (C.timeParam c hP hfinal g) =
      μ.restrict (C.timeParam c hP hfinal g '' S) := by
  let V : Set B.domain := Subtype.val ⁻¹' S
  have hV : MeasurableSet V := measurable_subtype_coe hS
  have hv : MeasurableEmbedding (Subtype.val : B.domain → (UpperRootTransverse n × T) × c.Time) :=
    MeasurableEmbedding.subtype_coe (B.transverse_open.prod B.time_open).measurableSet
  have he := B.embedding.measurableEmbedding
  have hm := he.restrict_map (μ.comap B.param) (B.param '' V)
  rw [he.injective.preimage_image] at hm
  have hset : B.param '' V = C.timeParam c hP hfinal g '' S := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z.val,hz,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨⟨z,hSB hz⟩,hz,rfl⟩
  have hsub : B.param '' V ⊆ B.range := image_subset_range _ _
  rw [he.map_comap,Measure.restrict_restrict (he.measurableSet_image.mpr hV)] at hm
  change μ.restrict ((B.param '' V) ∩ B.range) = ((μ.comap B.param).restrict V).map B.param at hm
  rw [inter_eq_left.mpr hsub] at hm
  rw [coordinateMeasure,hv.restrict_map,Measure.map_map]
  · change ((μ.comap B.param).restrict V).map B.param = _
    exact hm.symm.trans (congrArg (fun A => μ.restrict A) hset)
  · exact (C.timeParam_localHomeomorph c hP hfinal g).continuous.measurable
  · exact measurable_subtype_coe

theorem ae_coordinate_of_ambient (B : RootPrefixBox C c hP hfinal g)
    (μ : Measure (X n)) {Q : X n → Prop} (hQ : ∀ᵐ x ∂μ, Q x) :
    ∀ᵐ z ∂B.coordinateMeasure μ, Q (C.timeParam c hP hfinal g z) := by
  have h := (Measure.absolutelyContinuous_of_le (Measure.restrict_le_self :
    μ.restrict B.range ≤ μ)).ae_le hQ
  rw [←B.map_coordinateMeasure μ] at h
  exact ae_of_ae_map (C.timeParam_localHomeomorph c hP hfinal g).continuous.measurable.aemeasurable h

end RootPrefixBox
end DukePrimeDegree

end

end OAI
