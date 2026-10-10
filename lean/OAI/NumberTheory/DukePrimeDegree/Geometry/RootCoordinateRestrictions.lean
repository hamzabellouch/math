import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalRectangleProducts

namespace OAI

/-! # Ambient restrictions represented by root-coordinate rectangles -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

namespace RootBox
variable {n : ℕ} {a b k : Fin n} {hab : a ≠ b}

theorem map_restricted_coordinates (A : RootBox hab k) (μ : Measure (X n))
    (S : Set (RootSlice a b k × ℝ)) (hS : MeasurableSet S) (hSA : S ⊆ A.domain) :
    ((A.coordinateMeasure μ).restrict S).map (rootQuotientParametrization hab) =
      μ.restrict (rootQuotientParametrization hab '' S) := by
  let T : Set A.domain := Subtype.val ⁻¹' S
  have hT : MeasurableSet T := measurable_subtype_coe hS
  have hv : MeasurableEmbedding (Subtype.val : A.domain → RootSlice a b k × ℝ) :=
    MeasurableEmbedding.subtype_coe (A.transverse_open.prod A.time_open).measurableSet
  have he := A.embedding.measurableEmbedding
  have hmap := he.restrict_map (μ.comap A.param) (A.param '' T)
  rw [he.injective.preimage_image] at hmap
  have hset : A.param '' T = rootQuotientParametrization hab '' S := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z.val,hz,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨⟨z,hSA hz⟩,hz,rfl⟩
  have hsub : A.param '' T ⊆ A.range := image_subset_range _ _
  rw [he.map_comap,Measure.restrict_restrict (he.measurableSet_image.mpr hT)] at hmap
  change μ.restrict ((A.param '' T) ∩ A.range) = ((μ.comap A.param).restrict T).map A.param at hmap
  rw [inter_eq_left.mpr hsub] at hmap
  rw [PrimeDegreePackets.RootBox.coordinateMeasure,hv.restrict_map,Measure.map_map]
  · change ((μ.comap A.param).restrict T).map A.param = _
    exact hmap.symm.trans (congrArg (fun V => μ.restrict V) hset)
  · exact (rootQuotientParametrization_localHomeomorph hab).continuous.measurable
  · exact measurable_subtype_coe

end RootBox

end DukePrimeDegree

end

end OAI
