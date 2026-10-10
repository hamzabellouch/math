import OAI.Analysis.KadisonKastler.FaithfulTensorFaithfulness
import OAI.Analysis.KadisonKastler.NormalRepresentationRange

namespace OAI

/-! # The tensor isomorphism for the explicit faithful cyclic representation

Only this representation change is needed by fixed-factor preparation.
The range is identified with the spatial product by its two generating
legs and bounded weak continuity, without an arbitrary-isomorphism input.
-/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [Nontrivial H] in
theorem faithfulTensorHom_boundedWeakNormal (M : VonNeumannAlgebra H)
    (D : VonNeumannAlgebra K) :
    BoundedWeakNormal (spatialProductAlgebra M D) (faithfulTensorHom M D) := by
  intro ι l a b C hn hw x y
  exact faithfulTensorHom_tendsto_weak M D a b C hn hw x y

omit [Nontrivial H] in
private theorem faithfulTensorHom_generators_map_le
    (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K) :
    (M.toStarSubalgebra.map (spatialLeft (H := H) (K := K))) ⊔
      (D.toStarSubalgebra.map (spatialRight (H := H) (K := K))) ≤
    ((spatialProductAlgebra (faithfulCyclicAlgebra M) D).toStarSubalgebra.comap
      (faithfulTensorHom M D)).map (spatialProductAlgebra M D).toStarSubalgebra.subtype := by
  let P := spatialProductAlgebra M D
  let N := spatialProductAlgebra (faithfulCyclicAlgebra M) D
  let B : StarSubalgebra ℂ (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
    (M.toStarSubalgebra.map (spatialLeft (H := H) (K := K))) ⊔
    (D.toStarSubalgebra.map (spatialRight (H := H) (K := K)))
  let S := N.toStarSubalgebra.comap (faithfulTensorHom M D)
  change B ≤ S.map P.toStarSubalgebra.subtype
  apply sup_le
  · rintro _ ⟨m, hm, rfl⟩
    refine ⟨⟨spatialLeft m, spatialLeft_mem_product M D hm⟩, ?_, rfl⟩
    change faithfulTensorHom M D _ ∈ N
    rw [faithfulTensorHom_left M D ⟨m, hm⟩]
    exact spatialLeft_mem_product (faithfulCyclicAlgebra M) D
      (subset_generatedVonNeumannAlgebra _ ⟨⟨m, hm⟩, rfl⟩)
  · rintro _ ⟨d, hd, rfl⟩
    refine ⟨⟨spatialRight d, spatialRight_mem_product M D hd⟩, ?_, rfl⟩
    change faithfulTensorHom M D _ ∈ N
    rw [faithfulTensorHom_right M D ⟨d, hd⟩]
    exact spatialRight_mem_product (faithfulCyclicAlgebra M) D hd

omit [Nontrivial H] in
theorem faithfulTensorHom_mem (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K)
    (a : Algebra (spatialProductAlgebra M D)) :
    faithfulTensorHom M D a ∈ spatialProductAlgebra (faithfulCyclicAlgebra M) D := by
  let P := spatialProductAlgebra M D
  let N := spatialProductAlgebra (faithfulCyclicAlgebra M) D
  let B : StarSubalgebra ℂ (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
    (M.toStarSubalgebra.map (spatialLeft (H := H) (K := K))) ⊔
      (D.toStarSubalgebra.map (spatialRight (H := H) (K := K)))
  have hBM : B ≤ P.toStarSubalgebra := subset_generatedVonNeumannAlgebra B
  have hB := faithfulTensorHom_generators_map_le M D
  have hBN (b : B) : faithfulTensorHom M D ⟨b.val, hBM b.property⟩ ∈ N := by
    obtain ⟨c, hc, heq⟩ := hB b.property
    have hcb : c = (⟨b.val, hBM b.property⟩ : Algebra P) := Subtype.ext heq
    change faithfulTensorHom M D c ∈ N at hc
    simpa only [hcb] using hc
  exact boundedWeakNormal_maps_generated P (faithfulTensorHom M D)
    (faithfulTensorHom_boundedWeakNormal M D) B hBM le_rfl N hBN a

theorem faithfulTensorHom_generated_range (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K) :
    generatedVonNeumannAlgebra (faithfulTensorHom M D).range =
      spatialProductAlgebra (faithfulCyclicAlgebra M) D := by
  apply le_antisymm
  · apply generatedVonNeumannAlgebra_le_of_le
    rintro _ ⟨a, rfl⟩
    exact faithfulTensorHom_mem M D a
  · apply generatedVonNeumannAlgebra_le_of_le
    apply sup_le
    · rintro _ ⟨m, hm, rfl⟩
      obtain ⟨a, ha⟩ := faithfulCyclicHom_surjective M m hm
      apply subset_generatedVonNeumannAlgebra
      refine ⟨⟨spatialLeft a.val, spatialLeft_mem_product M D a.property⟩, ?_⟩
      exact (faithfulTensorHom_left M D a).trans
        (congrArg (spatialLeft (K := K)) ha)
    · rintro _ ⟨d, hd, rfl⟩
      apply subset_generatedVonNeumannAlgebra
      exact ⟨⟨spatialRight d, spatialRight_mem_product M D hd⟩,
        faithfulTensorHom_right M D ⟨d, hd⟩⟩

def faithfulTensorEquiv (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K) :
    Algebra (spatialProductAlgebra M D) ≃⋆ₐ[ℂ]
      Algebra (spatialProductAlgebra (faithfulCyclicAlgebra M) D) :=
  (boundedWeakNormalEquiv (spatialProductAlgebra M D) (faithfulTensorHom M D)
    (faithfulTensorHom_injective M D) (faithfulTensorHom_boundedWeakNormal M D)).trans
      (vonNeumannAlgebraEquivOfEq (faithfulTensorHom_generated_range M D))

/-- The particular cyclic representation for which the tensor extension has
just been constructed. -/
def tensorCompatibleCyclicRepresentation (M : VonNeumannAlgebra H) :
    FaithfulCyclicRepresentation M where
  K := faithfulCyclicSpace M
  algebra := faithfulCyclicAlgebra M
  equiv := faithfulCyclicEquiv M
  vector := faithfulCyclicVector M
  unit_vector := norm_faithfulCyclicVector M
  cyclic := by
    apply (faithfulCyclicHom_cyclic M).mono
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨faithfulCyclicHom M a, subset_generatedVonNeumannAlgebra _ ⟨a, rfl⟩⟩, rfl⟩
  separating := faithfulCyclicAlgebra_separating M

end

end KadisonKastler

end OAI
