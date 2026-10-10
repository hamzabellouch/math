import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralBarProjection

namespace OAI

/-! # Exactness of the central transgression at second homology

When the transgression of a two-cycle vanishes, its corrected section lift is
completed to a cycle by an actual bar chain in the abelian kernel. Degenerate
chains supply the explicit homotopy after projection.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {N G Q : Type} [CommGroup N] [Group G] [Group Q]
variable (E : GroupExtension N G Q) (hc : E.inl.range ≤ Subgroup.center G)

theorem centralExtension_cycle_lift (σ : E.Section)
    (z : groupHomology.cycles₂ (integralTrivialCoefficient Q))
    (hz : centralExtensionTransgression E hc σ
      (groupHomology.H2π (integralTrivialCoefficient Q) z) = 0) :
    ∃ w : groupHomology.cycles₂ (integralTrivialCoefficient G),
      (groupHomology.mapCycles₂ E.rightHom (groupIntegralTrivialCoefficientMap E.rightHom)
        w).val - z.val ∈ groupHomology.boundaries₂ (integralTrivialCoefficient Q) := by
  have hsum : abelianBarSum (centralBarKernelLetters E σ z.val) = 0 := by
    rw [centralBarKernelLetters_sum]
    exact (centralExtensionTransgression_cycle E hc σ z).symm.trans hz
  obtain ⟨t, ht⟩ := abelianBar_boundary_of_sum_zero _ hsum
  have htaug : integralBarAugmentation (N × N) t = 0 := by
    rw [← integralBarAugmentation_boundary, ht, centralBarKernelLetters_augmentation,
      integralBarAugmentation_cycle]
  let w : groupHomology.cycles₂ (integralTrivialCoefficient G) :=
    ⟨centralBarLift E σ z.val +
        groupHomology.chainsMap₂ E.inl (groupIntegralTrivialCoefficientMap E.inl) t, by
      change groupHomology.d₂₁ (integralTrivialCoefficient G) (_ + _) = 0
      rw [map_add, centralBarLift_boundary, integralBarMap_boundary, ht,
        z.property, map_zero, zero_sub, neg_add_cancel]⟩
  refine ⟨w, ?_⟩
  have hw : (groupHomology.mapCycles₂ E.rightHom
      (groupIntegralTrivialCoefficientMap E.rightHom) w).val =
      z.val - integralBarDegenerate z.val := by
    rw [groupHomology.coe_mapCycles₂]
    change groupHomology.chainsMap₂ E.rightHom
      (groupIntegralTrivialCoefficientMap E.rightHom)
      (centralBarLift E σ z.val +
        groupHomology.chainsMap₂ E.inl (groupIntegralTrivialCoefficientMap E.inl) t) = _
    rw [map_add, centralBarLift_projection, centralKernelBar_projection,
      htaug, Finsupp.single_zero, add_zero]
  rw [hw]
  refine ⟨-integralBarDegeneratePrimitive z.val, ?_⟩
  change groupHomology.d₃₂ (integralTrivialCoefficient Q)
    (-integralBarDegeneratePrimitive z.val) = _
  rw [map_neg, integralBarDegenerate_boundary, integralBarAugmentation_cycle,
    Finsupp.single_zero, sub_zero]
  abel

theorem centralExtensionTransgression_exact_H2 (σ : E.Section) :
    LinearMap.range
      (groupHomology.map E.rightHom (groupIntegralTrivialCoefficientMap E.rightHom) 2).hom =
    LinearMap.ker (centralExtensionTransgression E hc σ) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact centralExtensionTransgression_lift E hc σ x
  · intro x hx
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
      (groupHomology.H2π (integralTrivialCoefficient Q))).mp inferInstance x
    obtain ⟨w, hw⟩ := centralExtension_cycle_lift E hc σ z hx
    refine ⟨groupHomology.H2π (integralTrivialCoefficient G) w, ?_⟩
    rw [groupHomology.H2π_comp_map_apply]
    exact (groupHomology.H2π_eq_iff _ _).mpr hw

end PolycyclicRecognition

end

end OAI
