import OAI.Analysis.KadisonKastler.SpatialProductCyclic
import OAI.Analysis.KadisonKastler.ModularConjugationData
import OAI.Analysis.KadisonKastler.PreparedPairCorrection

namespace OAI

/-! # Separating product vectors

The modular conjugations on the two original spaces supply dense
commutant orbits. Their tensor product commutes with the generated
spatial algebra, so its cyclic product vector separates that algebra.
-/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem ModularConjugationData.commutant_cyclic {M : VonNeumannAlgebra H} {Ω : H}
    (d : ModularConjugationData M Ω) (hc : DenseRange (algebraVectorMap M Ω)) :
    DenseRange (algebraVectorMap M.commutant Ω) := by
  have hJ : DenseRange d.conjugation := d.conjugation.surjective.denseRange
  have hdense := hJ.comp hc d.conjugation.continuous
  apply Dense.mono _ hdense
  rintro _ ⟨a, rfl⟩
  refine ⟨⟨conjugationOperator d.conjugation a.val, d.right_mem le_rfl a⟩, ?_⟩
  change d.conjugation (a.val (d.conjugation Ω)) = d.conjugation (a.val Ω)
  rw [d.fixes_vector]

theorem spatialProduct_commutants_le (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K) :
    spatialProductAlgebra M.commutant D.commutant ≤ (spatialProductAlgebra M D).commutant := by
  apply generatedVonNeumannAlgebra_le_of_le
  apply sup_le
  · rintro _ ⟨a, ha, rfl⟩
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro T hT
    exact (spatialLeft_commutes_product M D a ha T hT).symm
  · rintro _ ⟨b, hb, rfl⟩
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro T hT
    exact (spatialRight_commutes_product M D b hb T hT).symm

/-- A cyclic vector in each original algebra is separating for their
spatial product when each space carries its modular conjugation. -/
theorem separating_spatialProduct_vector
    (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K) (Ω : H) (ξ : K)
    (hM : DenseRange (algebraVectorMap M Ω))
    (hD : DenseRange (algebraVectorMap D ξ))
    (dM : ModularConjugationData M Ω) (dD : ModularConjugationData D ξ) :
    Function.Injective (algebraVectorMap (spatialProductAlgebra M D) (tensorVector ξ Ω)) := by
  have hsmall := denseRange_spatialProduct_vector M.commutant D.commutant Ω ξ
    (dM.commutant_cyclic hM) (dD.commutant_cyclic hD)
  have hlarge : DenseRange (algebraVectorMap (spatialProductAlgebra M D).commutant
      (tensorVector ξ Ω)) := by
    apply Dense.mono _ hsmall
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨a.val, spatialProduct_commutants_le M D a.property⟩, rfl⟩
  intro a b hab
  apply Subtype.ext
  apply operator_eq_of_mem_commutant_of_eq_on_cyclicVector
    (spatialProductAlgebra M D).commutant (tensorVector ξ Ω) hlarge a.val b.val
  · rw [VonNeumannAlgebra.commutant_commutant]
    exact a.property
  · rw [VonNeumannAlgebra.commutant_commutant]
    exact b.property
  · exact hab

end

end KadisonKastler

end OAI
