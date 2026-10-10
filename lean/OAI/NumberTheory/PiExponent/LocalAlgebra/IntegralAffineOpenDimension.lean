import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Stalk
import OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension
import OAI.NumberTheory.PiExponent.LocalAlgebra.AffineTranscendenceDimension

namespace OAI

noncomputable section
namespace PiExponent.IntegralAffineOpenDimension
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
variable (p : X ⟶ Spec (.of k))

def chartConstants (U : X.affineOpens) : k →+* Γ(X, U.1) :=
  (Spec.preimage (U.2.fromSpec ≫ p)).hom

@[instance_reducible] def chartAlgebra (U : X.affineOpens) : Algebra k Γ(X, U.1) :=
  (chartConstants p U).toAlgebra

@[instance_reducible] def functionFieldAlgebra : Algebra k X.functionField :=
  (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p)).hom.toAlgebra

theorem germToFunctionField_fromSpec (U : X.affineOpens) [Nonempty U.1] :
    Spec.map (X.germToFunctionField U.1) ≫ U.2.fromSpec =
      X.fromSpecStalk (genericPoint X) :=
  U.2.fromSpecStalk_eq_fromSpecStalk _

theorem chart_functionField_scalarTower (U : X.affineOpens) [Nonempty U.1] :
    letI := chartAlgebra p U
    letI := functionFieldAlgebra p
    IsScalarTower k Γ(X, U.1) X.functionField := by
  let := chartAlgebra p U
  let := functionFieldAlgebra p
  have h : Spec.preimage (U.2.fromSpec ≫ p) ≫ X.germToFunctionField U.1 =
      Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, ← Category.assoc,
      germToFunctionField_fromSpec, Spec.map_preimage]
  exact IsScalarTower.of_algebraMap_eq' (CommRingCat.hom_ext_iff.mp h).symm

omit [IsIntegral X] in
theorem chart_finiteType [LocallyOfFiniteType p] (U : X.affineOpens) :
    letI := chartAlgebra p U
    Algebra.FiniteType k Γ(X, U.1) := by
  let := chartAlgebra p U
  have h : LocallyOfFiniteType (Spec.map (Spec.preimage (U.2.fromSpec ≫ p))) := by
    rw [Spec.map_preimage]
    let hOpen : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
    let : LocallyOfFiniteType U.2.fromSpec :=
      @locallyOfFiniteType_of_isOpenImmersion _ _ U.2.fromSpec hOpen
    exact locallyOfFiniteType_comp U.2.fromSpec p
  have h' : RingHom.FiniteType (chartConstants p U) := HasRingHomProperty.Spec_iff.mp h
  exact RingHom.finiteType_algebraMap.mp h'

theorem chart_ring_dimension [LocallyOfFiniteType p] (U : X.affineOpens) [Nonempty U.1] :
    letI := functionFieldAlgebra p
    ringKrullDim Γ(X, U.1) = ((Algebra.trdeg k X.functionField).toNat : WithBot ℕ∞) := by
  let := chartAlgebra p U
  let := functionFieldAlgebra p
  let := chart_functionField_scalarTower p U
  let := chart_finiteType p U
  let := functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  let : FaithfulSMul Γ(X, U.1) X.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective _ _)
  rw [PiExponentJets.W24.finiteType_domain_krullDim_eq_trdeg k Γ(X, U.1),
    PiExponentJets.W24.localization_trdeg_toNat_eq k Γ(X, U.1) X.functionField
      (nonZeroDivisors Γ(X, U.1))]

omit [IsIntegral X] in
theorem affine_dimension_eq_ring (U : X.affineOpens) :
    topologicalKrullDim U.1 = ringKrullDim Γ(X, U.1) := by
  have h := U.2.isoSpec.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq
  change topologicalKrullDim U.1 = topologicalKrullDim (PrimeSpectrum Γ(X, U.1)) at h
  exact h.trans (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _)

theorem affine_open_dimension_eq [LocallyOfFiniteType p] (U : X.affineOpens) [Nonempty U.1] :
    topologicalKrullDim U.1 = topologicalKrullDim X := by
  let := functionFieldAlgebra p
  have hU : topologicalKrullDim U.1 =
      ((Algebra.trdeg k X.functionField).toNat : WithBot ℕ∞) :=
    (affine_dimension_eq_ring U).trans (chart_ring_dimension p U)
  apply le_antisymm (topologicalKrullDim_subspace_le X U.1)
  change topologicalKrullDim X ≤ topologicalKrullDim U.1
  rw [hU]
  apply PiExponent.NumericalAmpleness.dimension_le_of_local_bound
  intro x
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  let : Nonempty V := ⟨⟨x, hxV⟩⟩
  exact ⟨V, hxV, ((affine_dimension_eq_ring ⟨V, hV⟩).trans
    (chart_ring_dimension p ⟨V, hV⟩)).le⟩

theorem affine_ring_dimension_eq [LocallyOfFiniteType p] (U : X.affineOpens) [Nonempty U.1] :
    ringKrullDim Γ(X, U.1) = topologicalKrullDim X :=
  (affine_dimension_eq_ring U).symm.trans (affine_open_dimension_eq p U)

end PiExponent.IntegralAffineOpenDimension

end

end OAI
