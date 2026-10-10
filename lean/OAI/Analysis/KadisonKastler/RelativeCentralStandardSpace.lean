import OAI.Analysis.KadisonKastler.RelativeCentralVectorDensity
import OAI.Analysis.KadisonKastler.CyclicOrbitRestriction

namespace OAI

/-! # The concrete standard space for a finite matrix relative commutant

The relative algebra's cyclic orbit is exactly the matrix central-vector
space. The original conjugation restricts to this same Hilbert subspace.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

/-- The antiunitary on the actual central-vector subspace. -/
def centralSpaceConjugation (N : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) :
    centralVectorSpace N J ≃ₗᵢ⋆[ℂ] centralVectorSpace N J where
  toFun x := ⟨J x,centralVectorSpace_conjugate N J hJ x.property⟩
  invFun x := ⟨J x,centralVectorSpace_conjugate N J hJ x.property⟩
  left_inv x := Subtype.ext (hJ x)
  right_inv x := Subtype.ext (hJ x)
  map_add' x y := Subtype.ext (map_add J (x : H) y)
  map_smul' c x := Subtype.ext (J.map_smulₛₗ c (x : H))
  norm_map' x := J.norm_map x

@[simp] theorem centralSpaceConjugation_coe (N : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (x : centralVectorSpace N J) :
    (centralSpaceConjugation N J hJ x : H) = J x := rfl

theorem centralSpaceConjugation_involutive (N : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) :
    Function.Involutive (centralSpaceConjugation N J hJ) := by
  intro x
  exact Subtype.ext (hJ x)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (E : MatrixUnitSystem ι (Algebra M))
  (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)

include hJ hright in
theorem relative_cyclicOrbitSpace_eq (η : H)
    (hη : η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J)
    (hcyc : DenseRange (algebraVectorMap M η)) :
    cyclicOrbitSpace E.relativeVonNeumann η =
      centralVectorSpace (matrixUnitConcreteAlgebra E) J := by
  apply SetLike.coe_injective
  exact relative_centralVector_orbit_dense E J hJ hright η hη hcyc

include hJ hright in
theorem relative_cyclicOrbit_projection_eq (η : H)
    (hη : η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J)
    (hcyc : DenseRange (algebraVectorMap M η)) :
    (cyclicOrbitSpace E.relativeVonNeumann η).starProjection =
      (centralVectorSpace (matrixUnitConcreteAlgebra E) J).starProjection := by
  simp only [relative_cyclicOrbitSpace_eq E J hJ hright η hη hcyc]

omit [Nonempty ι] in
theorem relative_vector_separating (η : H)
    (hsep : Function.Injective (algebraVectorMap M η)) :
    Function.Injective (algebraVectorMap E.relativeVonNeumann η) := by
  intro a b hab
  have he := hsep (a₁ := ⟨a.val,E.relativeVonNeumann_le a.property⟩)
    (a₂ := ⟨b.val,E.relativeVonNeumann_le b.property⟩) hab
  exact Subtype.ext (congrArg (fun c : Algebra M => c.val) he)

local instance relativeCentralRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

include hJ hright in
theorem matrixCentralProjection_cyclic
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ = ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hsep : Function.Injective (algebraVectorMap M η)) :
    DenseRange (algebraVectorMap M
      ((centralVectorSpace (matrixUnitConcreteAlgebra E) J).starProjection η)) := by
  classical
  let o : ι := Classical.choice inferInstance
  have hcone := matrixCentralProjection_preserves_positiveCone E J hJ hright ξ o hη
  exact cyclic_of_separating_of_conjugation_fixed J hJ hleft
    (modularPositiveCone_fixed J hright ξ hξ hcone)
    (matrixCentralProjection_separating J hJ hright ξ hξ hpos E hη hsep)

include hJ hright in
theorem relative_averaged_cyclicOrbitSpace_eq
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ = ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hsep : Function.Injective (algebraVectorMap M η)) :
    cyclicOrbitSpace E.relativeVonNeumann
      ((centralVectorSpace (matrixUnitConcreteAlgebra E) J).starProjection η) =
      centralVectorSpace (matrixUnitConcreteAlgebra E) J := by
  apply relative_cyclicOrbitSpace_eq E J hJ hright
  · exact Submodule.starProjection_apply_mem _ _
  · exact matrixCentralProjection_cyclic E J hJ hright hleft ξ hξ hpos hη hsep

end

end KadisonKastler

end OAI
