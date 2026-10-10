import OAI.Analysis.KadisonKastler.TomitaPolarCoordinates

namespace OAI

/-! # The antiunitary obtained from the polar graph coordinates

Transporting adjoint on the closed graph yields an involutive antiunitary
on the original Hilbert space. The commutant identity is a subsequent step.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

omit [CompleteSpace H] in
theorem tomitaGraphFlip_involutive (J : H ≃ₗᵢ⋆[ℂ] H) :
    Function.Involutive (tomitaGraphFlip J) := by
  intro ξ
  ext i
  fin_cases i <;> simp

/-- Adjoint restricts to an antiunitary involution on the closed graph. -/
def tomitaGraphAntiunitary (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) :
    rescaledGraphSubspace M J Ω 1 ≃ₗᵢ⋆[ℂ] rescaledGraphSubspace M J Ω 1 where
  toFun ξ := ⟨tomitaGraphFlip J ξ.val, tomitaGraphFlip_mem J Ω ξ.property⟩
  invFun ξ := ⟨tomitaGraphFlip J ξ.val, tomitaGraphFlip_mem J Ω ξ.property⟩
  left_inv ξ := Subtype.ext (tomitaGraphFlip_involutive J ξ.val)
  right_inv ξ := Subtype.ext (tomitaGraphFlip_involutive J ξ.val)
  map_add' ξ η := Subtype.ext ((tomitaGraphFlip J).map_add ξ.val η.val)
  map_smul' z ξ := Subtype.ext ((tomitaGraphFlip J).map_smulₛₗ z ξ.val)
  norm_map' ξ := (tomitaGraphFlip J).norm_map ξ.val

theorem tomitaGraphAntiunitary_involutive (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) :
    Function.Involutive (tomitaGraphAntiunitary (M := M) J Ω) :=
  fun ξ => Subtype.ext (tomitaGraphFlip_involutive J ξ.val)

/-- The polar conjugation constructed on the original represented Hilbert space. -/
def tomitaPolarConjugation (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) : H ≃ₗᵢ⋆[ℂ] H :=
  ((tomitaPolarCoordinates J Ω hsep hcyc).trans (tomitaGraphAntiunitary J Ω)).trans
    (tomitaPolarCoordinates J Ω hsep hcyc).symm

theorem tomitaPolarConjugation_involutive (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) :
    Function.Involutive (tomitaPolarConjugation J Ω hsep hcyc) := by
  intro ξ
  change (tomitaPolarCoordinates J Ω hsep hcyc).symm
    (tomitaGraphAntiunitary J Ω ((tomitaPolarCoordinates J Ω hsep hcyc)
      ((tomitaPolarCoordinates J Ω hsep hcyc).symm
        (tomitaGraphAntiunitary J Ω ((tomitaPolarCoordinates J Ω hsep hcyc) ξ))))) = ξ
  rw [LinearIsometryEquiv.apply_symm_apply, tomitaGraphAntiunitary_involutive,
    LinearIsometryEquiv.symm_apply_apply]

end

end KadisonKastler

end OAI
