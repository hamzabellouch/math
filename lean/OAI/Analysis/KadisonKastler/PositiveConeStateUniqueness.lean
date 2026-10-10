import OAI.Analysis.KadisonKastler.PositiveConeOrbitUniqueness
import OAI.Analysis.KadisonKastler.StatePreservingSpatial
import OAI.Analysis.KadisonKastler.CanonicalPositiveCone
import OAI.Analysis.KadisonKastler.ConstructedModularData

namespace OAI

/-! # Uniqueness of a cyclic positive representative of the reference state

Equality of vector functionals constructs the intertwining unitary.
Positivity then forces that unitary to fix the reference vector.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {ξ η : H}

local instance positiveStateRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

theorem positiveCone_eq_of_vectorState_eq
    (d : ModularConjugationData M ξ) (hcyc : DenseRange (algebraVectorMap M ξ))
    (hηcyc : DenseRange (algebraVectorMap M η))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic d.conjugation a ξ))
    (hη : η ∈ modularPositiveCone (M := M) d.conjugation ξ)
    (hstate : ∀ a : Algebra M, inner ℂ ξ (a.val ξ) = inner ℂ η (a.val η)) : η = ξ := by
  let θ := StarAlgEquiv.refl ℂ (Algebra M)
  let V := statePreservingUnitary θ ξ η hcyc hηcyc hstate
  let u : unitary (H →L[ℂ] H) := Unitary.linearIsometryEquiv.symm V
  have huξ : (u : H →L[ℂ] H) ξ = η :=
    statePreservingUnitary_vector θ ξ η hcyc hηcyc hstate
  have huM : (u : H →L[ℂ] H) ∈ M.commutant := by
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro a ha
    ext x
    exact (statePreservingUnitary_intertwines θ ξ η hcyc hηcyc hstate ⟨a,ha⟩ x).symm
  have hu := positiveCone_commutant_unitary_fixed d hpos u huM (huξ.symm ▸ hη)
  rwa [huξ] at hu

theorem canonicalPositiveCone_eq_of_vectorState_eq
    [TopologicalSpace.SeparableSpace H] (J : H ≃ₗᵢ⋆[ℂ] H)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hcyc : DenseRange (algebraVectorMap M ξ))
    (hηcyc : DenseRange (algebraVectorMap M η))
    (hη : η ∈ canonicalModularPositiveCone J ξ hsep hcyc)
    (hstate : ∀ a : Algebra M, inner ℂ ξ (a.val ξ) = inner ℂ η (a.val η)) : η = ξ := by
  let d := constructedModularConjugationData J ξ hsep hcyc
    (tomitaPolarConjugation_commutant_eq J ξ hsep hcyc)
  apply positiveCone_eq_of_vectorState_eq d hcyc hηcyc ?_ hη hstate
  intro a
  exact (tomitaPolarConjugation_quadratic_nonneg J ξ hsep hcyc a).1

end

end KadisonKastler

end OAI
