import OAI.Analysis.KadisonKastler.PositiveConeUnitaryOrbit
import OAI.Analysis.KadisonKastler.PositiveConeFaithfulApproximation
import OAI.Analysis.KadisonKastler.StatePreservingSpatial

namespace OAI

/-! # Faithful vector states determine their positive representatives

Cyclicity follows from separation and the fixed-conjugation property.
Equality of the vector functionals then supplies a commutant unitary,
whose positive orbit has only one point.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance positiveFaithfulUniqueRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

theorem separating_of_vectorState_eq {η ζ : H}
    (hs : Function.Injective (algebraVectorMap M η))
    (hstate : ∀ a : Algebra M, inner ℂ η (a.val η) = inner ℂ ζ (a.val ζ)) :
    Function.Injective (algebraVectorMap M ζ) := by
  let θ := StarAlgEquiv.refl ℂ (Algebra M)
  intro a b hab
  apply hs
  change a.val η = b.val η
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hn := statePreserving_norm θ η ζ hstate (a-b)
  change ‖a.val ζ - b.val ζ‖ = ‖a.val η - b.val η‖ at hn
  rw [show a.val ζ = b.val ζ from hab,sub_self,norm_zero] at hn
  exact hn.symm

theorem positiveCone_faithful_state_unique
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ = ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η ζ : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hζ : ζ ∈ modularPositiveCone (M := M) J ξ)
    (hs : Function.Injective (algebraVectorMap M η))
    (hstate : ∀ a : Algebra M, inner ℂ η (a.val η) = inner ℂ ζ (a.val ζ)) : ζ = η := by
  have hηcyc := cyclic_of_separating_of_conjugation_fixed J hJ hleft
    (modularPositiveCone_fixed J hright ξ hξ hη) hs
  have hζcyc := cyclic_of_separating_of_conjugation_fixed J hJ hleft
    (modularPositiveCone_fixed J hright ξ hξ hζ) (separating_of_vectorState_eq hs hstate)
  let θ := StarAlgEquiv.refl ℂ (Algebra M)
  let V := statePreservingUnitary θ η ζ hηcyc hζcyc hstate
  let u : unitary (H →L[ℂ] H) := Unitary.linearIsometryEquiv.symm V
  have huη : (u : H →L[ℂ] H) η = ζ :=
    statePreservingUnitary_vector θ η ζ hηcyc hζcyc hstate
  have huM : (u : H →L[ℂ] H) ∈ M.commutant := by
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro a ha
    ext x
    exact (statePreservingUnitary_intertwines θ η ζ hηcyc hζcyc hstate ⟨a,ha⟩ x).symm
  have hu := positiveCone_unitary_orbit_unique J hJ hright hleft ξ hξ hpos hη u huM
    (huη.symm ▸ hζ)
  rwa [huη] at hu

end

end KadisonKastler

end OAI
