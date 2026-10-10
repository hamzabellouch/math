import Mathlib
import OAI.Analysis.Commutator.TracialSmallCorners

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder

namespace Kadison.TracialSequence

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (Q : VonNeumannAlgebra K) (j : Q →⋆ₐ[ℂ] A)

lemma compressed_commutes_of_range (T : τ.GNS →L[ℂ] τ.GNS)
    (hT : ∀ q : Q,T*τ.gnsStarAlgHom (j q)=τ.gnsStarAlgHom (j q)*T)
    (d : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)
    (hd : d∈Set.range ((leftRestricted τ ω).comp (mapSequence j))) :
    compressed τ ω T*d=d*compressed τ ω T := by
  obtain ⟨a,rfl⟩ := hd
  exact commutator_zero τ ω T (mapSequence j a) (fun i => hT (a i))

end Kadison.TracialSequence

end

end
end

end OAI
