import Mathlib
import OAI.Analysis.Commutator.ConstantSequenceRange
import OAI.Analysis.Commutator.TraceEquivGNS

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Topology BoundedContinuousFunction

namespace Kadison.TracialSequence

open TracialGNS

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

lemma constant_vector_closed_of_GNS (hclosed : IsClosed {x : τ.GNS | ∃ a : A,‖a‖≤1 ∧ algebraVector τ a=x}) :
    IsClosed {x : boundedSubspace τ ω | ∃ a : A,‖a‖≤1 ∧ vectorIn τ ω (constantSequence a)=x} := by
  have heq (a : A) : vectorIn τ ω (constantSequence a)=constantIn τ ω (algebraVector τ a) := by
    apply Subtype.ext
    exact vector_const τ ω a
  have hc := (constantIn τ ω).isometry.isClosedEmbedding.isClosedMap _ hclosed
  suffices he : {x : boundedSubspace τ ω | ∃ a : A,‖a‖≤1 ∧ vectorIn τ ω (constantSequence a)=x} =
      (constantIn τ ω) '' {x : τ.GNS | ∃ a : A,‖a‖≤1 ∧ algebraVector τ a=x} by
    rw [he]
    exact hc
  ext x
  constructor
  · rintro ⟨a,ha,hax⟩
    exact ⟨algebraVector τ a,⟨a,ha,rfl⟩,(heq a).symm.trans hax⟩
  · rintro ⟨y,⟨a,ha,rfl⟩,hy⟩
    exact ⟨a,ha,(heq a).trans hy⟩

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (e : A ≃⋆ₐ[ℂ] M) (σ : M →ₚ[ℂ] ℂ)

lemma constant_range_bicommutant_of_equiv (hτ : ∀ a b : A,τ (a*b)=τ (b*a))
    (htrace : ∀ a,σ (e a)=τ a) (hnormal : NormalGNS.BoundedWOTContinuous M σ) :
    Set.centralizer (Set.centralizer (Set.range ((leftRestricted τ ω).comp constantSequence)))=Set.range ((leftRestricted τ ω).comp constantSequence) := by
  apply constant_range_bicommutant_of_closed τ ω hτ
  apply constant_vector_closed_of_GNS τ ω
  exact TraceEquivGNS.vector_unitball_closed e τ σ htrace
    (NormalGNS.vector_unitball_isClosed M σ hnormal)

end Kadison.TracialSequence

end

end
end

end OAI
