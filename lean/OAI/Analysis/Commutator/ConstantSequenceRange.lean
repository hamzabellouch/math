import Mathlib
import OAI.Analysis.Commutator.TracialDoubleCompression

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Topology BoundedContinuousFunction

open Filter

namespace Kadison.TracialSequence

open TracialGNS HilbertSequence

section Represented

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

lemma constant_vectorIn (a : M) : vectorIn τ ω (constantSequence a)=constantIn τ ω (algebraVector τ a) := by
  apply Subtype.ext
  exact vector_const τ ω a

lemma constant_vector_unitball_isClosed (hnormal : NormalGNS.BoundedWOTContinuous M τ) :
    IsClosed {x : boundedSubspace τ ω | ∃ a : M, ‖a‖≤1 ∧ vectorIn τ ω (constantSequence a)=x} := by
  have hc := (constantIn τ ω).isometry.isClosedEmbedding.isClosedMap _
    (NormalGNS.vector_unitball_isClosed M τ hnormal)
  suffices he : {x : boundedSubspace τ ω | ∃ a : M, ‖a‖≤1 ∧ vectorIn τ ω (constantSequence a)=x} =
      (constantIn τ ω) '' {x : τ.GNS | ∃ a : M, ‖a‖≤1 ∧ algebraVector τ a=x} by
    exact (congrArg IsClosed he).mpr hc
  ext x
  constructor
  · rintro ⟨a,ha,hax⟩
    exact ⟨algebraVector τ a,⟨a,ha,rfl⟩,(constant_vectorIn M τ ω a).symm.trans hax⟩
  · rintro ⟨y,⟨a,ha,rfl⟩,hy⟩
    exact ⟨a,ha,(constant_vectorIn M τ ω a).trans hy⟩

end Represented

section Abstract

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

include hτ in
lemma constant_bicommutant_contraction (hclosed : IsClosed {x : boundedSubspace τ ω | ∃ a : A, ‖a‖≤1 ∧ vectorIn τ ω (constantSequence a)=x})
    {T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range ((leftRestricted τ ω).comp constantSequence))))
    (hsT : IsSelfAdjoint T) (hnT : ‖T‖≤1) :
    ∃ a : A, ‖a‖≤1 ∧ leftRestricted τ ω (constantSequence a)=T := by
  let φ := (leftRestricted τ ω).comp constantSequence
  have hx : T (sequenceVacuum τ ω)∈closure
      {x : boundedSubspace τ ω | ∃ a : A, ‖a‖≤1 ∧ vectorIn τ ω (constantSequence a)=x} := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨a,_,hna,ha⟩ := Kaplansky.range_selfAdjoint_contraction_finite_approx
      Unit φ hT hsT hnT (fun _ => sequenceVacuum τ ω) ε hε
    refine ⟨vectorIn τ ω (constantSequence a),⟨a,hna,rfl⟩,?_⟩
    rw [dist_eq_norm,norm_sub_rev]
    change ‖vectorIn τ ω (constantSequence a)-T (sequenceVacuum τ ω)‖<ε
    rw [←leftRestricted_vacuum]
    exact ha ()
  rw [hclosed.closure_eq] at hx
  obtain ⟨a,hna,ha⟩ := hx
  refine ⟨a,hna,bicommutant_eq_of_vacuum τ ω hτ _ _ ?_ ?_ ?_⟩
  · exact Set.subset_centralizer_centralizer (Set.mem_range_self (constantSequence a))
  · intro c hc
    apply hT c
    rintro _ ⟨b,rfl⟩
    exact hc _ ⟨constantSequence b,rfl⟩
  · simpa only [leftRestricted_vacuum] using ha

lemma constant_range_bicommutant_of_closed
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))
    (hclosed : IsClosed {x : boundedSubspace τ ω | ∃ a : A, ‖a‖≤1 ∧ vectorIn τ ω (constantSequence a)=x}) :
    Set.centralizer (Set.centralizer (Set.range ((leftRestricted τ ω).comp constantSequence)))=
      Set.range ((leftRestricted τ ω).comp constantSequence) := by
  exact BicommutantRange.operatorHom_range (H := boundedSubspace τ ω)
    ((leftRestricted τ ω).comp constantSequence) fun T hT hsT hnT =>
      (constant_bicommutant_contraction τ ω hτ hclosed hT hsT hnT).imp fun _ ha => ha.2

end Abstract

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

lemma constant_range_bicommutant (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hnormal : NormalGNS.BoundedWOTContinuous M τ) :
    Set.centralizer (Set.centralizer (Set.range ((leftRestricted τ ω).comp constantSequence)))=
      Set.range ((leftRestricted τ ω).comp constantSequence) :=
  constant_range_bicommutant_of_closed τ ω hτ (constant_vector_unitball_isClosed M τ ω hnormal)

end Kadison.TracialSequence

end

end
end

end OAI
