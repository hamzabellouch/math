import Mathlib
import OAI.Analysis.Commutator.ConjugatedFreeness
import OAI.Analysis.Commutator.FreeMoments
import OAI.Analysis.Commutator.NormalSubalgebra
import OAI.Analysis.Commutator.TracialSmallCorners
import OAI.Analysis.Commutator.UnitarySequence
import OAI.Analysis.Commutator.WordScaling

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Topology BoundedContinuousFunction

open Filter

namespace Kadison.TracialSequence

open FinitePatching FinitePatching.Words FinitePatching.ConjugatedWords

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

lemma sequenceUnitary_free (hτ : ∀ a b : A,τ (a*b)=τ (b*a))
    (hω : (ω : Filter ℕ)≤atTop) (u : ℕ → unitary A)
    (hlim : ∀ (J : Type) (x : J → A),(∀ j,‖x j‖≤1) → (∀ j,τ (x j)=0) →
      ∀ l : List (Letter J Bool),l≠[] → Valid l →
        Tendsto (fun n => τ (word x signPower (PartialUnitary.ofUnitary (u n)) l)) atTop (𝓝 0)) :
    FreeMoments.Free (pair (A := A) (B := boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)
      ((leftRestricted τ ω).comp constantSequence) (sequenceUnitary τ ω u))
      (sequenceTrace τ ω).toLinearMap := by
  apply free_of_centered_unitary_words (A := A) (B := boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)
    _ _ (leftRestricted τ ω).range (sequenceTrace τ ω).toLinearMap
    τ.toLinearMap
  · exact ⟨boundedUnitary u,rfl⟩
  · intro a
    exact ⟨constantSequence a,rfl⟩
  · rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩
    change sequenceTrace τ ω (leftRestricted τ ω a * leftRestricted τ ω b)=
      sequenceTrace τ ω (leftRestricted τ ω b * leftRestricted τ ω a)
    exact (congrArg (fun T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω =>
      sequenceTrace τ ω T) (map_mul (leftRestricted τ ω) a b)).symm.trans
        ((trace_mul τ ω hτ a b).trans
          (congrArg (fun T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω =>
            sequenceTrace τ ω T) (map_mul (leftRestricted τ ω) b a)))
  · exact trace_constant τ ω
  · intro J x hx l hl hv
    apply trace_sequence_word τ ω hω u x signPower l
    exact moment_limit_of_contractions τ signPower (fun n => PartialUnitary.ofUnitary (u n))
      (hlim J) x hx l hl hv

section Relative

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M R : VonNeumannAlgebra H) (hRM : R≤M)

variable (τ : M →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

def restrictBoundedUnitary (u : ℕ → unitary M) (hu : ∀ n,((u n:M):H →L[ℂ] H)∈R) : ℕ →ᵇ R :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun n => ⟨u n,hu n⟩) 1
    (fun n => (PartialUnitary.ofUnitary (u n)).norm_le_one)

lemma map_restrictBoundedUnitary (u : ℕ → unitary M) (hu : ∀ n,((u n:M):H →L[ℂ] H)∈R) :
    mapSequence (NormalSubalgebra.inclusion M R hRM) (restrictBoundedUnitary M R u hu)=boundedUnitary u := by
  ext n
  rfl

lemma sequenceUnitary_in_relative_range (u : ℕ → unitary M)
    (hu : ∀ n,((u n:M):H →L[ℂ] H)∈R) :
    (sequenceUnitary τ ω u : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
      Set.range ((leftRestricted τ ω).comp (mapSequence (NormalSubalgebra.inclusion M R hRM))) := by
  refine ⟨restrictBoundedUnitary M R u hu,?_⟩
  change leftRestricted τ ω (mapSequence _ _)=leftRestricted τ ω (boundedUnitary u)
  exact congrArg (leftRestricted τ ω) (map_restrictBoundedUnitary M R hRM u hu)

lemma constant_in_relative_range (a : M) (ha : (a:H →L[ℂ] H)∈R) :
    leftRestricted τ ω (constantSequence a)∈
      Set.range ((leftRestricted τ ω).comp (mapSequence (NormalSubalgebra.inclusion M R hRM))) := by
  refine ⟨constantSequence (⟨a,ha⟩ : R),?_⟩
  change leftRestricted τ ω (mapSequence _ _)=leftRestricted τ ω (constantSequence a)
  congr 1

end Relative

end Kadison.TracialSequence

end

end OAI
