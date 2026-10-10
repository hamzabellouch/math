import Mathlib
import OAI.Analysis.Commutator.GeneratedFreePair
import OAI.Analysis.Commutator.TracialDoubleCompression
import OAI.Analysis.Commutator.TracialSmallCorners

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace

namespace Kadison.TracialSequence

def constantAction {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) :
    A →⋆ₐ[ℂ] (boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) :=
  (leftRestricted τ ω).comp constantSequence

lemma constantAction_apply {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) (value : A) :
    constantAction τ ω value = leftRestricted τ ω (constantSequence value) := rfl

abbrev generatedFreeAlgebra {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (D : VonNeumannAlgebra (boundedSubspace τ ω)) :
    VonNeumannAlgebra (boundedSubspace τ ω) :=
  GeneratedFreePair.algebra (H := boundedSubspace τ ω) (A := A) D (constantAction τ ω)

lemma generatedFreeAlgebra_constants
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (D : VonNeumannAlgebra (boundedSubspace τ ω)) (a : A) :
    leftRestricted τ ω (constantSequence a)∈generatedFreeAlgebra τ ω D := by
  rw [← constantAction_apply]
  with_reducible
    exact GeneratedFreePair.right_mem (H := boundedSubspace τ ω) (A := A)
      D (constantAction τ ω) a

lemma generatedFreeAlgebra_natural
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (D : VonNeumannAlgebra (boundedSubspace τ ω))
    (hD : ∀ d : D,(d:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
      Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
    (a : generatedFreeAlgebra τ ω D) :
    (a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
      Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))) := by
  dsimp only [generatedFreeAlgebra] at a
  have constant_range (value : A) : constantAction τ ω value ∈ Set.range (leftRestricted τ ω) :=
    ⟨constantSequence value, (constantAction_apply τ ω value).symm⟩
  with_reducible
    exact GeneratedFreePair.in_range_bicommutant (H := boundedSubspace τ ω) (A := A)
      (B := BoundedContinuousFunction ℕ A) D (constantAction τ ω) (leftRestricted τ ω)
      hD constant_range a

lemma generatedFreeAlgebra_natural_of_range
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (D : VonNeumannAlgebra (boundedSubspace τ ω))
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (Q : VonNeumannAlgebra K) (j : Q →⋆ₐ[ℂ] A)
    (hD : ∀ d : D,(d:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
      Set.range ((leftRestricted τ ω).comp (mapSequence j)))
    (a : generatedFreeAlgebra τ ω D) :
    (a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
      Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))) := by
  apply generatedFreeAlgebra_natural τ ω D
  intro operator
  apply Set.subset_centralizer_centralizer
  exact Set.range_comp_subset_range (mapSequence j) (leftRestricted τ ω) (hD operator)

end Kadison.TracialSequence

end

end
end

end OAI
