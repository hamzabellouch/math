import Mathlib
import OAI.Analysis.Commutator.AbstractFreeCornerFromUnitary
import OAI.Analysis.Commutator.ConstantSequenceRange

namespace OAI

noncomputable section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.TracialSequence

open FinitePatching.ConjugatedWords

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M R : VonNeumannAlgebra H) (hRM : R≤M)

variable (τ : M →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (size : ℕ → ℕ)

variable (stage : ∀ n,Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ] M)

variable (inc : ∀ {n m : ℕ},n ≤ m → Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ]
  Matrix (Fin (size m+1)) (Fin (size m+1)) ℂ)

theorem freeCornerPosition_of_unitary
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a)) (hω : (ω : Filter ℕ)≤atTop)
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M,(∀ n (a : Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ),
      stage n a*b=b*stage n a) → ∃ c : ℂ,b=algebraMap ℂ M c)
    (hstage : ∀ n a,(stage n a : H →L[ℂ] H)∈R)
    (hinc : ∀ n m (h : n ≤ m) a,stage m (inc h a)=stage n a)
    (hsize : ∀ n q : ℕ,∃ m,n ≤ m ∧ q ≤ size m+1)
    (U : unitary (boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω))
    (hu : (U:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
      Set.range ((leftRestricted τ ω).comp (mapSequence (NormalSubalgebra.inclusion M R hRM))))
    (hfree : FreeMoments.Free (pair (A := M) (B := boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) (constantAction τ ω) U) (sequenceTrace τ ω).toLinearMap) :
    Nonempty (FreeCornerPosition τ ω R (NormalSubalgebra.inclusion M R hRM)) := by
  apply freeCornerPosition_of_unitary_abstract R (NormalSubalgebra.inclusion M R hRM)
    τ ω size stage inc hτ hω (constant_range_bicommutant M τ ω hτ hnormal)
    hfaith hone hirr _ hinc hsize U hu hfree
  intro n a
  exact ⟨⟨stage n a,hstage n a⟩,rfl⟩

end Kadison.TracialSequence
end
end

end OAI
