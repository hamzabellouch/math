import Mathlib
import OAI.Analysis.Commutator.TracialFreeOriginal
import OAI.Analysis.Commutator.TracialGeneratedAlgebra

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.TracialSequence

open FreeMoments

private theorem mem_generated_factor {H B : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [CStarAlgebra B]
    (D : VonNeumannAlgebra H) (k : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (x : GeneratedFreePair.algebra D k) (b : B)
    (hx : (x : H →L[ℂ] H) = k b) :
    x ∈ GeneratedFreePair.factors D k true := by
  change (x : H →L[ℂ] H) ∈ k.range
  exact ⟨b, hx.symm⟩

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
  (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (hω : (ω : Filter ℕ)≤atTop) (hone : τ 1=1)

variable (D : VonNeumannAlgebra (boundedSubspace τ ω))

variable (I : ℕ → Type*) [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)] [∀ n,Nonempty (I n)]
  (φ : ∀ n,Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)
  (inc : ∀ {n m : ℕ},n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
  (hinc : ∀ n m (h : n ≤ m) a,φ m (inc h a)=φ n a)
  (hsize : ∀ n q : ℕ,∃ m,n ≤ m ∧ q ≤ Fintype.card (I m))
  (hDgen : VectorGNS.GeneratedByStages D (sequenceVacuum τ ω) I φ)
  (hfree : Free (GeneratedFreePair.ambient D (constantAction τ ω))
    (VectorFunctional.functional (sequenceVacuum τ ω)).toLinearMap)

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (Q : VonNeumannAlgebra K) (j : Q →⋆ₐ[ℂ] A)
  (hDQ : ∀ d : D,(d:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
    Set.range ((leftRestricted τ ω).comp (mapSequence j)))

include hτ hω hone hinc hsize hDgen hfree hDQ in
theorem generated_free_small_corners_bound
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections D)
    (T : τ.GNS →L[ℂ] τ.GNS)
    (hTQ : ∀ q : Q,T*τ.gnsStarAlgHom (j q)=τ.gnsStarAlgHom (j q)*T)
    {b c β : ℝ} (hb : 0≤b) (hc : 0≤c) (hβ : 0<β) (hβ1 : β≤1) (hβb : β<b)
    (hTC : ∀ q : Q,IsStarProjection q → (τ (j q)).re≤b →
      ∀ a : A,j q*a*j q=a → ‖T*τ.gnsStarAlgHom a-τ.gnsStarAlgHom a*T‖≤c*‖a‖)
    (s : unitary A) (hs0 : τ (s:A)=0) (hs2 : (s:A)*(s:A)=1) :
    ‖T*τ.gnsStarAlgHom (s:A)-τ.gnsStarAlgHom (s:A)*T‖≤1040*c := by
  let N := generatedFreeAlgebra τ ω D
  have hN := generatedFreeAlgebra_natural_of_range τ ω D Q j hDQ
  with_reducible
    have hright (value : A) :
        constantHom τ ω N (generatedFreeAlgebra_constants τ ω D) value ∈
          GeneratedFreePair.factors D (constantAction τ ω) true := by
      exact mem_generated_factor D (constantAction τ ω) _ value
        ((constantHom_coe τ ω N (generatedFreeAlgebra_constants τ ω D) value).trans
          (constantAction_apply τ ω value).symm)
    exact free_position_small_corners_bound τ ω hτ hω N hN hone
      (generatedFreeAlgebra_constants τ ω D) D
      (GeneratedFreePair.left_le D (constantAction τ ω))
      (GeneratedFreePair.factors D (constantAction τ ω))
      (GeneratedFreePair.false_range D (constantAction τ ω))
      hright
      (GeneratedFreePair.free_in_generated D (constantAction τ ω) (sequenceVacuum τ ω) hfree)
      (GeneratedFreePair.original_generation D (constantAction τ ω))
      I φ inc hinc hsize hDgen Q j hDQ hdiffuse T hTQ hb hc hβ hβ1 hβb hTC s hs0 hs2

end Kadison.TracialSequence

end

end OAI
