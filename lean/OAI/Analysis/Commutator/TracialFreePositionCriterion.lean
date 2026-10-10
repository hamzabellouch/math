import Mathlib
import OAI.Analysis.Commutator.TracialGeneratedFreeBound

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.TracialSequence

open FreeMoments

variable {A K : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

structure FreeCornerPositionData {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (ξ : H)
    (action : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (operatorRange : Set (H →L[ℂ] H)) where
  algebra : VonNeumannAlgebra H
  size : ℕ → ℕ
  stage : ∀ n,Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ] algebra
  inclusion : ∀ {n m : ℕ}, n ≤ m →
    Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ]
      Matrix (Fin (size m+1)) (Fin (size m+1)) ℂ
  compatible : ∀ n m (h : n ≤ m) a,stage m (inclusion h a)=stage n a
  unbounded : ∀ n q : ℕ,∃ m, n ≤ m ∧ q ≤ size m+1
  generated : VectorGNS.GeneratedByStages algebra ξ
    (fun n => Fin (size n+1)) stage
  free : Free (GeneratedFreePair.ambient algebra action)
    (VectorFunctional.functional ξ).toLinearMap
  in_range : ∀ d : algebra,(d:H →L[ℂ] H)∈operatorRange
  diffuse : DiffuseProjection.HasNoMinimalProjections algebra

abbrev FreeCornerPosition (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (Q : VonNeumannAlgebra K) (j : Q →⋆ₐ[ℂ] A) :=
  FreeCornerPositionData (sequenceVacuum τ ω) (constantAction τ ω)
    (Set.range ((leftRestricted τ ω).comp (mapSequence j)))

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
  (Q : VonNeumannAlgebra K) (j : Q →⋆ₐ[ℂ] A)

theorem FreeCornerPosition.symmetry_bound (F : FreeCornerPosition τ ω Q j)
    (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (hω : (ω : Filter ℕ) ≤ atTop) (hone : τ 1=1)
    (T : τ.GNS →L[ℂ] τ.GNS)
    (hTQ : ∀ q : Q,T*τ.gnsStarAlgHom (j q)=τ.gnsStarAlgHom (j q)*T)
    {b c β : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hβ : 0<β) (hβ1 : β ≤ 1) (hβb : β<b)
    (hTC : ∀ q : Q,IsStarProjection q → (τ (j q)).re ≤ b →
      ∀ a : A,j q*a*j q=a → ‖T*τ.gnsStarAlgHom a-τ.gnsStarAlgHom a*T‖ ≤ c*‖a‖)
    (s : unitary A) (hs0 : τ (s:A)=0) (hs2 : (s:A)*(s:A)=1) :
    ‖T*τ.gnsStarAlgHom (s:A)-τ.gnsStarAlgHom (s:A)*T‖ ≤ 1040*c := by
  change FreeCornerPositionData (sequenceVacuum τ ω) (constantAction τ ω)
    (Set.range ((leftRestricted τ ω).comp (mapSequence j))) at F
  apply generated_free_small_corners_bound τ ω hτ hω hone F.algebra
    (fun n => Fin (F.size n+1)) F.stage F.inclusion F.compatible
    _ F.generated F.free Q j F.in_range F.diffuse T hTQ hb hc hβ hβ1 hβb hTC s hs0 hs2
  intro n q
  simpa only [Fintype.card_fin] using F.unbounded n q

end Kadison.TracialSequence

end

end OAI
