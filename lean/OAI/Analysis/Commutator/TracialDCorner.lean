import Mathlib
import OAI.Analysis.Commutator.TracialGNSCorners
import OAI.Analysis.Commutator.VectorFreeGeneration

namespace OAI

open Lean in
run_cmd modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "represented_D_corner_bound"

noncomputable section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder

open Filter

namespace Kadison.TracialSequence

lemma represented_D_corner_bound
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (hω : (ω : Filter ℕ)≤atTop)
    (M : VonNeumannAlgebra (boundedSubspace τ ω))
    (hM : ∀ a : M,(a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
      Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
    (hone : τ 1=1)
    (D : VonNeumannAlgebra (boundedSubspace τ ω))
    (hDM : D.toStarSubalgebra≤M.toStarSubalgebra)
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (Q : VonNeumannAlgebra K) (j : Q →⋆ₐ[ℂ] A)
    (hDQ : ∀ d : D,(d:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
      Set.range ((leftRestricted τ ω).comp (mapSequence j)))
    (R : Bool → StarSubalgebra ℂ M)
    (T : τ.GNS →L[ℂ] τ.GNS) {b c β : ℝ} (hb : 0≤b) (hc : 0≤c) (hβ : β<b)
    (hT : ∀ q : Q,IsStarProjection q → (τ (j q)).re≤b →
      ∀ a : A,j q*a*j q=a → ‖T*τ.gnsStarAlgHom a-τ.gnsStarAlgHom a*T‖≤c*‖a‖) :
    VectorGNS.CornerCommutatorBound (D := D) M (sequenceVacuum τ ω)
      (subalgebra_faithful τ ω hτ M hM) (subalgebra_normalized τ ω M hone)
      (VectorGNS.inclusion M D hDM) R (compressed τ ω T) c (β:ℂ) := by
  apply gns_small_corner_bound (A := A) (K := K) (D := D) τ ω hτ hω M hM hone Q j
    (VectorGNS.inclusion M D hDM) ?_ R T hb hc hβ hT
  intro element
  exact hDQ element

end Kadison.TracialSequence
end
end

end OAI
