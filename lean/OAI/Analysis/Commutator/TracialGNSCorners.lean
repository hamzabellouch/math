import Mathlib
import OAI.Analysis.Commutator.FreeSymmetrization
import OAI.Analysis.Commutator.GNSCornerTransport
import OAI.Analysis.Commutator.TracialSmallCorners

namespace OAI

open Lean in
run_cmd modifyEnv fun env =>
  let env := Lean.LibrarySuggestions.nameDenyListExt.addEntry env "subtype_corner"
  let env := Lean.LibrarySuggestions.nameDenyListExt.addEntry env "gnsCompression_commutes"
  let env := Lean.LibrarySuggestions.nameDenyListExt.addEntry env "small_represented_corner_bound"
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "gns_small_corner_bound"

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder BoundedContinuousFunction

open Filter ContinuousLinearMap

namespace Kadison.VectorGNS

lemma subtype_corner
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (q a : M) (hl : q*a=a) (hr : a*q=a) :
    (q:H →L[ℂ] H)*a*q=a := by
  have hh : q*a*q=a := by rw [hl,hr]
  exact congrArg M.toStarSubalgebra.subtype hh

def CornerCommutatorBound
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (ξ : H)
    (hfaith : ∀ a : M,subalgebraTrace M ξ (star a*a)=0 → a=0)
    (hone : subalgebraTrace M ξ 1=1)
    {D : Type} [CStarAlgebra D] (f : D →⋆ₐ[ℂ] M)
    (R : Bool → StarSubalgebra ℂ M) (T : H →L[ℂ] H) (c : ℝ) (β : ℂ) : Prop :=
  ∀ X,CornerSymmetrization.CornerElement
    (FreeBlocks.factorOperators (vectorState M ξ hfaith hone) f)
    (FreeBlocks.ambientOperators (vectorState M ξ hfaith hone) R)
    (TracialGNS.vacuum (subalgebraTrace M ξ)) β X →
    ‖subalgebraCompression M ξ T*X-X*subalgebraCompression M ξ T‖≤c*‖X‖

end Kadison.VectorGNS

namespace Kadison.TracialSequence

open FreeWordTensor FreeBlocks

abbrev gnsCompression
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (M : VonNeumannAlgebra (boundedSubspace τ ω))
    (T : τ.GNS →L[ℂ] τ.GNS) :=
  VectorGNS.subalgebraCompression M (sequenceVacuum τ ω) (compressed τ ω T)

private lemma represented_commutes
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (M : VonNeumannAlgebra (boundedSubspace τ ω))
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (Q : VonNeumannAlgebra K) (j : Q →⋆ₐ[ℂ] A)
    {D : Type} [CStarAlgebra D] (f : D →⋆ₐ[ℂ] M)
    (hfQ : ∀ q : D, (f q : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) ∈
      Set.range ((leftRestricted τ ω).comp (mapSequence j)))
    (operator : τ.GNS →L[ℂ] τ.GNS)
    (hoperator : ∀ entry : Q,
      operator*τ.gnsStarAlgHom (j entry)=τ.gnsStarAlgHom (j entry)*operator)
    (element : D) :
    compressed τ ω operator*(f element:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)=
      (f element:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)*compressed τ ω operator :=
  (Set.forall_mem_range
    (f := ((leftRestricted τ ω).comp (mapSequence j)))
    (p := fun represented =>
      compressed τ ω operator*represented=represented*compressed τ ω operator)).mpr
    (fun sequence => commutator_zero τ ω operator (mapSequence j sequence)
      (fun index => hoperator (sequence index)))
    (f element:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) (hfQ element)

lemma gnsCompression_commutes
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (M : VonNeumannAlgebra (boundedSubspace τ ω))
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (Q : VonNeumannAlgebra K) (j : Q →⋆ₐ[ℂ] A)
    {D : Type} [CStarAlgebra D] (f : D →⋆ₐ[ℂ] M)
    (hfQ : ∀ q : D, (f q : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) ∈
      Set.range ((leftRestricted τ ω).comp (mapSequence j)))
    (T : τ.GNS →L[ℂ] τ.GNS)
    (hT : ∀ q : Q,T*τ.gnsStarAlgHom (j q)=τ.gnsStarAlgHom (j q)*T) (q : D) :
    gnsCompression τ ω M T*(VectorGNS.subalgebraTrace M (sequenceVacuum τ ω)).gnsStarAlgHom (f q)=
    (VectorGNS.subalgebraTrace M (sequenceVacuum τ ω)).gnsStarAlgHom (f q)*gnsCompression τ ω M T :=
  VectorGNS.commutes M (sequenceVacuum τ ω) (compressed τ ω T) (f q)
    (represented_commutes τ ω M Q j f hfQ T hT q)

lemma small_represented_corner_bound
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (hω : (ω : Filter ℕ) ≤ atTop)
    (M : VonNeumannAlgebra (boundedSubspace τ ω))
    (hM : ∀ a : M, (a : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) ∈
      Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (Q : VonNeumannAlgebra K) (j : Q →⋆ₐ[ℂ] A)
    {D : Type} [CStarAlgebra D] (f : D →⋆ₐ[ℂ] M)
    (hfQ : ∀ q : D, (f q : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) ∈
      Set.range ((leftRestricted τ ω).comp (mapSequence j)))
    (T : τ.GNS →L[ℂ] τ.GNS) {b c β : ℝ} (hb : 0≤b) (hc : 0≤c) (hβ : β<b)
    (hT : ∀ q : Q,IsStarProjection q → (τ (j q)).re≤b →
      ∀ a : A,j q*a*j q=a → ‖T*τ.gnsStarAlgHom a-τ.gnsStarAlgHom a*T‖≤c*‖a‖)
    (q : D) (hq : IsStarProjection (f q))
    (hqt : VectorGNS.subalgebraTrace M (sequenceVacuum τ ω) (f q)=(β:ℂ))
    (a : M) (hl : f q*a=a) (hr : a*f q=a) :
    ‖compressed τ ω T*(a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)-
      (a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)*compressed τ ω T‖≤c*‖a‖ := by
  have he : IsStarProjection (f q:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) :=
    hq.map M.toStarSubalgebra.subtype
  have het : (sequenceTrace τ ω (f q:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)).re<b := by
    change (VectorGNS.subalgebraTrace M (sequenceVacuum τ ω) (f q)).re<b
    rw [hqt,Complex.ofReal_re]
    exact hβ
  have hqa := VectorGNS.subtype_corner M (f q) a hl hr
  exact small_corner_bound τ ω hτ Q j hω T hb hc hT he (hfQ q) het (hM a) hqa

theorem gns_small_corner_bound
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (hω : (ω : Filter ℕ) ≤ atTop)
    (M : VonNeumannAlgebra (boundedSubspace τ ω))
    (hM : ∀ a : M, (a : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) ∈
      Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
    (hone : τ 1 = 1)
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (Q : VonNeumannAlgebra K) (j : Q →⋆ₐ[ℂ] A)
    {D : Type} [CStarAlgebra D] (f : D →⋆ₐ[ℂ] M)
    (hfQ : ∀ q : D, (f q : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) ∈
      Set.range ((leftRestricted τ ω).comp (mapSequence j)))
    (R : Bool → StarSubalgebra ℂ M)
    (T : τ.GNS →L[ℂ] τ.GNS) {b c β : ℝ} (hb : 0≤b) (hc : 0≤c) (hβ : β<b)
    (hT : ∀ q : Q,IsStarProjection q → (τ (j q)).re≤b →
      ∀ a : A,j q*a*j q=a → ‖T*τ.gnsStarAlgHom a-τ.gnsStarAlgHom a*T‖≤c*‖a‖) :
    VectorGNS.CornerCommutatorBound M (sequenceVacuum τ ω)
      (subalgebra_faithful τ ω hτ M hM) (subalgebra_normalized τ ω M hone)
      f R (compressed τ ω T) c (β:ℂ) :=
  VectorGNS.corner_bound M (sequenceVacuum τ ω)
    (subalgebra_tracial τ ω hτ hω M hM)
    (subalgebra_faithful τ ω hτ M hM) (subalgebra_normalized τ ω M hone) f R
    (compressed τ ω T) c (β:ℂ)
    (small_represented_corner_bound τ ω hτ hω M hM Q j f hfQ T hb hc hβ hT)

end Kadison.TracialSequence

end

end
end

end OAI
