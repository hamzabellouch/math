import OAI.Analysis.BoundedHochschild.UltrapowerMoments

namespace OAI

/-! Passing coordinate moment limits to the actual tracial quotient. -/

noncomputable section
namespace KadisonSimilarity

open HochschildComparison HochschildPatching HochschildUltrapower BoundedHochschild
open TracialUltrapower Filter Topology
open scoped ComplexOrder BoundedContinuousFunction

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (τ : B →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
  (tr : ∀ a b, τ (a * b) = τ (b * a))

/-- All bounded finite words in the centered coefficient family vanish. -/
def FiniteQuotientMoments (A : ℕ → (ℕ →ᵇ B)) (u : ℕ → unitary B) : Prop :=
  ∀ m K N : ℕ, ∀ a : BoundedWord (Fin m) K N, admissibleTail a.2.val →
    quotientTrace τ h1 ω tr (mixedEval
      (fun i : Fin m => quotientHom τ h1 ω tr (A i.val) -
        quotientTrace τ h1 ω tr (quotientHom τ h1 ω tr (A i.val)) • 1)
      (asPartialUnitary (quotientUnitary τ h1 ω tr u)) a.1 a.2.val) = 0

/-- Every admissible mixed word in an indexed coefficient family vanishes. -/
def AllQuotientMoments {I : Type*} (A : I → (ℕ →ᵇ B)) (u : ℕ → unitary B) : Prop :=
  ∀ K : ℕ, ∀ a : Option I, ∀ l : List (WordAtom I K), admissibleTail l →
    quotientTrace τ h1 ω tr (mixedEval
      (fun i => quotientHom τ h1 ω tr (A i) -
        quotientTrace τ h1 ω tr (quotientHom τ h1 ω tr (A i)) • 1)
      (asPartialUnitary (quotientUnitary τ h1 ω tr u)) a l) = 0

/-- The quotient step uses only the coordinate limits, with no factor or
freeness assumption. -/
theorem finiteQuotientMoments_of_limits (hω : (ω : Filter ℕ) ≤ atTop)
    (A : ℕ → (ℕ →ᵇ B)) (u : ℕ → unitary B)
    (hu : ∀ m K N : ℕ, ∀ a : BoundedWord (Fin m) K N, admissibleTail a.2.val →
      Tendsto (fun n => τ (mixedEval
        (fun i : Fin m => (1 / 2 : ℂ) • (A i.val n - τ (A i.val n) • 1))
        (asPartialUnitary (u n)) a.1 a.2.val)) atTop (𝓝 0)) :
    FiniteQuotientMoments τ h1 ω tr A u := by
  intro m K N a ha
  let D : Fin m → (ℕ →ᵇ B) := fun i => (1 / 2 : ℂ) • centeredSequence τ (A i.val)
  let x : ℕ →ᵇ B := mixedEval D (asPartialUnitary (unitarySequence u)) a.1 a.2.val
  have hx : sequenceTrace τ ω x = 0 := by
    apply tendsto_nhds_unique (tendsto_sequenceTrace τ h1 ω x)
    have hh := (hu m K N a ha).mono_left hω
    convert hh using 1
    funext n
    change τ (mixedEval D (asPartialUnitary (unitarySequence u)) a.1 a.2.val n) = _
    rw [mixedEval_sequence]
    rfl
  let C : Fin m → Ultrapower τ h1 ω tr := fun i => quotientHom τ h1 ω tr (A i.val) -
    quotientTrace τ h1 ω tr (quotientHom τ h1 ω tr (A i.val)) • 1
  have hD : quotientHom τ h1 ω tr ∘ D = fun i => (1 / 2 : ℂ) • C i := by
    funext i
    change quotientHom τ h1 ω tr ((1 / 2 : ℂ) • centeredSequence τ (A i.val)) = _
    rw [map_smul, quotient_centeredSequence]
  have hm : mapUnitary (quotientHom τ h1 ω tr) (unitarySequence u) =
      quotientUnitary τ h1 ω tr u := rfl
  have ht : quotientTrace τ h1 ω tr (quotientHom τ h1 ω tr x) = 0 := hx
  change quotientTrace τ h1 ω tr (quotientHom τ h1 ω tr
    (mixedEval D (asPartialUnitary (unitarySequence u)) a.1 a.2.val)) = 0 at ht
  rw [mixedEval_hom, hD, hm, mixedEval_smul, map_smul, smul_eq_mul] at ht
  exact (mul_eq_zero.mp ht).resolve_left (pow_ne_zero _ (by norm_num))

end KadisonSimilarity

end

end OAI
