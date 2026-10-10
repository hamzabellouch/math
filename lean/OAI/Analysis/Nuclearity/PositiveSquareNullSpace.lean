import OAI.Analysis.Nuclearity.PositiveConeNullIdeal

namespace OAI

/-! The closed linear left kernel used at the end of KR02 Lemma 7.18.
The elementary-span hypothesis for the tensor ideal supplies the
passage from elementary generators to its closure. -/

noncomputable section
open scoped ComplexOrder

namespace WeakPureInfiniteness

variable {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

def positiveSquareNullSpace (φ : D →ₚ[ℂ] ℂ) : Submodule ℂ D where
  carrier := {x | φ (star x * x) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    exact commonSquareNull_add {φ} (by simpa [commonSquareNull] using hx)
      (by simpa [commonSquareNull] using hy) φ (Set.mem_singleton φ)
  smul_mem' := by
    intro c x hx
    exact commonSquareNull_smul {φ} (by simpa [commonSquareNull] using hx) c
      φ (Set.mem_singleton φ)

lemma positiveSquareNullSpace_closed (φ : D →ₚ[ℂ] ℂ) :
    IsClosed (positiveSquareNullSpace φ : Set D) :=
  isClosed_eq ((map_continuous φ).comp (continuous_star.mul continuous_id)) continuous_const

lemma positiveFunctional_square_null_of_closure_span (φ : D →ₚ[ℂ] ℂ)
    (S : Set D) (hS : ∀ x ∈ S, φ (star x * x) = 0) {z : D}
    (hz : z ∈ closure (Submodule.span ℂ S : Set D)) : φ (star z * z) = 0 := by
  have hs : Submodule.span ℂ S ≤ positiveSquareNullSpace φ := Submodule.span_le.mpr hS
  exact closure_minimal hs (positiveSquareNullSpace_closed φ) hz

/-- The last nullspace step of the published proof. The witness may depend on
the elementary generator, as it does for the positive element x* x in KR02. -/
lemma common_nullspace_inclusion_of_elementary_span
    (K : Set (D →ₚ[ℂ] ℂ))
    (hconj : ∀ φ ∈ K, ∀ d : D, conjugatePositiveFunctional φ d ∈ K)
    (S : Set D)
    (hspan : ((commonSquareNullIdeal K hconj).module : Set D) ⊆
      closure (Submodule.span ℂ S : Set D))
    (hS : S ⊆ (commonSquareNullIdeal K hconj).module)
    (φ₀ : D →ₚ[ℂ] ℂ)
    (hfix : ∀ x ∈ S, ∃ φ ∈ K, φ₀ (star x * x) = φ (star x * x)) :
    ∀ x, commonSquareNull K x → φ₀ (star x * x) = 0 := by
  intro x hx
  apply positiveFunctional_square_null_of_closure_span φ₀ S _ (hspan hx)
  intro z hz
  obtain ⟨φ, hφ, he⟩ := hfix z hz
  exact he.trans (hS hz φ hφ)

end WeakPureInfiniteness

end

end OAI
