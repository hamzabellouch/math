import OAI.Analysis.PureInfiniteness.CountableAbelianization
import OAI.Analysis.Nuclearity.PositiveSpanningSequence
import OAI.Analysis.PureInfiniteness.InnerHomCompression

namespace OAI

/-! The abelian-range extension of KR02 Proposition 7.13, stated using the
inclusion homomorphisms of the separable algebras. It provides an actual
one-step inner map in the norm ultrapower. -/

noncomputable section
open Filter

namespace WeakPureInfiniteness

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCommCStarAlgebra C] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

theorem exists_abelian_range_compression (hP : MainGap.PropertyP A)
    (β : B →⋆ₙₐ[ℂ] N) (γ : C →⋆ₙₐ[ℂ] N) :
    ∃ v : N, ‖v‖ ≤ 1 ∧ (∀ c, star v * γ c * v = γ c) ∧
      ∀ x y, Commute (star v * β x * v) (star v * β y * v) := by
  obtain ⟨p, hp⟩ := exists_dense_positive_sequence (D := C)
  obtain ⟨q, hq⟩ := exists_dense_positive_sequence (D := B)
  obtain ⟨v, hv, hfix, _, hpair⟩ := ultrapower_countable_positive_abelianization U hP
    (fun i => γ (p i)) (fun i => β (q i))
    (fun i => map_nonneg γ (p i).property) (fun i => map_nonneg β (q i).property)
    (fun i j => (Commute.all (p i : C) (p j : C)).map γ)
  have hmaps : innerHomCompression γ v = starHomContinuousLinear γ :=
    continuousLinearMap_ext_positive_sequence p hp _ _ hfix
  refine ⟨v, hv, ?_, ?_⟩
  · intro c
    exact congrArg (fun f : C →L[ℂ] N => f c) hmaps
  · exact abelian_range_of_positive_sequence q hq (innerHomCompression β v) hpair

/-- The completely positive contraction accompanying the actual compressor. -/
theorem abelian_range_extension_cpc (hP : MainGap.PropertyP A)
    (β : B →⋆ₙₐ[ℂ] N) (γ : C →⋆ₙₐ[ℂ] N) :
    ∃ v : N, ∃ T : B →L[ℂ] N,
      ‖v‖ ≤ 1 ∧ (∀ b, T b = star v * β b * v) ∧
      CompletelyPositive T ∧ ‖T‖ ≤ 1 ∧
      (∀ c, star v * γ c * v = γ c) ∧ ∀ x y, Commute (T x) (T y) := by
  obtain ⟨v, hv, hfix, hpair⟩ := exists_abelian_range_compression U hP β γ
  exact ⟨v, innerHomCompression β v, hv, fun _ => rfl,
    innerHomCompression_cp β v, innerHomCompression_norm_le β v hv, hfix, hpair⟩

end WeakPureInfiniteness

end

end OAI
