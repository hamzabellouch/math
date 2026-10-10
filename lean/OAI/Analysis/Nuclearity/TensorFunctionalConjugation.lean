import OAI.Analysis.Nuclearity.NuclearTensorFunctional

namespace OAI

/-! The finite algebraic conjugation formula in KR02 Lemma 7.18. This is an
identity for the constructed continuous positive tensor functional. -/

noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder InnerProductSpace

namespace WeakPureInfiniteness

variable {B C H I : Type*} [NonUnitalCStarAlgebra B] [CStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Fintype I]


omit [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C] in
lemma minimalTensor_sum_selfAdjoint (x : I → B) (y : I → C)
    (hx : ∀ i, IsSelfAdjoint (x i)) (hy : ∀ i, IsSelfAdjoint (y i)) :
    IsSelfAdjoint (∑ i, minimalElementary (x i) (y i)) := by
  change star (∑ i, minimalElementary (x i) (y i)) = _
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← minimalElementary_star, (hx i).star_eq, (hy i).star_eq]

omit [Fintype I] [PartialOrder C] [StarOrderedRing C] in
lemma commuting_operator_inner_split (F : H →L[ℂ] H)
    (η : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ c, Commute F (η c))
    (ξ : H) (a c b : C) :
    ⟪ξ, F (η (star a * c * b) ξ)⟫_ℂ =
      ⟪η a ξ, F (η c (η b ξ))⟫_ℂ := by
  have he := congrArg (fun T : H →L[ℂ] H => T (η c (η b ξ))) (hc (star a)).eq
  simp only [mul_apply_eq_comp] at he
  simp only [map_mul, mul_apply_eq_comp]
  rw [he, map_star, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

lemma nuclearTensorFunctional_finite_conjugation (hB : Nuclear B)
    (f : B →L[ℂ] (H →L[ℂ] H)) (hf : CompletelyPositive f)
    (η : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ b c, Commute (f b) (η c))
    (ξ : H) (x : I → B) (y : I → C) (b : B) (c : C) :
    nuclearTensorFunctional hB f hf η hc ξ
        (star (∑ i, minimalElementary (x i) (y i)) * minimalElementary b c *
          (∑ j, minimalElementary (x j) (y j))) =
      ∑ i, ∑ j, ⟪ξ, f (star (x i) * b * x j)
        (η (star (y i) * c * y j) ξ)⟫_ℂ := by
  simp only [star_sum, Finset.sum_mul, Finset.mul_sum, ← minimalElementary_star,
    ← minimalElementary_mul, map_sum, nuclearTensorFunctional_elementary]
  exact Finset.sum_comm

lemma nuclearTensorFunctional_finite_conjugation_vectors (hB : Nuclear B)
    (f : B →L[ℂ] (H →L[ℂ] H)) (hf : CompletelyPositive f)
    (η : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ b c, Commute (f b) (η c))
    (ξ : H) (x : I → B) (y : I → C) (b : B) (c : C) :
    nuclearTensorFunctional hB f hf η hc ξ
        (star (∑ i, minimalElementary (x i) (y i)) * minimalElementary b c *
          (∑ j, minimalElementary (x j) (y j))) =
      ∑ i, ∑ j, ⟪η (y i) ξ, f (star (x i) * b * x j)
        (η c (η (y j) ξ))⟫_ℂ := by
  rw [nuclearTensorFunctional_finite_conjugation]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact commuting_operator_inner_split _ η (hc _) ξ _ _ _

end WeakPureInfiniteness

end

end OAI
