import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

namespace OAI

/-! A cyclic representation is bounded by any C*-representation carrying
the same cyclic vector state. The source algebra need not carry a norm. -/

noncomputable section
open scoped InnerProductSpace ComplexOrder

namespace WeakPureInfiniteness

variable {A B H : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma cyclic_vector_norm_eq_preGNS (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (q : A →⋆ₐ[ℂ] B) (φ : B →ₚ[ℂ] ℂ) (ξ : H)
    (hφ : ∀ a, φ (q a) = inner ℂ ξ (π a ξ)) (b : A) :
    ‖π b ξ‖ = ‖φ.toPreGNS (q b)‖ := by
  rw [PositiveLinearMap.preGNS_norm_def,
    PositiveLinearMap.ofPreGNS_toPreGNS, ← map_star q, ← map_mul q, hφ]
  simp only [map_mul, map_star, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    ]
  have hnorm : (inner ℂ (π b ξ) (π b ξ)).re = ‖π b ξ‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) (π b ξ)
  rw [hnorm, Real.sqrt_sq (norm_nonneg _)]

theorem cyclic_representation_norm_le (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (q : A →⋆ₐ[ℂ] B) (φ : B →ₚ[ℂ] ℂ) (ξ : H)
    (hξ : DenseRange (fun a => π a ξ))
    (hφ : ∀ a, φ (q a) = inner ℂ ξ (π a ξ)) (a : A) :
    ‖π a‖ ≤ ‖q a‖ := by
  have hn := cyclic_vector_norm_eq_preGNS π q φ ξ hφ
  have hmul : ‖φ.leftMulMapPreGNS (q a)‖ ≤ ‖q a‖ := by
    unfold PositiveLinearMap.leftMulMapPreGNS
    exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
  refine (π a).opNorm_le_bound (norm_nonneg _) ?_
  refine isClosed_property hξ (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro b
  calc
    ‖π a (π b ξ)‖ = ‖π (a * b) ξ‖ := by rw [map_mul]; rfl
    _ = ‖φ.toPreGNS (q (a * b))‖ := hn (a * b)
    _ = ‖φ.leftMulMapPreGNS (q a) (φ.toPreGNS (q b))‖ := by
      simp only [map_mul, PositiveLinearMap.leftMulMapPreGNS_apply,
        PositiveLinearMap.ofPreGNS_toPreGNS]
    _ ≤ ‖φ.leftMulMapPreGNS (q a)‖ * ‖φ.toPreGNS (q b)‖ :=
      (φ.leftMulMapPreGNS (q a)).le_opNorm _
    _ ≤ ‖q a‖ * ‖φ.toPreGNS (q b)‖ :=
      mul_le_mul_of_nonneg_right hmul (norm_nonneg _)
    _ = ‖q a‖ * ‖π b ξ‖ := by rw [hn b]

end WeakPureInfiniteness

end

end OAI
