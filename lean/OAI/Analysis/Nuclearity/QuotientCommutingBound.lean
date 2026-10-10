import OAI.Analysis.OperatorAlgebra.StandardTensorCompression
import OAI.Analysis.OperatorAlgebra.CyclicStandardIntertwiner
import OAI.Analysis.Nuclearity.BoundedStarCompletion

namespace OAI

/-! A uniform bound for arbitrary commuting representations of a separable
quotient, obtained by the explicit two-GNS reduction to standard form. -/
noncomputable section
open Filter TopologicalSpace
open scoped ComplexOrder TensorProduct
namespace WeakPureInfiniteness
open BoundedRecovery KirchbergRordam.GenericRW.GroupedFactors

variable {A Q B H : Type*} [CStarAlgebra A] [CStarAlgebra Q] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder Q] [StarOrderedRing Q]
  [PartialOrder B] [StarOrderedRing B] [SeparableSpace Q]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma nuclear_quotient_coefficient_bound
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] Q) (hq : Function.Surjective q)
    (π : Q →⋆ₐ[ℂ] (H →L[ℂ] H)) (η : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hc : ∀ a b, Commute (π a) (η b)) (ξ : H) (hξ : ‖ξ‖ = 1)
    (z : Q ⊗[ℂ] B) :
    ‖inner ℂ ξ (Pureness.commutingStarTensorHom π η hc z ξ)‖ ≤
      36 * ‖minimalAlgebraicLinear z‖ := by
  obtain ⟨K, S, ρ, V, hS, hVn, hVξ, hV⟩ := exists_cyclic_standard_intertwiner π ξ hξ
  let L := standardTensorCompression ω hω hA q hq ρ π V hV η hc S hS
  have he : inner ℂ S.xi (L (minimalAlgebraicLinear z) S.xi) =
      inner ℂ ξ (Pureness.commutingStarTensorHom π η hc z ξ) := by
    rw [standardTensorCompression_algebraic]
    change inner ℂ S.xi (V.adjoint (Pureness.commutingStarTensorHom π η hc z (V S.xi))) = _
    rw [ContinuousLinearMap.adjoint_inner_right, hVξ]
  rw [← he]
  calc
    _ ≤ ‖S.xi‖ * ‖L (minimalAlgebraicLinear z) S.xi‖ := norm_inner_le_norm _ _
    _ ≤ ‖L (minimalAlgebraicLinear z)‖ := by
      rw [S.norm_xi, one_mul]
      simpa only [S.norm_xi, mul_one] using (L (minimalAlgebraicLinear z)).le_opNorm S.xi
    _ ≤ (4 * (‖V‖ * ‖V‖)) * ‖minimalAlgebraicLinear z‖ :=
      standardTensorCompression_norm_le ω hω hA q hq ρ π V hV η hc S hS _
    _ ≤ 36 * ‖minimalAlgebraicLinear z‖ := by
      have hn : ‖V‖ * ‖V‖ ≤ 9 := by
        calc
          _ ≤ (3 : ℝ) * 3 := mul_self_le_mul_self (norm_nonneg V) hVn
          _ = 9 := by norm_num
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg (minimalAlgebraicLinear z))
      nlinarith

lemma nuclear_quotient_commuting_algebraic_bound
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] Q) (hq : Function.Surjective q)
    (π : Q →⋆ₐ[ℂ] (H →L[ℂ] H)) (η : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hc : ∀ a b, Commute (π a) (η b)) (z : Q ⊗[ℂ] B) :
    ‖Pureness.commutingStarTensorHom π η hc z‖ ≤ 6 * ‖minimalAlgebraicLinear z‖ := by
  let χ := Pureness.commutingStarTensorHom π η hc
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (mul_nonneg (by norm_num) (norm_nonneg _))
  intro ξ hξ
  have h := nuclear_quotient_coefficient_bound ω hω hA q hq π η hc ξ hξ (star z * z)
  have he : ‖inner ℂ ξ (χ (star z * z) ξ)‖ = ‖χ z ξ‖ ^ 2 := by
    rw [map_mul, map_star]
    change ‖inner ℂ ξ ((χ z).adjoint (χ z ξ))‖ = _
    rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    simp
  rw [he, minimalAlgebraicLinear_mul, minimalAlgebraicLinear_star,
    CStarRing.norm_star_mul_self] at h
  nlinarith [norm_nonneg (χ z ξ), norm_nonneg (minimalAlgebraicLinear z)]

@[irreducible] def nuclearQuotientCommutingRepresentation
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] Q) (hq : Function.Surjective q)
    (π : Q →⋆ₐ[ℂ] (H →L[ℂ] H)) (η : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hc : ∀ a b, Commute (π a) (η b)) :
    MinimalTensor Q B →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
  boundedStarCompletion minimalAlgebraicMap
    (Pureness.commutingStarTensorHom π η hc).toNonUnitalStarAlgHom
    minimalAlgebraicMap_dense 6
    (fun z => by
      simpa only [StarAlgHom.coe_toNonUnitalStarAlgHom, minimalAlgebraicMap_apply] using
        nuclear_quotient_commuting_algebraic_bound ω hω hA q hq π η hc z)

lemma nuclearQuotientCommutingRepresentation_apply
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] Q) (hq : Function.Surjective q)
    (π : Q →⋆ₐ[ℂ] (H →L[ℂ] H)) (η : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hc : ∀ a b, Commute (π a) (η b)) (z : Q ⊗[ℂ] B) :
    nuclearQuotientCommutingRepresentation ω hω hA q hq π η hc (minimalAlgebraicMap z) =
      Pureness.commutingStarTensorHom π η hc z := by
  unfold nuclearQuotientCommutingRepresentation
  apply boundedStarCompletion_apply

lemma nuclearQuotientCommutingRepresentation_elementary
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] Q) (hq : Function.Surjective q)
    (π : Q →⋆ₐ[ℂ] (H →L[ℂ] H)) (η : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hc : ∀ a b, Commute (π a) (η b)) (a : Q) (b : B) :
    nuclearQuotientCommutingRepresentation ω hω hA q hq π η hc (minimalElementary a b) =
      π a * η b := by
  have h := nuclearQuotientCommutingRepresentation_apply ω hω hA q hq π η hc (a ⊗ₜ[ℂ] b)
  simpa only [minimalAlgebraicMap_tmul, Pureness.commutingStarTensorHom_tmul] using h

end WeakPureInfiniteness

end

end OAI
