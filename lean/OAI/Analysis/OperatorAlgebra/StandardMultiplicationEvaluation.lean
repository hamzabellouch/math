import OAI.Analysis.OperatorAlgebra.StandardMinimalMultiplication

namespace OAI

/-! Evaluation of the completed standard-form tensor representation. -/
noncomputable section
open Filter
open scoped TensorProduct
namespace WeakPureInfiniteness
open BoundedRecovery KirchbergRordam.GenericRW.GroupedFactors

variable {A B H : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local irreducible] standardAlgebraicMultiplication

lemma nuclearQuotientStandardMultiplication_apply
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : StandardModularData H)
    (hS : S.M = bicommutant π.range)
    (z : S.M.toStarSubalgebra ⊗[ℂ] S.M.toStarSubalgebraᵐᵒᵖ) :
    nuclearQuotientStandardMultiplication ω hω hA q hq π S hS (minimalAlgebraicLinear z) =
      standardAlgebraicMultiplication S z := by
  unfold nuclearQuotientStandardMultiplication
  have h := denseLinearStarCompletion_apply minimalAlgebraicLinear
    (standardAlgebraicLinear S) minimalAlgebraicLinear_dense
    (subalgebraAlgebraicLinear_mul S.M) (map_mul (standardAlgebraicMultiplication S))
    (subalgebraAlgebraicLinear_star S.M) (map_star (standardAlgebraicMultiplication S))
    (nuclear_quotient_standard_algebraic_bound ω hω hA q hq π S hS) z
  simpa only [standardAlgebraicLinear_apply] using h

lemma nuclearQuotientStandardMultiplication_elementary
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : StandardModularData H)
    (hS : S.M = bicommutant π.range)
    (a : S.M.toStarSubalgebra) (b : S.M.toStarSubalgebraᵐᵒᵖ) :
    nuclearQuotientStandardMultiplication ω hω hA q hq π S hS (minimalElementary a b) =
      a.val * antiunitaryConjugate S.J (star b.unop.val) := by
  exact (nuclearQuotientStandardMultiplication_apply ω hω hA q hq π S hS
    (a ⊗ₜ[ℂ] b)).trans (standardAlgebraicMultiplication_tmul S a b)

end WeakPureInfiniteness

end

end OAI
