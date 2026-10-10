import OAI.Analysis.ModularTheory.CornerTensorBound

namespace OAI

/-! The full modular tensor estimate with operator-valued coefficients. -/
noncomputable section
open MeasureTheory Filter
open scoped TensorProduct ComplexOrder
namespace WeakPureInfiniteness
open BoundedRecovery KirchbergRordam.GenericRW.GroupedFactors
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A]

lemma nuclear_quotient_modular_operator_bound
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : StandardModularData H)
    (hS : S.M = bicommutant π.range) {I : Type*} [Fintype I]
    (a b : I → Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (ha : ∀ i, a i ∈ modularCrossedProduct volume S)
    (hb : ∀ i, b i ∈ modularCrossedProduct volume S) :
    ‖canonicalLpOperator (∑ i, a i * modularTracialRightAction S (b i))‖ ≤
      ‖∑ i, minimalElementary (canonicalLpOperator (a i))
        (MulOpposite.op (canonicalLpOperator (b i)))‖ :=
  nuclear_quotient_modular_finite_sum_bound ω hω hA q hq π S hS
    (fun i => ⟨a i, ha i⟩) (fun i => ⟨b i, hb i⟩)

end WeakPureInfiniteness

end

end OAI
