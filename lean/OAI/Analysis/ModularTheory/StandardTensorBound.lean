import OAI.Analysis.ModularTheory.OperatorTensorBound
import OAI.Analysis.ModularTheory.OriginalNorm
import OAI.Analysis.OperatorAlgebra.LpTensorFunctoriality

namespace OAI

/-! The finite tracial core estimates imply the original standard-form tensor
bound. Only the supplied nuclear algebra and its quotient are used. -/
noncomputable section
open MeasureTheory Filter
open scoped TensorProduct ComplexOrder
namespace WeakPureInfiniteness
open BoundedRecovery KirchbergRordam.GenericRW.GroupedFactors

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def modularLpOppositeRepresentation (D : RealSpectralCalculus H) :
    (H →L[ℂ] H)ᵐᵒᵖ →⋆ₐ[ℂ]
      (Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))ᵐᵒᵖ where
  __ := (modularLpRepresentation volume D).toAlgHom.op
  map_star' a := congrArg MulOpposite.op (map_star (modularLpRepresentation volume D) a.unop)

lemma modularLpOppositeRepresentation_injective (D : RealSpectralCalculus H) :
    Function.Injective (modularLpOppositeRepresentation D) := by
  intro a b h
  apply MulOpposite.unop_injective
  apply modularLpRepresentation_injective D
  exact congrArg MulOpposite.unop h

lemma modularLp_minimal_sum_norm_le (D : RealSpectralCalculus H)
    {I : Type*} [Fintype I] (a b : I → H →L[ℂ] H) :
    ‖∑ i, minimalElementary (canonicalLpOperator (modularLpRepresentation volume D (a i)))
      (MulOpposite.op (canonicalLpOperator (modularLpRepresentation volume D (b i))))‖ ≤
    ‖∑ i, minimalElementary (a i) (MulOpposite.op (b i))‖ := by
  exact lp_norm_minimalSum_map_le
    (modularLpRepresentation volume D).toNonUnitalStarAlgHom
    (modularLpOppositeRepresentation D).toNonUnitalStarAlgHom
    a (fun i => MulOpposite.op (b i))

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A]

lemma nuclear_quotient_modular_coefficients_bound
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : StandardModularData H)
    (hS : S.M = bicommutant π.range) {I : Type*} [Fintype I]
    (a b : I → S.M.toStarSubalgebra) :
    ‖canonicalLpOperator (∑ i, modularLpRepresentation volume S.D (a i).val *
      modularTracialRightAction S (modularLpRepresentation volume S.D (b i).val))‖ ≤
    ‖∑ i, minimalElementary (canonicalLpOperator (modularLpRepresentation volume S.D (a i).val))
      (MulOpposite.op (canonicalLpOperator (modularLpRepresentation volume S.D (b i).val)))‖ :=
  nuclear_quotient_modular_operator_bound ω hω hA q hq π S hS
    (fun i => modularLpRepresentation volume S.D (a i).val)
    (fun i => modularLpRepresentation volume S.D (b i).val)
    (fun i => modularCrossedProduct_coeff volume S (a i))
    (fun i => modularCrossedProduct_coeff volume S (b i))

theorem nuclear_quotient_standard_tensor_sum_bound
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : StandardModularData H)
    (hS : S.M = bicommutant π.range) {I : Type*} [Fintype I]
    (a b : I → S.M.toStarSubalgebra) :
    ‖∑ i, (a i).val * antiunitaryConjugate S.J (star (b i).val)‖ ≤
      ‖∑ i, minimalElementary (a i).val (MulOpposite.op (b i).val)‖ := by
  have he := norm_le_canonicalLpOperator
    (∑ i, modularLpRepresentation volume S.D (a i).val *
      modularTracialRightAction S (modularLpRepresentation volume S.D (b i).val))
    (modularRight_product_sum_norm_ge S (fun i => (a i).val) (fun i => (b i).val))
  exact (he.trans (nuclear_quotient_modular_coefficients_bound ω hω hA q hq π S hS a b)).trans
    (modularLp_minimal_sum_norm_le S.D (fun i => (a i).val) (fun i => (b i).val))

end WeakPureInfiniteness

end

end OAI
