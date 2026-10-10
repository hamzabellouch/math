import OAI.Analysis.ModularTheory.CornerRepresentedBound
import OAI.Analysis.OperatorAlgebra.TracialCanonicalCornerBound
import OAI.Analysis.OperatorAlgebra.CanonicalLpOperations
import OAI.Analysis.OperatorAlgebra.StrongCompressionBound

namespace OAI

/-! Finite tracial estimates pass through the actual GNS corner inclusions
and the strongly exhausting two-sided projections. -/
noncomputable section
open MeasureTheory Filter
open scoped TensorProduct ComplexOrder Topology
namespace WeakPureInfiniteness
open BoundedRecovery KirchbergRordam.GenericRW.GroupedFactors

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
attribute [local irreducible] modularCompressedCorner modularCompressedTracialState

lemma modularCoreCompression_product_sum (S : StandardModularData H) (n : ℕ)
    {I : Type*} [Fintype I]
    (a b : I → (modularCrossedProduct (volume : Measure ℝ) S).toStarSubalgebra) :
    (modularTracialCornerProjection S (n + 1) *
      (∑ i, ((a i).val : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) * modularTracialRightAction S (b i).val) *
        modularTracialCornerProjection S (n + 1) :
      Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) =
    ∑ i, (isometricCornerLift (modularCornerInclusion (H := H) (n + 1))
        (modularCoreCompression S (n + 1) (a i).val (a i).property).val :
        Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) *
      modularTracialRightAction S
        (isometricCornerLift (modularCornerInclusion (H := H) (n + 1))
          (modularCoreCompression S (n + 1) (b i).val (b i).property).val) := by
  classical
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [modularCoreCompression_lift, modularCoreCompression_lift]
  exact modularTracialCornerProjection_compress S (n + 1) _ _ (a i).property (b i).property

abbrev modularCoreCompression_minimal_sum_bound (S : StandardModularData H) (n : ℕ)
    {I : Type*} [Fintype I]
    (a b : I → (modularCrossedProduct (volume : Measure ℝ) S).toStarSubalgebra) :=
  norm_minimalSum_corner_compression (modularCompressedCorner S (n + 1))
    (modularCornerInclusion (H := H) (n + 1)) (modularFiniteProjection (H := H) (n + 1))
    (modularFiniteProjection_norm_le (n + 1)) (fun i => (a i).val) (fun i => (b i).val)
    (fun i => modularCoreCompression S (n + 1) (a i).val (a i).property)
    (fun i => modularCoreCompression S (n + 1) (b i).val (b i).property)
    (fun i => modularCoreCompression_lift S (n + 1) (a i).val (a i).property)
    (fun i => modularCoreCompression_lift S (n + 1) (b i).val (b i).property)

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A]

private abbrev modular_lifted_compressed_sum_proof
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : StandardModularData H)
    (hS : S.M = bicommutant π.range) (n : ℕ) {I : Type*} [Fintype I]
    (a b : I → (modularCrossedProduct (volume : Measure ℝ) S).toStarSubalgebra) :=
  tracial_canonical_lp_corner_sum_bound
    (J := H)
    (K := ModularCornerHilbert (H := H) (n + 1))
    (modularCompressedCorner S (n + 1)) (modularCompressedTracialState S n)
    (nuclear_quotient_modular_corner_expectation ω hω hA q hq π S hS (n + 1))
    (modularCornerGNSInclusion S n)
    (fun a => isometricCornerLift (modularCornerInclusion (H := H) (n + 1)) a.val)
    (fun b => modularTracialRightAction S
      (isometricCornerLift (modularCornerInclusion (H := H) (n + 1)) b.val))
    (modularCornerGNSInclusion_left S n) (modularCornerGNSInclusion_right S n)
    (fun a b => by
      rw [← modularCornerGNSInclusion_projection]
      exact modularCornerProduct_right_support S (n + 1) a b)
    (modularCornerInclusion (H := H) (n + 1)) (modularFiniteProjection (H := H) (n + 1))
    (modularFiniteProjection_norm_le (n + 1)) (fun i => (a i).val) (fun i => (b i).val)
    (fun i => modularCoreCompression S (n + 1) (a i).val (a i).property)
    (fun i => modularCoreCompression S (n + 1) (b i).val (b i).property)
    (fun i => modularCoreCompression_lift S (n + 1) (a i).val (a i).property)
    (fun i => modularCoreCompression_lift S (n + 1) (b i).val (b i).property)

private theorem modular_lifted_compressed_sum_bound
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : StandardModularData H)
    (hS : S.M = bicommutant π.range) (n : ℕ) {I : Type*} [Fintype I]
    (a b : I → (modularCrossedProduct (volume : Measure ℝ) S).toStarSubalgebra) :
    type_of% (modular_lifted_compressed_sum_proof ω hω hA q hq π S hS n a b) :=
  modular_lifted_compressed_sum_proof ω hω hA q hq π S hS n a b

lemma nuclear_quotient_modular_compressed_sum_bound
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : StandardModularData H)
    (hS : S.M = bicommutant π.range) (n : ℕ) {I : Type*} [Fintype I]
    (a b : I → (modularCrossedProduct (volume : Measure ℝ) S).toStarSubalgebra) :
    ‖canonicalLpOperator (modularTracialCornerProjection S (n + 1) *
      (∑ i, (a i).val * modularTracialRightAction S (b i).val) *
        modularTracialCornerProjection S (n + 1))‖ ≤
    ‖∑ i, minimalElementary (canonicalLpOperator (a i).val)
      (MulOpposite.op (canonicalLpOperator (b i).val))‖ := by
  rw [modularCoreCompression_product_sum, canonicalLpOperator_sum]
  simp only [canonicalLpOperator_mul]
  exact modular_lifted_compressed_sum_bound ω hω hA q hq π S hS n a b

theorem nuclear_quotient_modular_finite_sum_bound
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : StandardModularData H)
    (hS : S.M = bicommutant π.range) {I : Type*} [Fintype I]
    (a b : I → (modularCrossedProduct (volume : Measure ℝ) S).toStarSubalgebra) :
    ‖canonicalLpOperator (∑ i, (a i).val * modularTracialRightAction S (b i).val)‖ ≤
      ‖∑ i, minimalElementary (canonicalLpOperator (a i).val)
        (MulOpposite.op (canonicalLpOperator (b i).val))‖ := by
  apply norm_le_of_strong_compression_bound atTop
    (fun n => canonicalLpOperator (modularTracialCornerProjection S (n + 1)))
    (fun n => by rw [canonicalLpOperator_norm]; exact modularTracialCornerProjection_norm_le S (n + 1))
    (fun x => by
      simpa only [canonicalLpOperator_apply, Function.comp_def] using
        (modularTracialCornerProjection_strong S x).comp (tendsto_add_atTop_nat 1))
    _ (norm_nonneg _)
  intro n
  have h := nuclear_quotient_modular_compressed_sum_bound ω hω hA q hq π S hS n a b
  simpa only [canonicalLpOperator_mul] using h

end WeakPureInfiniteness

end

end OAI
