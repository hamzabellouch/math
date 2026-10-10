import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
namespace Coulomb
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [CompleteSpace E]
noncomputable def frameOperator (μ : Measure X) (v : X → E) : E →L[ℂ] E :=
  ∫ x, InnerProductSpace.rankOne ℂ (v x) (v x) ∂μ
omit [CompleteSpace E] in
lemma rankOne_self_continuous : Continuous (fun z : E => InnerProductSpace.rankOne ℂ z z) := by
  change Continuous (fun z : E => (innerSL ℂ z).smulRight z)
  exact (ContinuousLinearMap.smulRightL ℂ E E).continuous₂.comp₂
    (innerSL ℂ).continuous continuous_id
omit [CompleteSpace E] in
lemma rankOne_integrable {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ) :
    Integrable (fun x => InnerProductSpace.rankOne ℂ (v x) (v x)) μ := by
  have hm : AEStronglyMeasurable (fun x => InnerProductSpace.rankOne ℂ (v x) (v x)) μ :=
    rankOne_self_continuous.comp_aestronglyMeasurable hv.aestronglyMeasurable
  exact (hv.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)).mono' hm
    (Filter.Eventually.of_forall fun x => by simp [pow_two])
omit [CompleteSpace E] in
lemma frameOperator_apply {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ) (u : E) :
    frameOperator μ v u = ∫ x, inner ℂ (v x) u • v x ∂μ := by
  rw [frameOperator,ContinuousLinearMap.integral_apply (rankOne_integrable hv)]
  rfl
lemma frameOperator_inner {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ) (u w : E) :
    inner ℂ u (frameOperator μ v w) = ∫ x,inner ℂ u (v x)*inner ℂ (v x) w ∂μ := by
  have hi : Integrable (fun x => inner ℂ (v x) w • v x) μ :=
    (ContinuousLinearMap.apply ℂ E w).integrable_comp (rankOne_integrable hv)
  rw [frameOperator_apply hv]
  change (innerSL ℂ u) (∫ x,inner ℂ (v x) w • v x ∂μ) = _
  rw [←(innerSL ℂ u).integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [mul_comm]
lemma frameOperator_quadratic {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ) (u : E) :
    (inner ℂ u (frameOperator μ v u)).re = ∫ x,‖inner ℂ (v x) u‖^2 ∂μ := by
  have hi := ((innerSL ℂ u).comp (ContinuousLinearMap.apply ℂ E u)).integrable_comp
    (rankOne_integrable hv)
  have hi' : Integrable (fun x => inner ℂ u (v x)*inner ℂ (v x) u) μ := by
    simpa [ContinuousLinearMap.comp_apply,inner_smul_right,mul_comm] using hi
  rw [frameOperator_inner hv]
  change RCLike.re (∫ x,inner ℂ u (v x)*inner ℂ (v x) u ∂μ) = _
  rw [←integral_re hi']
  apply integral_congr_ae
  filter_upwards [] with x
  rw [←inner_conj_symm u (v x),←Complex.normSq_eq_conj_mul_self]
  exact (Complex.sq_norm _).symm
lemma frameOperator_nonneg {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ) (u : E) :
    0 ≤ (inner ℂ u (frameOperator μ v u)).re := by
  rw [frameOperator_quadratic hv]
  exact integral_nonneg (fun x => sq_nonneg _)
omit [CompleteSpace E] in
lemma rankOne_compact (v w : E) : IsCompactOperator (InnerProductSpace.rankOne ℂ v w) := by
  rw [InnerProductSpace.rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (ContinuousLinearMap.toSpanSingleton ℂ v)).comp_clm (innerSL ℂ w)
lemma integral_mem_closed_submodule {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {μ : Measure X} {f : X → F} (S : Submodule ℂ F)
    (hS : IsClosed (S : Set F)) (hf : Integrable f μ) (hmem : ∀ᵐ x ∂μ, f x ∈ S) :
    (∫ x,f x ∂μ) ∈ S := by
  let : Fact (IsClosed (S : Set F)) := ⟨hS⟩
  apply (Submodule.Quotient.mk_eq_zero S).mp
  change S.mkQL (∫ x,f x ∂μ) = 0
  rw [←S.mkQL.integral_comp_comm hf]
  apply integral_eq_zero_of_ae
  filter_upwards [hmem] with x hx
  exact (Submodule.Quotient.mk_eq_zero S).mpr hx
lemma frameOperator_compact {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ) :
    IsCompactOperator (frameOperator μ v) := by
  exact integral_mem_closed_submodule (compactOperator (RingHom.id ℂ) E E)
    isClosed_setOfPred_isCompactOperator (rankOne_integrable hv)
    (Filter.Eventually.of_forall fun x => rankOne_compact (v x) (v x))
lemma frameOperator_symmetric {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ) :
    (frameOperator μ v).toLinearMap.IsSymmetric := by
  intro u w
  change inner ℂ (frameOperator μ v u) w = inner ℂ u (frameOperator μ v w)
  rw [←inner_conj_symm (frameOperator μ v u) w,frameOperator_inner hv,frameOperator_inner hv]
  rw [←integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [map_mul,inner_conj_symm,mul_comm]
lemma frameOperator_positive {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ) :
    (frameOperator μ v).toLinearMap.IsPositive := by
  refine ⟨frameOperator_symmetric hv,fun u => ?_⟩
  change 0 ≤ RCLike.re (inner ℂ (frameOperator μ v u) u)
  rw [inner_re_symm]
  exact frameOperator_nonneg hv u
lemma id_sub_frameOperator_positive {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ)
    (hb : ∀ u, (∫ x,‖inner ℂ (v x) u‖^2 ∂μ) ≤ ‖u‖^2) :
    (ContinuousLinearMap.id ℂ E - frameOperator μ v).toLinearMap.IsPositive := by
  have hid : (LinearMap.id : E →ₗ[ℂ] E).IsSymmetric := fun _ _ => rfl
  refine ⟨hid.sub (frameOperator_symmetric hv),fun u => ?_⟩
  change 0 ≤ RCLike.re (inner ℂ (u-frameOperator μ v u) u)
  rw [inner_sub_left,map_sub,inner_self_eq_norm_sq_to_K]
  change 0 ≤ ((‖u‖ : ℂ)^2).re - (inner ℂ (frameOperator μ v u) u).re
  rw [← Complex.ofReal_pow, Complex.ofReal_re]
  change 0 ≤ ‖u‖^2 - RCLike.re (inner ℂ (frameOperator μ v u) u)
  rw [inner_re_symm]
  apply sub_nonneg.mpr
  change (inner ℂ u (frameOperator μ v u)).re ≤ ‖u‖^2
  rw [frameOperator_quadratic hv]
  exact hb u
end Coulomb

open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate

end

end OAI
