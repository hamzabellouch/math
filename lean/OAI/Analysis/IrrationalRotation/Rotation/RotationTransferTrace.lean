import OAI.Analysis.IrrationalRotation.Analysis.FieldMultiplierCutoff
import OAI.Analysis.IrrationalRotation.Rotation.RotationMeasurable
import OAI.Analysis.IrrationalRotation.Rotation.RotationTransfer
import OAI.Analysis.IrrationalRotation.Rotation.RotationTrace
import OAI.Analysis.IrrationalRotation.Operators.AffiliatedTraceCutoffs

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology NNReal

namespace Invariant233.Rotation

open WeightedShift.SpectralCutoff

theorem boundedOperator_orbit_mem_algebra
    (θ : ℝ) (g : Circle → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun x => g (action θ k x)) circleMeasure) :
    boundedOperator (fun x k => g (action θ k x)) C hC
      (fun x k => hb (action θ k x)) hm ∈ algebra θ := by
  have heq : boundedOperator (fun x k => g (action θ k x)) C hC
      (fun x k => hb (action θ k x)) hm =
      measurableRepresentation θ g C hC hg hb := by
    apply operator_ext_of_coordinates
    intro ξ
    filter_upwards [boundedOperator_ae (fun x k => g (action θ k x)) C hC
      (fun x k => hb (action θ k x)) hm ξ,
      measurableRepresentation_coordinates_ae θ g C hC hg hb ξ] with x hx hy
    intro k
    exact (hx k).trans (hy k).symm
  rw [heq]
  exact measurableRepresentation_mem_algebra θ g C hC hg hb

theorem exponentialTransfer_cutoff_mem_algebra
    (θ : ℝ) {b : Circle → ℝ} (hb : Measurable b) (n : ℕ) :
    projection (fun x k => Real.exp (b (action θ k x)))
      (exponentialTransfer_coefficient_measurable θ hb) n ∈ algebra θ := by
  apply boundedOperator_orbit_mem_algebra θ (fun x => symbol n (Real.exp (b x)))
  · exact ((measurable_const.indicator measurableSet_Icc).comp hb.exp)
  · exact fun x => norm_symbol_le n _

theorem exponentialTransfer_cutoffProduct_mem_algebra
    (θ : ℝ) {b : Circle → ℝ} (hb : Measurable b) (n : ℕ) :
    productOperator (fun x k => Real.exp (b (action θ k x)))
      (exponentialTransfer_coefficient_measurable θ hb) n ∈ algebra θ := by
  apply boundedOperator_orbit_mem_algebra θ (fun x => productSymbol n (Real.exp (b x)))
  · exact (Complex.measurable_ofReal.comp hb.exp).mul
      ((measurable_const.indicator measurableSet_Icc).comp hb.exp)
  · exact fun x => norm_productSymbol_le n _

theorem exponentialTransfer_inverseCutoffProduct_mem_algebra
    (θ : ℝ) {b : Circle → ℝ} (hb : Measurable b) (n : ℕ) :
    inverseOperator (fun x k => Real.exp (b (action θ k x)))
      (exponentialTransfer_coefficient_measurable θ hb) n ∈ algebra θ := by
  apply boundedOperator_orbit_mem_algebra θ (fun x => inverseSymbol n (Real.exp (b x)))
  · exact (Complex.measurable_ofReal.comp hb.exp.inv).mul
      ((measurable_const.indicator measurableSet_Icc).comp hb.exp)
  · exact fun x => norm_inverseSymbol_le n _

theorem exponentialTransfer_transported_vectorTrace
    (θ : ℝ) {b : Circle → ℝ} (hb : Measurable b)
    (p : Submodule ℂ Hilbert) [CompleteSpace p]
    (hp : p.starProjection ∈ algebra θ) :
    vectorTrace vacuum
      (InvariantRotation.AffiliatedTransport.transported (exponentialTransfer θ b) p).starProjection =
      vectorTrace vacuum p.starProjection := by
  let h : Circle → ℤ → ℝ := fun x k => Real.exp (b (action θ k x))
  let hm : ∀ k, Measurable (fun x => h x k) := exponentialTransfer_coefficient_measurable θ hb
  let E : ℕ → Submodule ℂ Hilbert := fun n => cutoffSpace (μ := circleMeasure) h hm n
  let (n : ℕ) : CompleteSpace ↥(E n) := by
    exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hpos : ∀ᵐ x ∂circleMeasure, ∀ k, 0 < h x k :=
    Eventually.of_forall fun _ _ => Real.exp_pos _
  have hEM (n : ℕ) : (E n).starProjection ∈ algebra θ := by
    rw [show (E n).starProjection = projection h hm n from cutoffSpace_starProjection h hm n]
    exact exponentialTransfer_cutoff_mem_algebra θ hb n
  have hED (n : ℕ) : E n ≤ (exponentialTransfer θ b).domain :=
    (cutoffSpace_le_domains h hm n).1
  have hiED (n : ℕ) : E n ≤ (exponentialTransfer θ b).inverse.domain :=
    (cutoffSpace_le_domains h hm n).2
  have hξ := vacuum_faithfulTracial θ
  have hsym : (exponentialTransfer θ b).IsFormalAdjoint (exponentialTransfer θ b) := by
    have hs := LinearPMap.adjoint_isFormalAdjoint (exponentialTransfer_selfAdjoint θ hb).dense_domain
    rw [LinearPMap.isSelfAdjoint_def.mp (exponentialTransfer_selfAdjoint θ hb)] at hs
    exact hs
  have hker : (exponentialTransfer θ b).toFun.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr (exponentialTransfer_injective θ b)
  have hr (n : ℕ) (x : E n) :
      (x : Hilbert) ∈ (projection (μ := circleMeasure) h hm n).range := by
    have hx : (x : Hilbert) ∈ cutoffSpace (μ := circleMeasure) h hm n := x.property
    rw [cutoffSpace_eq_range] at hx
    exact hx
  have hF (n : ℕ) (x : E n) :
      exponentialTransfer θ b ⟨x, hED n x.property⟩ =
        productOperator (μ := circleMeasure) h hm n x := by
    exact multiplier_on_range (μ := circleMeasure) h hm n ⟨x, hr n x⟩
  have hG (n : ℕ) (x : E n) :
      (exponentialTransfer θ b).inverse ⟨x, hiED n x.property⟩ =
        inverseOperator (μ := circleMeasure) h hm n x := by
    exact inverse_multiplier_on_range (μ := circleMeasure) h hm hpos n ⟨x, hr n x⟩
  have hLower (n : ℕ) (x : E n) :
      ‖x‖ ≤ (n + 1 : ℝ≥0) * ‖productOperator (μ := circleMeasure) h hm n x‖ := by
    have hx := (multiplier_range_bounds (μ := circleMeasure) h hm n ⟨x, hr n x⟩).2
    rw [multiplier_on_range] at hx
    exact hx
  have hInvLower (n : ℕ) (x : E n) :
      ‖x‖ ≤ (n + 1 : ℝ≥0) * ‖inverseOperator (μ := circleMeasure) h hm n x‖ := by
    have hx := (inverse_multiplier_range_bounds (μ := circleMeasure) h hm hpos n ⟨x, hr n x⟩).2
    rw [inverse_multiplier_on_range h hm hpos] at hx
    exact hx
  exact AffiliatedTraceCutoffs.vectorTrace_transported_eq_of_cutoffs
    (algebra θ) vacuum hξ (exponentialTransfer θ b) hsym hker p hp E hEM
    (cutoffSpace_tendsto h hm hpos vacuum) hED hiED
    (productOperator h hm) (inverseOperator h hm)
    (exponentialTransfer_cutoffProduct_mem_algebra θ hb)
    (exponentialTransfer_inverseCutoffProduct_mem_algebra θ hb)
    hF hG (fun n => n + 1) (fun n => n + 1) hLower hInvLower

theorem exponentialTransfer_projection_trace
    (θ : ℝ) {b : Circle → ℝ} (hb : Measurable b)
    (p : Hilbert →L[ℂ] Hilbert) (hp : p ∈ algebra θ) (hpP : IsStarProjection p) :
    vectorTrace vacuum
      (InvariantRotation.AffiliatedTransport.transported (exponentialTransfer θ b) p.range).starProjection =
      vectorTrace vacuum p := by
  let : CompleteSpace p.range := (ContinuousLinearMap.IsIdempotentElem.isClosed_range hpP.isIdempotentElem).completeSpace_coe
  obtain ⟨hi, he⟩ := isStarProjection_iff_eq_starProjection_range.mp hpP
  have hpm : p.range.starProjection ∈ algebra θ := by
    rw [← he]
    exact hp
  simpa only [← he] using exponentialTransfer_transported_vectorTrace θ hb p.range hpm

end Invariant233.Rotation

end

end OAI
