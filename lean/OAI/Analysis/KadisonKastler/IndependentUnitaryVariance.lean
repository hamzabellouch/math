import OAI.Analysis.KadisonKastler.CountableUnitaryL2
import OAI.Analysis.KadisonKastler.IndependentL2Variance

namespace OAI

/-! Variance bounds for independently separated unitary transport blocks. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory

variable {X G K : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  [MeasurableSpace G] [Countable G] [MeasurableSingletonClass G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K] [MeasurableSpace K] [BorelSpace K]

omit [IsProbabilityMeasure μ] [MeasurableSpace K] [BorelSpace K] in
theorem countableUnitaryL2_forward_inverse
    (U : G → unitary (K →L[ℂ] K)) {c : X → G} (hc : Measurable c) (B : Lp K 2 μ) :
    countableUnitaryL2 U hc (countableUnitaryL2 (fun g => (U g)⁻¹) hc B) = B := by
  apply Lp.ext
  filter_upwards [countableUnitaryL2_ae U hc (countableUnitaryL2 (fun g => (U g)⁻¹) hc B),
    countableUnitaryL2_ae (fun g => (U g)⁻¹) hc B] with x h₁ h₂
  rw [h₁, h₂]
  exact (Unitary.linearIsometryEquiv (U (c x))).apply_symm_apply (B x)

omit [IsProbabilityMeasure μ] in
theorem independent_unitary_inverse_independent
    (U : G → unitary (K →L[ℂ] K)) {c : X → G} (hc : Measurable c)
    (A B : Lp K 2 μ) (hi : IndepFun A (fun x => (c x, B x)) μ) :
    IndepFun A (countableUnitaryL2 (fun g => (U g)⁻¹) hc B) μ := by
  let T : G × K → K := fun p => (((U p.1)⁻¹ : unitary (K →L[ℂ] K)) : K →L[ℂ] K) p.2
  have hm : Measurable T := measurable_from_prod_countable_right
    (fun g => (((U g)⁻¹ : unitary (K →L[ℂ] K)) : K →L[ℂ] K).continuous.measurable)
  have hraw : IndepFun (fun x => A x) (fun x => T (c x, B x)) μ := hi.comp measurable_id hm
  have hae : (countableUnitaryL2 (fun g => (U g)⁻¹) hc B : X → K) =ᵐ[μ]
      (fun x => T (c x, B x)) := countableUnitaryL2_ae (fun g => (U g)⁻¹) hc B
  exact hraw.congr Filter.EventuallyEq.rfl hae.symm

theorem independent_unitary_variance_left
    (U : G → unitary (K →L[ℂ] K)) {c : X → G} (hc : Measurable c)
    (A B : Lp K 2 μ) (hi : IndepFun A (fun x => (c x, B x)) μ) :
    ‖A - hilbertConstantL2 μ (∫ x, A x ∂μ)‖ ≤ ‖countableUnitaryL2 U hc A - B‖ := by
  let C := countableUnitaryL2 (fun g => (U g)⁻¹) hc B
  have hAC : IndepFun A C μ := independent_unitary_inverse_independent U hc A B hi
  have hC : countableUnitaryL2 U hc C = B := countableUnitaryL2_forward_inverse U hc B
  let : InnerProductSpace ℝ K := InnerProductSpace.complexToReal
  calc
    ‖A - hilbertConstantL2 μ (∫ x, A x ∂μ)‖ ≤ ‖A - C‖ := independent_L2_centering_le A C hAC
    _ = ‖countableUnitaryL2 U hc (A - C)‖ := (countableUnitaryL2_norm U hc _).symm
    _ = ‖countableUnitaryL2 U hc A - B‖ := by rw [countableUnitaryL2_sub, hC]

theorem independent_unitary_variance_right
    (U : G → unitary (K →L[ℂ] K)) {c : X → G} (hc : Measurable c)
    (A B : Lp K 2 μ) (hi : IndepFun B (fun x => (c x, A x)) μ) :
    ‖B - hilbertConstantL2 μ (∫ x, B x ∂μ)‖ ≤ ‖countableUnitaryL2 U hc A - B‖ := by
  have h := independent_unitary_variance_left (fun g => (U g)⁻¹) hc B A hi
  have hnorm : ‖countableUnitaryL2 (fun g => (U g)⁻¹) hc B - A‖ =
      ‖countableUnitaryL2 U hc A - B‖ := by
    rw [← countableUnitaryL2_norm U hc, countableUnitaryL2_sub]
    have hB : countableUnitaryL2 U hc (countableUnitaryL2 (fun g => (U g)⁻¹) hc B) = B := by
      exact countableUnitaryL2_forward_inverse U hc B
    rw [hB, norm_sub_rev]
  exact h.trans_eq hnorm

end

end KadisonKastler

end OAI
