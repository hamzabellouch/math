import OAI.Geometry.RCD.Sobolev.CompactLaplacian

namespace OAI

/-! # Pairing the exact derivative of the averaged potential

On the inner ball the cutoff is one, so its L2 derivative has precisely
the normalized endpoint pairing appearing in the energy estimate.
-/

open Set Filter MeasureTheory Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

theorem averaged_endpoint_pairing (z : X) {r h : ℝ} (hr : 0 < r) (hh : 0 < h)
    (F G : X → ℝ) (hF : ContinuousOn F (closedBall z r)) (hG : ContinuousOn G (closedBall z r))
    (D : Lp ℝ 2 μ)
    (hD : D =ᵐ[μ] fun x => radialCutoff z r x*((G x-F x)/(2*h)))
    (φ : X → ℝ) {L : ℝ≥0} (hφ : LipschitzWith L φ) (hs : tsupport φ ⊆ ball z r) :
    h⁻¹*((∫ x in closedBall z r, φ x*G x ∂μ)-(∫ x in closedBall z r, φ x*F x ∂μ)) =
      2*(∫ x, φ x*D x ∂μ) := by
  have hzero (x : X) (hx : x ∉ closedBall z r) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hp => hx (ball_subset_closedBall (hs hp)))
  have hiF : IntegrableOn (fun x => φ x*F x) (closedBall z r) μ :=
    (hφ.continuous.continuousOn.mul hF).integrableOn_compact (isCompact_closedBall z r)
  have hiG : IntegrableOn (fun x => φ x*G x) (closedBall z r) μ :=
    (hφ.continuous.continuousOn.mul hG).integrableOn_compact (isCompact_closedBall z r)
  have he : (∫ x, φ x*D x ∂μ) = ∫ x in closedBall z r, φ x*D x ∂μ :=
    (setIntegral_eq_integral_of_ae_compl_eq_zero
      (Eventually.of_forall fun x hx => by rw [hzero x hx,zero_mul])).symm
  rw [he,← integral_const_mul]
  calc
    _ = ∫ x in closedBall z r, h⁻¹*(φ x*G x-φ x*F x) ∂μ := by
      rw [← integral_sub hiG hiF,← integral_const_mul]
    _ = ∫ x in closedBall z r, 2*(φ x*D x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hD] with x hx
      by_cases hφx : φ x = 0
      · simp only [hφx,zero_mul,sub_self,mul_zero]
      · have hxin := hs (subset_tsupport φ hφx)
        rw [hx,radialCutoff_eq_one z hr (mem_closedBall'.mp (ball_subset_closedBall hxin)),one_mul]
        field_simp

end RegularPointCoordinates

end

end OAI
