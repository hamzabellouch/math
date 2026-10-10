import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalEvolution

namespace OAI

/-! # A positive marked-collision bound on a short waiting interval -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem clockSurvival_antitone (C : ℝ≥0) : Antitone (clockSurvival C) := by
  intro s t hst
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left hst (neg_nonpos.mpr C.coe_nonneg)

theorem physicalMarkedEvent_wait_lower (b : BeamCoefficients) (endTime : ℝ)
    (C : ℝ≥0) (m : HistoryMark) (p : PhysicalFlightState) {h : ℝ}
    (hrem : h ≤ p.1) {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F)
    (D : ℝ≥0∞)
    (hlower : ∀ s ∈ Ioo 0 h, D ≤
      mediumMarkedRate b m (mediumPoint endTime p s,p.2.2) *
        ∫⁻ n : Sphere, F (mediumParameterState b endTime p (m,(s,n))) ∂sphereProbability) :
    clockSurvival C h*D*ENNReal.ofReal h ≤
      ∫⁻ q, F q ∂physicalMarkedEvent b endTime C m p := by
  rw [physicalMarkedEvent_lintegral b endTime C m p hF]
  calc
    _ = ∫⁻ _s in Ioo 0 h, clockSurvival C h*D := by
      rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioo,sub_zero]
    _ ≤ ∫⁻ s in Ioo 0 h, clockSurvival C s *
        (mediumMarkedRate b m (mediumPoint endTime p s,p.2.2) *
          ∫⁻ n : Sphere, F (mediumParameterState b endTime p (m,(s,n))) ∂sphereProbability) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact mul_le_mul' (clockSurvival_antitone C hs.2.le) (hlower s hs)
    _ ≤ _ := by
      have hs : Ioo (0:ℝ) h ⊆ Ioc 0 p.1 := fun s hs => ⟨hs.1,hs.2.le.trans hrem⟩
      exact lintegral_mono' (Measure.restrict_mono hs le_rfl) le_rfl

theorem physicalMarkedEvent_wait_positive (b : BeamCoefficients) (endTime : ℝ)
    (C : ℝ≥0) (m : HistoryMark) (p : PhysicalFlightState) {h : ℝ}
    (hh : 0 < h) (hrem : h ≤ p.1) {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F)
    {D : ℝ≥0∞} (hD : 0 < D)
    (hlower : ∀ s ∈ Ioo 0 h, D ≤
      mediumMarkedRate b m (mediumPoint endTime p s,p.2.2) *
        ∫⁻ n : Sphere, F (mediumParameterState b endTime p (m,(s,n))) ∂sphereProbability) :
    0 < ∫⁻ q, F q ∂physicalMarkedEvent b endTime C m p := by
  have hc : 0 < clockSurvival C h := ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have ht : 0 < ENNReal.ofReal h := ENNReal.ofReal_pos.mpr hh
  have hp : 0 < clockSurvival C h*D*ENNReal.ofReal h :=
    pos_iff_ne_zero.mpr (mul_ne_zero (mul_ne_zero (ne_of_gt hc) (ne_of_gt hD)) (ne_of_gt ht))
  exact hp.trans_le (physicalMarkedEvent_wait_lower b endTime C m p hrem hF D hlower)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
