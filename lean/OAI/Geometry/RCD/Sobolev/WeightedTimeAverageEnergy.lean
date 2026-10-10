import OAI.Geometry.RCD.Coordinates.TimeIntervalAverage
import OAI.Geometry.RCD.Coordinates.IntervalVectorExtension
import OAI.Geometry.RCD.Sobolev.WeightedSobolevIntegralLower

namespace OAI

/-! # Time averaging preserves the actual weighted energy inequality -/

open Set Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem weighted_time_average_energy {a b : ℝ}
    (v : Ioo a b → SobolevSpace μ Q)
    (hv : AEStronglyMeasurable v (volume.comap Subtype.val))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ q, ‖v q‖ ≤ C)
    (φ : X → ℝ) (hφ : AEStronglyMeasurable φ μ) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂μ, ‖φ x‖ ≤ B) (hφ0 : ∀ᵐ x ∂μ, 0 ≤ φ x)
    (P : ℝ → ℝ)
    (henergy : ∀ s t : ℝ, a < s → s < t → t < b →
      (∫ q in Icc s t, intervalExtension (fun τ => weightedGamma μ Q φ (v τ) (v τ)) q) ≤
        2*(P t-P s))
    {h t : ℝ} (hh : 0 < h) (ha : a < t-h) (hb' : t+h < b) :
    weightedGamma μ Q φ (timeIntervalAverage (intervalVectorExtension v) h t)
      (timeIntervalAverage (intervalVectorExtension v) h t) ≤ h⁻¹*(P (t+h)-P (t-h)) := by
  let F := weightedGammaCLM μ Q hφ hB
  let u := intervalVectorExtension v
  have he (q : ℝ) : F (u q) (u q) =
      intervalExtension (fun τ => weightedGamma μ Q φ (v τ) (v τ)) q :=
    bilinear_intervalVectorExtension F v q
  have hsub : Icc (t-h) (t+h) ⊆ Ioo a b :=
    fun q hq => ⟨ha.trans_le hq.1,hq.2.trans_lt hb'⟩
  have hui : Integrable u := intervalVectorExtension_integrable v hv hb
  have hei : IntegrableOn (fun q => F (u q) (u q)) (Icc (t-h) (t+h)) := by
    exact ((interval_bilinear_energy_integrable F v hv hC hb).mono_set hsub).congr
      (Eventually.of_forall fun q => (he q).symm)
  have hj := positive_bilinear_timeIntervalAverage F
    (weightedGamma_nonneg_of_weight μ Q hφ0) (weightedGamma_comm μ Q φ)
    u hh t hui.integrableOn hei
  have hbound := henergy (t-h) (t+h) ha (by linarith) hb'
  calc
    _ ≤ (2*h)⁻¹ * ∫ q in (t-h)..(t+h), F (u q) (u q) := hj
    _ = (2*h)⁻¹ * ∫ q in Icc (t-h) (t+h),
        intervalExtension (fun τ => weightedGamma μ Q φ (v τ) (v τ)) q := by
      rw [intervalIntegral.integral_of_le (by linarith),← integral_Icc_eq_integral_Ioc]
      simp_rw [he]
    _ ≤ (2*h)⁻¹ * (2*(P (t+h)-P (t-h))) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by field_simp

end RegularPointCoordinates

end

end OAI
