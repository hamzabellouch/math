import OAI.Geometry.RCD.Heat.CompactTimePairing
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace OAI

/-! # The weak time equation for compact spatial pairings -/

open Set MeasureTheory
open scoped Interval Topology
noncomputable section
namespace RegularPointCoordinates
variable {Y : Type*} [MetricSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y)

theorem compact_time_pairing_weak_equation (H D : ℝ → Y → ℝ)
    (hH : ContinuousOn (Function.uncurry H) (Ioi 0 ×ˢ univ))
    (hD : ContinuousOn (Function.uncurry D) (Ioi 0 ×ˢ univ))
    (hd : ∀ t, 0 < t → ∀ y, HasDerivAt (fun s => H s y) (D t y) t)
    (φ : Y → ℝ) (hφ : Integrable φ μ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (θ θ' : ℝ → ℝ) (hθ : ContinuousOn θ (Icc a b))
    (hθ' : ContinuousOn θ' (Icc a b))
    (hder : ∀ t ∈ Ioo a b, HasDerivAt θ (θ' t) t)
    (hθa : θ a = 0) (hθb : θ b = 0) :
    (∫ t in a..b, θ t * ∫ y, φ y * D t y ∂μ) =
      -(∫ t in a..b, θ' t * ∫ y, φ y * H t y ∂μ) := by
  have hsub : Icc a b ×ˢ (univ : Set Y) ⊆ Ioi 0 ×ˢ univ :=
    fun q hq => ⟨ha.trans_le hq.1.1,hq.2⟩
  have hPH := compact_time_pairing_continuousOn μ H (hH.mono hsub) φ hφ
  have hPD := compact_time_pairing_continuousOn μ D (hD.mono hsub) φ hφ
  have he := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (by simpa only [uIcc_of_le hab] using hθ)
    (by simpa only [uIcc_of_le hab] using hPH)
    (by simpa only [min_eq_left hab,max_eq_right hab] using hder)
    (fun t ht => compact_time_pairing_hasDerivAt μ H D hH hD hd φ hφ
      (ha.trans (by simpa only [min_eq_left hab] using ht.1)))
    (hθ'.intervalIntegrable_of_Icc hab) (hPD.intervalIntegrable_of_Icc hab)
  simpa only [hθa,hθb,zero_mul,sub_zero,zero_sub] using he

end RegularPointCoordinates

end

end OAI
