import OAI.Geometry.RCD.Transport.RadialTransportCutoff

namespace OAI

/-! # Positive interior weight of the radial transport cutoff -/

open Metric

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X]

/-- The fixed transport cutoff is uniformly positive through radius 2R,
although it vanishes outside radius 3R. -/
theorem radial_transport_cutoff_lower {n : ℕ} {R : ℝ} (hR : 2 ≤ R) (z : X) :
    let β := transportCutoffExponent n
    let m := ((2 * R) ^ (-β) - (3 * R) ^ (-β)) / β
    0 < m ∧ ∀ x, dist z x ≤ 2 * R → m ≤ radialPowerRep β R (3 * R) z x := by
  dsimp only
  let β := transportCutoffExponent n
  have hβ : 0 < β := transportCutoffExponent_pos n
  have hR0 : 0 < R := by linarith
  have hneg : -β < 0 := neg_neg_of_pos hβ
  constructor
  · exact div_pos (sub_pos.mpr (Real.rpow_lt_rpow_of_neg
      (by positivity : 0 < 2 * R) (by linarith : 2 * R < 3 * R) hneg)) hβ
  · intro x hx
    by_cases hinner : dist z x ≤ R
    · rw [radialPowerRep_inner hβ hR0 (by linarith : R ≤ 3 * R) z x hinner]
      apply div_le_div_of_nonneg_right _ hβ.le
      exact sub_le_sub_right (Real.rpow_le_rpow_of_nonpos hR0 (by linarith) hneg.le) _
    · rw [radialPowerRep_annulus hβ hR0 z x (le_of_not_ge hinner)
        (by linarith : dist z x ≤ 3 * R)]
      apply div_le_div_of_nonneg_right _ hβ.le
      exact sub_le_sub_right (Real.rpow_le_rpow_of_nonpos
        (lt_of_lt_of_le hR0 (le_of_not_ge hinner)) hx hneg.le) _

end RegularPointCoordinates

end

end OAI
