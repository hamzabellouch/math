import OAI.MathematicalPhysics.Transonic.Certificates.SonicEndpointBox
import OAI.MathematicalPhysics.Transonic.Certificates.FixedLowJet

namespace OAI

section

namespace SepticProfile.LowEndpointBox
open SonicEndpointBox FixedInterval

def R : ℤ := 1000000000000000000000000000000000000000000000000000000000000000000000000
def lower : ℤ := 989491784059057597398012966628527884590702912895570068883115000000000000
def upper : ℤ := 989491784059077597398012966628527884590702912895570068883115000000000000
theorem R_pos : 0<R := by decide +kernel
theorem lower_data : FixedLowJet.Q*lower≤R*((endpointBox FixedLowJet.Q FixedLowJet.w (-1/1000)).center-
    (endpointBox FixedLowJet.Q FixedLowJet.w (-1/1000)).radius) := by decide +kernel
theorem upper_data : R*((endpointBox FixedLowJet.Q FixedLowJet.w (1/1000)).center+
    (endpointBox FixedLowJet.Q FixedLowJet.w (1/1000)).radius)≤FixedLowJet.Q*upper := by decide +kernel

lemma endpoint_bounds (f : PowerSeries ℝ)
    (hw : ∀ i≤220, Holds FixedLowJet.Q (FixedLowJet.w i) (PowerSeries.coeff i (f-1))) :
    (lower:ℝ)/R ≤ (EulerPolynomial.barrier f (-1/1000)).eval (5/6) ∧
    (EulerPolynomial.barrier f (1/1000)).eval (5/6) ≤ (upper:ℝ)/R := by
  constructor
  · apply lower_from_box FixedLowJet.Q_pos R_pos _ lower_data
    simpa only [Rat.cast_neg,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      holds_endpoint FixedLowJet.Q_pos FixedLowJet.w f (-1/1000) hw
  · apply upper_from_box FixedLowJet.Q_pos R_pos _ upper_data
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      holds_endpoint FixedLowJet.Q_pos FixedLowJet.w f (1/1000) hw
end SepticProfile.LowEndpointBox


end

end OAI
