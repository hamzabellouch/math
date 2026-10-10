import OAI.MathematicalPhysics.Transonic.Certificates.SonicEndpointBox
import OAI.MathematicalPhysics.Transonic.Certificates.FixedHighJet

namespace OAI

section

namespace SepticProfile.HighEndpointBox
open SonicEndpointBox FixedInterval

def R : ℤ := 1000000000000000000000000000000000000000000000000000000000000000000000000
def lower : ℤ := 989491913992814365815320586337540913276548720244583995065900000000000000
def upper : ℤ := 989491913992834365815320586337540913276548720244583995065900000000000000
theorem R_pos : 0<R := by decide +kernel
theorem lower_data : FixedHighJet.Q*lower≤R*((endpointBox FixedHighJet.Q FixedHighJet.w (-1/1000)).center-
    (endpointBox FixedHighJet.Q FixedHighJet.w (-1/1000)).radius) := by decide +kernel
theorem upper_data : R*((endpointBox FixedHighJet.Q FixedHighJet.w (1/1000)).center+
    (endpointBox FixedHighJet.Q FixedHighJet.w (1/1000)).radius)≤FixedHighJet.Q*upper := by decide +kernel

lemma endpoint_bounds (f : PowerSeries ℝ)
    (hw : ∀ i≤220, Holds FixedHighJet.Q (FixedHighJet.w i) (PowerSeries.coeff i (f-1))) :
    (lower:ℝ)/R ≤ (EulerPolynomial.barrier f (-1/1000)).eval (5/6) ∧
    (EulerPolynomial.barrier f (1/1000)).eval (5/6) ≤ (upper:ℝ)/R := by
  constructor
  · apply lower_from_box FixedHighJet.Q_pos R_pos _ lower_data
    simpa only [Rat.cast_neg,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      holds_endpoint FixedHighJet.Q_pos FixedHighJet.w f (-1/1000) hw
  · apply upper_from_box FixedHighJet.Q_pos R_pos _ upper_data
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      holds_endpoint FixedHighJet.Q_pos FixedHighJet.w f (1/1000) hw
end SepticProfile.HighEndpointBox


end

end OAI
