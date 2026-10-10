import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexBoundaryFormula
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralDilationBoundaryEstimate

namespace OAI

/-! The exact angular boundary term is controlled by the frequency-weighted
Cauchy energy, including angular degrees of order square root frequency. -/

namespace DefocusingNLS
open ProfileCertificate

theorem radialComplexAngularBoundary_bound (n : ℕ) (z : ProfileMatchingBall)
    (R omega eta W Q S A s : ℝ) (q : ℝ → ℝ) (f : ℝ → ℂ)
    (hR : 0 < R) (ho : 1 ≤ omega) (heta : 0 ≤ eta) (hW : 0 ≤ W)
    (hQ : 0 ≤ Q) (hS : 0 ≤ S) (hA : 0 ≤ A)
    (hang : eta ≤ A*omega) (hw : |radialMatchedVelocity n z R| ≤ W)
    (hs : |s| ≤ S) (hq : |q R| ≤ Q) (hf : Differentiable ℝ f) :
    |radialComplexAngularBoundary n z eta R s q f| ≤
      (W*(Q+1)+S+W*(A/R^2))*radialMassDensity n z R*
        (omega*‖f R‖^2+‖deriv f R‖^2) := by
  have hM : 0 ≤ radialMassDensity n z R := by dsimp only [radialMassDensity]; positivity
  have hV : |radialMassFlux n z R| ≤ W*radialMassDensity n z R := by
    change |radialMassDensity n z R*radialMatchedVelocity n z R| ≤ _
    rw [abs_mul,abs_of_nonneg hM]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hw hM
  have hK : radialAngularDensity n z R=radialMassDensity n z R/R^2 := by
    dsimp only [radialAngularDensity,radialMassDensity]
    field_simp
  have hJ : |eta*radialAngularDensity n z R*radialMatchedVelocity n z R| ≤
      W*(A/R^2)*omega*radialMassDensity n z R := by
    rw [hK,abs_mul,abs_mul,abs_of_nonneg heta,abs_of_nonneg (by positivity : 0 ≤ radialMassDensity n z R/R^2)]
    calc
      _ ≤ (A*omega)*(radialMassDensity n z R/R^2)*W :=
        mul_le_mul (mul_le_mul_of_nonneg_right hang (by positivity)) hw (abs_nonneg _) (by positivity)
      _ = _ := by ring
  rw [radialComplexAngularBoundary_eq n z eta R s q f hf]
  exact spectralDilationBoundary_estimate _ _ _ omega W Q S (A/R^2) s (q R)
    (f R) (deriv f R) hM ho hW hQ hS (by positivity) hV hJ hs hq

end DefocusingNLS

end OAI
