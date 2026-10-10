import OAI.MathematicalPhysics.Transonic.Certificates.LowPolynomialCertificate
import OAI.MathematicalPhysics.Transonic.Certificates.HighPolynomialCertificate
import OAI.MathematicalPhysics.Transonic.Certificates.LowEndpointBox
import OAI.MathematicalPhysics.Transonic.Certificates.HighEndpointBox
import OAI.MathematicalPhysics.Transonic.Shooting.RegularLowEndpoint
import OAI.MathematicalPhysics.Transonic.Shooting.RegularHighEndpoint
import OAI.MathematicalPhysics.Transonic.Shooting.SourceFamilyEulerSeed

namespace OAI

section
noncomputable section

namespace SepticProfile.SourceFamily
open Set

lemma sig_left : sig leftParameter=(FixedLowJet.sigma:ℝ) := by
  norm_num [sig,leftParameter,ShootingParameters.sigma,ShootingParameters.d,
    ShootingParameters.e,ShootingParameters.leftEnd,FixedLowJet.sigma]
lemma kap_left : kap leftParameter=(FixedLowJet.kappa:ℝ) := by
  norm_num [kap,leftParameter,ShootingParameters.kappa,ShootingParameters.e,
    ShootingParameters.leftEnd,FixedLowJet.kappa]
lemma slp_left : slp leftParameter= -500*(FixedLowJet.a:ℝ) := by
  norm_num [slp,leftParameter,ShootingParameters.slope,ShootingParameters.e,
    ShootingParameters.a,ShootingParameters.leftEnd,FixedLowJet.a]
lemma sig_right : sig rightParameter=(FixedHighJet.sigma:ℝ) := by
  norm_num [sig,rightParameter,ShootingParameters.sigma,ShootingParameters.d,
    ShootingParameters.e,ShootingParameters.rightEnd,FixedHighJet.sigma]
lemma kap_right : kap rightParameter=(FixedHighJet.kappa:ℝ) := by
  norm_num [kap,rightParameter,ShootingParameters.kappa,ShootingParameters.e,
    ShootingParameters.rightEnd,FixedHighJet.kappa]
lemma slp_right : slp rightParameter= -500*(FixedHighJet.a:ℝ) := by
  norm_num [slp,rightParameter,ShootingParameters.slope,ShootingParameters.e,
    ShootingParameters.a,ShootingParameters.rightEnd,FixedHighJet.a]

lemma UniformGerm.euler_jet_data (G : UniformGerm) (p : Parameter) :
    PowerSeries.coeff 0 (SonicJet.jet (G.eulerFunction p))=1 ∧
    PowerSeries.coeff 1 (SonicJet.jet (G.eulerFunction p))= -slp p/500 ∧
    EulerFormal.residual (sig p) (kap p) (3/5) (1/500) (SonicJet.jet (G.eulerFunction p))=0 := by
  have hd := G.euler_data p
  refine ⟨?_,?_,?_⟩
  · simpa [SonicJet.coeff_jet] using hd.2.1
  · simpa [SonicJet.coeff_jet] using hd.2.2.1
  · exact EulerFormal.residual_of_solution _ _ _ _ hd.1.contDiffAt hd.2.2.2

lemma left_certificate : SonicContinuation.PolynomialCertificate (sig leftParameter)
    (kap leftParameter) (slp leftParameter) := by
  rw [sig_left,kap_left,slp_left]
  exact LowPolynomialCertificate.certificate
lemma right_certificate : SonicContinuation.PolynomialCertificate (sig rightParameter)
    (kap rightParameter) (slp rightParameter) := by
  rw [sig_right,kap_right,slp_right]
  exact HighPolynomialCertificate.certificate

lemma UniformGerm.left_entry_bounds (G : UniformGerm) :
    (IntegerPolynomial.head RegularLowData.step0.lo:ℝ)/RegularLowData.Q ≤
      (EulerPolynomial.barrier (SonicJet.jet (G.eulerFunction leftParameter)) (-1/1000)).eval (5/6) ∧
    (EulerPolynomial.barrier (SonicJet.jet (G.eulerFunction leftParameter)) (1/1000)).eval (5/6) ≤
      (IntegerPolynomial.head RegularLowData.step0.hi:ℝ)/RegularLowData.Q := by
  have hd := G.euler_jet_data leftParameter
  rw [sig_left,kap_left,slp_left] at hd
  have hb := LowEndpointBox.endpoint_bounds _ (LowPolynomialCertificate.jet_enclosed _ hd.1 hd.2.1 hd.2.2)
  have hQ : LowEndpointBox.R=RegularLowData.Q := rfl
  have hlo : LowEndpointBox.lower=IntegerPolynomial.head RegularLowData.step0.lo := by decide +kernel
  have hhi : LowEndpointBox.upper=IntegerPolynomial.head RegularLowData.step0.hi := by decide +kernel
  rwa [hQ,hlo,hhi] at hb

lemma UniformGerm.right_entry_bounds (G : UniformGerm) :
    (IntegerPolynomial.head RegularHighData.step0.lo:ℝ)/RegularHighData.Q ≤
      (EulerPolynomial.barrier (SonicJet.jet (G.eulerFunction rightParameter)) (-1/1000)).eval (5/6) ∧
    (EulerPolynomial.barrier (SonicJet.jet (G.eulerFunction rightParameter)) (1/1000)).eval (5/6) ≤
      (IntegerPolynomial.head RegularHighData.step0.hi:ℝ)/RegularHighData.Q := by
  have hd := G.euler_jet_data rightParameter
  rw [sig_right,kap_right,slp_right] at hd
  have hb := HighEndpointBox.endpoint_bounds _ (HighPolynomialCertificate.jet_enclosed _ hd.1 hd.2.1 hd.2.2)
  have hQ : HighEndpointBox.R=RegularHighData.Q := rfl
  have hlo : HighEndpointBox.lower=IntegerPolynomial.head RegularHighData.step0.lo := by decide +kernel
  have hhi : HighEndpointBox.upper=IntegerPolynomial.head RegularHighData.step0.hi := by decide +kernel
  rwa [hQ,hlo,hhi] at hb

lemma sig_left_regular : sig leftParameter=(RegularLowData.SN:ℝ)/RegularLowData.S := by
  rw [sig_left]
  norm_num [FixedLowJet.sigma,RegularLowData.SN,RegularLowData.S]
lemma kap_left_regular : kap leftParameter=(RegularLowData.KN:ℝ)/RegularLowData.K := by
  rw [kap_left]
  norm_num [FixedLowJet.kappa,RegularLowData.KN,RegularLowData.K]
lemma sig_right_regular : sig rightParameter=(RegularHighData.SN:ℝ)/RegularHighData.S := by
  rw [sig_right]
  norm_num [FixedHighJet.sigma,RegularHighData.SN,RegularHighData.S]
lemma kap_right_regular : kap rightParameter=(RegularHighData.KN:ℝ)/RegularHighData.K := by
  rw [kap_right]
  norm_num [FixedHighJet.kappa,RegularHighData.KN,RegularHighData.K]

end SepticProfile.SourceFamily

end
end

end OAI
