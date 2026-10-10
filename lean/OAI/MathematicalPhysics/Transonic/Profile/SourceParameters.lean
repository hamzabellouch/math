import OAI.MathematicalPhysics.Transonic.Profile.Equations
import OAI.MathematicalPhysics.Transonic.Shooting.SourceFamilyJets

namespace OAI

noncomputable section
namespace SepticProfile
namespace SourceFamily
lemma source_q (p : Parameter) : SepticProfile.q (ShootingParameters.beta p.val)=ShootingParameters.q p.val := by
  rw [(ShootingParameters.parameter_identities p.property).1]
  unfold SepticProfile.q ell
  ring
lemma source_sigma (p : Parameter) : SepticProfile.sigma (ShootingParameters.beta p.val)=sig p := by
  rw [SepticProfile.sigma,source_q]
  exact (ShootingParameters.parameter_identities p.property).2.1.symm
lemma source_kappa (p : Parameter) : SepticProfile.kappa (ShootingParameters.beta p.val)=kap p := by
  rw [SepticProfile.kappa,source_q]
  exact (ShootingParameters.parameter_identities p.property).2.2.symm
lemma source_q_pos (p : Parameter) : 0<SepticProfile.q (ShootingParameters.beta p.val) := by
  rw [source_q]
  unfold ShootingParameters.q
  exact div_pos (mul_pos (by norm_num) (ShootingParameters.e_pos p.property)) (ShootingParameters.d_pos p.property)
end SourceFamily
end SepticProfile

end

end OAI
