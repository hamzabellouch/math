import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.FormStability
import OAI.Analysis.CoulombRadii.FormDomain.CoreKinetic

namespace OAI

/-! Positive-mass trial vectors give upper bounds for the exact full-domain
Coulomb infimum after normalization. -/

noncomputable section
namespace ContinuumCoulomb

theorem formGroundEnergy_le_rayleigh {M n : ℕ} (S : Coulomb.Nuclei M)
    (w : Coulomb.H1Vector n) (hw : Coulomb.Antisymmetric w) (hm : 0 < Coulomb.mass w) :
    formGroundEnergy S n ≤ ((Coulomb.form S w/Coulomb.mass w : ℝ):EReal) := by
  have h := formGroundEnergy_le_trial S ⟨w.normalized,hw.normalized⟩
    (Coulomb.mass_normalized w hm)
  have he : Coulomb.form S w.normalized = Coulomb.form S w/Coulomb.mass w := by
    apply (eq_div_iff (ne_of_gt hm)).mpr
    simpa only [mul_comm] using Coulomb.form_normalized_weight S w
  simpa only [he] using h

theorem formGroundEnergy_finite_of_positive_mass {M n : ℕ} (S : Coulomb.Nuclei M)
    (w : Coulomb.H1Vector n) (hw : Coulomb.Antisymmetric w) (hm : 0 < Coulomb.mass w) :
    formGroundEnergy S n ≠ ⊤ ∧ formGroundEnergy S n ≠ ⊥ :=
  formGroundEnergy_finite S ⟨w.normalized,hw.normalized⟩ (Coulomb.mass_normalized w hm)

end ContinuumCoulomb

end

end OAI
