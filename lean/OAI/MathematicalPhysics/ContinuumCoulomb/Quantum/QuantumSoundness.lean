import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumEndpoint

namespace OAI

/-! Homogeneous soundness for arbitrary, unnormalized witnesses. -/

noncomputable section
namespace ContinuumCoulomb

theorem qmaRejectVector_sound_all (c : QMACircuit) (hc : c.WellFormed)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    (2/3:ℝ)*‖psi‖^2 ≤ ‖qmaRejectVector c hc psi‖^2 := by
  by_cases hz : psi = 0
  · subst psi
    simp
  have hn : ‖psi‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let phi := ((‖psi‖⁻¹ : ℝ) : ℂ) • psi
  have hphi : ‖phi‖ = 1 := by
    simp [phi,norm_smul,hn]
  have hscale : psi = (‖psi‖ : ℂ) • phi := by
    change psi = (‖psi‖ : ℝ) • (‖psi‖⁻¹ • psi)
    rw [smul_smul,mul_inv_cancel₀ hn,one_smul]
  have hb := qmaRejectVector_of_sound c hc phi hphi (hsound phi hphi)
  have he : ‖qmaRejectVector c hc psi‖^2 =
      ‖psi‖^2*‖qmaRejectVector c hc phi‖^2 := by
    conv_lhs => rw [hscale]
    rw [qmaRejectVector_smul]
    simp [norm_smul,mul_pow]
  rw [he]
  nlinarith [sq_nonneg ‖psi‖]

end ContinuumCoulomb

end

end OAI
