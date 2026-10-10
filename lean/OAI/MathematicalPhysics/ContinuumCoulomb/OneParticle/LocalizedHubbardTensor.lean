import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockHubbardForm
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedCoulombMatrix
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedHubbard

namespace OAI

/-! The actual localized direct-Coulomb tensor has exactly the on-site
and off-site coefficients of the Hubbard charge operator. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb
open HubbardGlobal

theorem localizedDensityTensor_hubbard (freq : ℝ) {m : ℕ}
    (u : Fin (m+1) → PlanarPosition) :
    localizedDensityTensor freq u = hubbardCoulombTensor m
      (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u) := by
  funext a b c d
  by_cases h : a=c ∧ b=d
  · simp only [localizedDensityTensor,hubbardCoulombTensor,ite_eq_left h]
    rw [localizedFourIndex_diagonal]
    by_cases hs : modeSite m a = modeSite m b
    · simp only [siteCoulombCoefficient,ite_eq_left hs]
      change (localizedCoulombCoeff freq (u (modeSite m a))
        (u (modeSite m b)) : ℂ) = _
      rw [hs,localizedCoulombCoeff_distance,sub_self,norm_zero]
    · change (localizedCoulombCoeff freq (u (modeSite m a))
        (u (modeSite m b)) : ℂ) = _
      simp only [siteCoulombCoefficient,ite_eq_right hs,localizedOffsiteCoulomb]
  · simp only [localizedDensityTensor,hubbardCoulombTensor,ite_eq_right h]

theorem localizedSpinMode_hubbard_tensor_error {freq D : ℝ} (hf : 0 < freq)
    {m : ℕ} (u : Fin (m+1) → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : (m+1:ℕ)*localizedOverlapBound D ≤ 1/2)
    (a b c d : Fin ((2*m+1)+1)) :
    ‖flatCoulombTensor (localizedSpinMode freq u) a b c d-
      hubbardCoulombTensor m (localizedCoulombProfile freq 0)
        (localizedOffsiteCoulomb freq u) a b c d‖ ≤
      (m+1:ℝ)^4*(32*(2*(m+1:ℝ)*localizedOverlapBound D)*localizedPotentialBound freq)+
        localizedFourIndexConstant freq*Real.exp (-(9/10:ℝ)*D) := by
  rw [← localizedDensityTensor_hubbard]
  exact localizedSpinMode_coulomb_error hf u hsep hs a b c d

end ContinuumCoulomb

end

end OAI
