import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedWeakResidual
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.H1PairingBound

namespace OAI

/-! The actual manufactured operator's mixed mode pairing is bounded by
its proved differential residual, uniformly on the full weak-H1 domain. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def manufacturedModePairing (rho H S freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) (v : Coulomb.H1Vector 1)
    (s : SpinConfiguration 1) : ℂ :=
  (1/2:ℂ)*(∑ a, ∫ x, v.gradient s a x*
    (configurationRealPartial (oneElectronLocalizedMode freq (u j)) a x : ℂ))+
    (∫ x, v.value s x*(manufacturedSlabPotential rho H S freq scale u
      (oneElectronCoordinates x)*oneElectronLocalizedMode freq (u j) x : ℝ))-
    (((-1/2:ℝ)+freq/2):ℂ)*(∫ x, v.value s x*(oneElectronLocalizedMode freq (u j) x : ℂ))

theorem manufacturedModePairing_square_bound
    (hdensity : PublishedSobolevSmoothDensity) {rho H S freq δ D R : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
    (hrelation : freq^2 = 4*Real.pi*rho) (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (j : Fin m)
    (v : Coulomb.H1Vector 1) (s : SpinConfiguration 1) :
    ‖manufacturedModePairing rho H S freq scale u j v s‖^2 ≤
      manufacturedOrbitalSquaredError rho H S freq δ D R u j*(∫ x, ‖v.value s x‖^2) := by
  rw [manufacturedModePairing,
    manufacturedOrbitalResidual_weak_identity hdensity hrho hH.le hS hfreq hrelation scale u hδ hcoeff]
  have hmem := (manufacturedOrbitalResidual_memLp hrho hH.le hS.le hfreq scale u hδ hcoeff j).comp_measurePreserving oneElectronCoordinates.measurePreserving
  have h := h1_real_pairing_sq_le v s
    (fun x => manufacturedOrbitalResidual rho H S freq scale u j (oneElectronCoordinates x)) hmem
  have hint : (∫ x : Configuration 1,
      manufacturedOrbitalResidual rho H S freq scale u j (oneElectronCoordinates x)^2) =
      ∫ x, manufacturedOrbitalResidual rho H S freq scale u j x^2 :=
    oneElectronCoordinates_integral (fun x => manufacturedOrbitalResidual rho H S freq scale u j x^2)
  rw [hint] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (manufacturedOrbitalResidual_square_bound hrho hH hS hfreq hR hRH hRS scale u hsep hδ hcoeff j)
    (integral_nonneg (fun _ => sq_nonneg _)))

end ContinuumCoulomb

end

end OAI
