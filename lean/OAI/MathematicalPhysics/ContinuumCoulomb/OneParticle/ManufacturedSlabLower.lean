import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedWellField
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabConfinement

namespace OAI

/-! Global comparison of the actual manufactured Coulomb field with the
separable capped oscillator and planar wells. -/

noncomputable section
namespace ContinuumCoulomb

def manufacturedSlabPotential (rho H S freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (x : Position) : ℝ :=
  slabPotential rho H S x-slabPotential rho H S 0+manufacturedWellField freq scale S u x

theorem manufacturedSlabPotential_lower {rho H S freq scale δ : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 ≤ S) (hscale : 0 ≤ scale)
    (hfreq : freq^2 = 4*Real.pi*rho) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 2 ≤ ‖u i-u j‖) (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i / scale ∧
      localizedCounterterm freq u i / scale ≤ δ) (x : Position) :
    planarWellSum u (positionSplitCoordinates x).1 +
      verticalCapPotential freq S (positionSplitCoordinates x).2 -
      (δ*PlanarSobolev.wellBound+6*Real.pi*rho*S^3/H) ≤
      manufacturedSlabPotential rho H S freq scale u x := by
  have hs := slabPotential_confinement hrho hH hS x
  have hw := manufacturedWellField_lower freq hscale S u hsep hδ hcoeff x
  have he : verticalCapPotential freq S (positionSplitCoordinates x).2 =
      2*Real.pi*rho*min ((x 2)^2) (S^2) := by
    rw [verticalCapPotential,hfreq,positionSplitCoordinates_snd]
    ring
  rw [he]
  unfold manufacturedSlabPotential
  linarith

end ContinuumCoulomb

end

end OAI
