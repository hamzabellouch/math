import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.OneElectronFormDecomposition
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CorrectedRemainderGap

namespace OAI

/-! Absorption of the actual differential residual into the complementary
spectral gap on the full spinful weak-H1 domain. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem manufacturedOrbitalSquaredError_nonneg {rho H S freq δ D R : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
    (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (j : Fin m) :
    0 ≤ manufacturedOrbitalSquaredError rho H S freq δ D R u j :=
  (integral_nonneg (fun _ => sq_nonneg _)).trans
    (manufacturedOrbitalResidual_square_bound hrho hH hS hfreq hR hRH hRS
      scale u hsep hδ hcoeff j)

theorem manufacturedSlab_projected_lower
    (hdensity : PublishedSobolevSmoothDensity) {rho H S freq δ D R γ : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
    (hrelation : freq^2 = 4*Real.pi*rho) (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S)
    (hγ : 0 < γ) (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (hs : m*localizedOverlapBound D ≤ 1/2)
    (hδ : 0 ≤ δ) (hcoeff : ∀ j, 0 ≤ localizedCounterterm freq u j/scale ∧
      localizedCounterterm freq u j/scale ≤ δ)
    (v : Coulomb.H1Vector 1)
    (hgap : ((-1/2:ℝ)+freq/2+γ/2)*
        Coulomb.mass (correctedOneElectronRemainder hfreq u v) ≤
      boundedPotentialForm (fun x => manufacturedSlabPotential rho H S freq scale u
        (oneElectronCoordinates x)) (correctedOneElectronRemainder hfreq u v)) :
    boundedPotentialForm (fun x => manufacturedSlabPotential rho H S freq scale u
        (oneElectronCoordinates x)) (correctedOneElectronProjection hfreq u v)-
      ((-1/2:ℝ)+freq/2)*Coulomb.mass (correctedOneElectronProjection hfreq u v)+
      (γ/4)*Coulomb.mass (correctedOneElectronRemainder hfreq u v)-
      ((4*(m:ℝ)^2*(∑ j, manufacturedOrbitalSquaredError rho H S freq δ D R u j))/(γ/4))*
        Coulomb.mass (correctedOneElectronProjection hfreq u v) ≤
      boundedPotentialForm (fun x => manufacturedSlabPotential rho H S freq scale u
        (oneElectronCoordinates x)) v-((-1/2:ℝ)+freq/2)*Coulomb.mass v := by
  let V : Configuration 1 → ℝ := fun x =>
    manufacturedSlabPotential rho H S freq scale u (oneElectronCoordinates x)
  have hV : Continuous V :=
    (manufacturedSlabPotential_continuous hrho hH.le hS.le freq scale u).comp
      oneElectronCoordinates.continuous
  obtain ⟨B,hB⟩ := manufacturedSlabPotential_bounded hrho hH.le hS freq scale u
  have hB' : ∀ x, |V x| ≤ B := fun x => hB (oneElectronCoordinates x)
  have hcross := corrected_cross_square_bound hdensity hrho hH hS hfreq hrelation hR
    hRH hRS scale u hsep hs hδ hcoeff (correctedOneElectronCoefficients hfreq u v)
    (correctedOneElectronRemainder hfreq u v)
    (correctedOneElectronRemainder_orthogonal hfreq u hsep hs v) B hB'
  have herr : 0 ≤ 4*(m:ℝ)^2*(∑ j, manufacturedOrbitalSquaredError rho H S freq δ D R u j) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (Finset.sum_nonneg (fun j _ => manufacturedOrbitalSquaredError_nonneg hrho hH hS
        hfreq hR hRH hRS scale u hsep hδ hcoeff j))
  have ha := absorb_cross_term herr
    (Coulomb.mass_nonneg (correctedOneElectronProjection hfreq u v))
    (Coulomb.mass_nonneg (correctedOneElectronRemainder hfreq u v))
    (show 0 < γ/4 by positivity) hcross
  have hf := correctedOneElectron_form_decomposition hfreq u v V hV B hB'
  have hm := correctedOneElectron_mass_decomposition hfreq u hsep hs v
  change boundedPotentialForm V _-((-1/2:ℝ)+freq/2)*_+(γ/4)*_-_ ≤
    boundedPotentialForm V _-((-1/2:ℝ)+freq/2)*_
  change ((-1/2:ℝ)+freq/2+γ/2)*_ ≤ boundedPotentialForm V _ at hgap
  change -(4*(m:ℝ)^2*(∑ j, manufacturedOrbitalSquaredError rho H S freq δ D R u j)/(γ/4))*
    Coulomb.mass (correctedOneElectronProjection hfreq u v)-
    (γ/4)*Coulomb.mass (correctedOneElectronRemainder hfreq u v) ≤
      2*graphBoundedCross (BoundedPotential.operator V hV B hB')
        (h1Coordinates (correctedOneElectronProjection hfreq u v))
        (h1Coordinates (correctedOneElectronRemainder hfreq u v)) at ha
  rw [hm,hf]
  nlinarith only [hgap,ha]

end ContinuumCoulomb

end

end OAI
