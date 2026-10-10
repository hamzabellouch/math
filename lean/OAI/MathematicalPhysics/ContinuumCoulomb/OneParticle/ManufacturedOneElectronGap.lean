import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.PhysicalOneElectronLower
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.OneElectronClosure

namespace OAI

/-! The manufactured field's finite-rank lower estimate holds on the entire
spinful weak-H1 domain. No smoothness, compact support, or reality condition is
imposed on the state in this theorem. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def manufacturedSpectralLevel (γ : ℝ) (m : ℕ) (D η freq S rho H δ : ℝ) : ℝ :=
  planarSpectralLevel γ m D η+verticalSpectralLevel freq S η-freq*(1+η)-
    (δ*PlanarSobolev.wellBound+6*Real.pi*rho*S^3/H)

theorem manufacturedSlab_weakH1_lower
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap)
    (hdensity : PublishedSobolevSmoothDensity) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ ∀ (m : ℕ) (D η freq S rho H scale δ : ℝ),
      8 ≤ D → 0 < η → ∀ hfreq : 0 < freq, 0 < S → 0 ≤ rho → 0 < H → 0 ≤ scale → 0 ≤ δ →
      freq^2 = 4*Real.pi*rho → 3*freq/2 ≤ freq^2*S^2/8 →
      ∀ u : Fin m → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      (∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ) →
      γ*(1+η)*(1+m*localizedOverlapBound D) ≤ freq*(1+η) →
      ∀ v : Coulomb.H1Vector 1,
      manufacturedSpectralLevel γ m D η freq S rho H δ*Coulomb.mass v-
        γ*(1+η)*graphOrbitalMass
          (fun i => oneElectronOrbitalLp (continuumLocalizedMode freq (u i))
            (continuumLocalizedMode_memLp hfreq (u i))) (h1Coordinates v) ≤
        boundedPotentialForm (fun x => manufacturedSlabPotential rho H S freq scale u
          (oneElectronCoordinates x)) v := by
  obtain ⟨γ,hγ,hsmall,hphysical⟩ := manufacturedSlab_test_lower hp hv
  refine ⟨γ,hγ,hsmall,fun m D η freq S rho H scale δ hD hη hfreq hS hrho hH hscale hδ
    hrelation hbarrier u hsep hcoeff hdom v => ?_⟩
  obtain ⟨B,hB⟩ := manufacturedSlabPotential_bounded hrho hH.le hS freq scale u
  exact oneElectron_weakH1_lower hdensity _
    (manufacturedSlabPotential_continuous hrho hH.le hS.le freq scale u) B hB
    (fun i => continuumLocalizedMode freq (u i))
    (fun i => continuumLocalizedMode_memLp hfreq (u i)) _ _
    (hphysical m D η freq S rho H scale δ hD hη hfreq hS hrho hH hscale hδ
      hrelation hbarrier u hsep hcoeff hdom) v

end ContinuumCoulomb

end

end OAI
