import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.ElectronSlotBound
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedOneElectronGap

namespace OAI

/-! The actual manufactured Coulomb lower bound on the complete spinful
many-electron weak-H1 domain. The sum of orbital occupations is the sum of
the actual L2 slice contractions, not a restriction on the admitted states. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem manufacturedSlab_manyElectron_lower
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ ∀ (m : ℕ) (D η freq S rho H scale δ : ℝ),
      8 ≤ D → 0 < η → ∀ hfreq : 0 < freq, 0 < S → 0 ≤ rho → 0 < H → 0 ≤ scale → 0 ≤ δ →
      freq^2 = 4*Real.pi*rho → 3*freq/2 ≤ freq^2*S^2/8 →
      ∀ u : Fin m → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      (∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ) →
      γ*(1+η)*(1+m*localizedOverlapBound D) ≤ freq*(1+η) →
      ∀ (n : ℕ) (v : Coulomb.H1Vector (n+1)),
      (n+1:ℕ)*manufacturedSpectralLevel γ m D η freq S rho H δ*Coulomb.mass v-
        γ*(1+η)*totalOrbitalMass v
          (fun i => oneElectronOrbitalLp (continuumLocalizedMode freq (u i))
            (continuumLocalizedMode_memLp hfreq (u i))) ≤
        boundedPotentialForm (fun x => ∑ i, manufacturedSlabPotential rho H S freq scale u
          (Coulomb.position x i)) v := by
  obtain ⟨γ,hγ,hsmall,hbound⟩ := manufacturedSlab_weakH1_lower hp hv hdensity
  refine ⟨γ,hγ,hsmall,fun m D η freq S rho H scale δ hD hη hfreq hS hrho hH hscale hδ
    hrelation hbarrier u hsep hcoeff hdom n v => ?_⟩
  obtain ⟨B,hB⟩ := manufacturedSlabPotential_bounded hrho hH.le hS freq scale u
  exact manyElectron_projection_lower _
    (manufacturedSlabPotential_continuous hrho hH.le hS.le freq scale u) B hB
    (fun i => oneElectronOrbitalLp (continuumLocalizedMode freq (u i))
      (continuumLocalizedMode_memLp hfreq (u i))) _ _
    (hbound m D η freq S rho H scale δ hD hη hfreq hS hrho hH hscale hδ
      hrelation hbarrier u hsep hcoeff hdom) v

end ContinuumCoulomb

end

end OAI
