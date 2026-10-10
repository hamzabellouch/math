import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedOneElectronGap
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CorrectedComplement

namespace OAI

/-! The manufactured field has a positive gap above its one-orbital energy
on the complement of the actual orthonormalized modes. All localization losses
are retained explicitly; they are not charged to the final energy precision. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def manufacturedSpectralLoss (γ : ℝ) (m : ℕ) (D η freq S rho H δ : ℝ) : ℝ :=
  planarSiteDerivativeBound D^2+
    γ*(1+η⁻¹)*m*planarSiteTailConstant*Real.exp (-(19/20:ℝ)*(D/8))+
    verticalCutoffDerivativeBound S^2/2+
    freq*(1+η⁻¹)*verticalCutoffTailConstant freq*Real.exp (-freq*S^2/8)+
    freq*η+δ*PlanarSobolev.wellBound+6*Real.pi*rho*S^3/H

theorem manufacturedSpectralLevel_eq (γ : ℝ) (m : ℕ) (D η freq S rho H δ : ℝ) :
    manufacturedSpectralLevel γ m D η freq S rho H δ =
      -1/2+freq/2+γ-manufacturedSpectralLoss γ m D η freq S rho H δ := by
  unfold manufacturedSpectralLevel manufacturedSpectralLoss planarSpectralLevel verticalSpectralLevel
  ring

theorem manufacturedSpectralLevel_lower {γ D η freq S rho H δ : ℝ} {m : ℕ}
    (hloss : manufacturedSpectralLoss γ m D η freq S rho H δ ≤ γ/2) :
    -1/2+freq/2+γ/2 ≤ manufacturedSpectralLevel γ m D η freq S rho H δ := by
  rw [manufacturedSpectralLevel_eq]
  linarith

theorem manufacturedSlab_corrected_complement_lower
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ ∀ (m : ℕ) (D η freq S rho H scale δ : ℝ),
      8 ≤ D → 0 < η → ∀ hfreq : 0 < freq, 0 < S → 0 ≤ rho → 0 < H → 0 ≤ scale → 0 ≤ δ →
      freq^2 = 4*Real.pi*rho → 3*freq/2 ≤ freq^2*S^2/8 →
      ∀ u : Fin m → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      (∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ) →
      γ*(1+η)*(1+m*localizedOverlapBound D) ≤ freq*(1+η) →
      m*localizedOverlapBound D ≤ 1/2 →
      manufacturedSpectralLoss γ m D η freq S rho H δ ≤ γ/2 →
      ∀ v : Coulomb.H1Vector 1,
      (∀ s i, inner ℂ (oneElectronOrbitalLp (correctedLocalizedMode freq u i)
        (correctedLocalizedMode_memLp hfreq u i)) (h1Coordinates v (Sum.inl s)) = 0) →
      (-1/2+freq/2+γ/2)*Coulomb.mass v ≤
        boundedPotentialForm (fun x => manufacturedSlabPotential rho H S freq scale u
          (oneElectronCoordinates x)) v := by
  obtain ⟨γ,hγ,hsmall,hbound⟩ := manufacturedSlab_weakH1_lower hp hv hdensity
  refine ⟨γ,hγ,hsmall,fun m D η freq S rho H scale δ hD hη hfreq hS hrho hH hscale hδ
    hrelation hbarrier u hsep hcoeff hdom hover hloss v ho => ?_⟩
  have hb := hbound m D η freq S rho H scale δ hD hη hfreq hS hrho hH hscale hδ
    hrelation hbarrier u hsep hcoeff hdom v
  rw [corrected_graph_orthogonal_implies_raw hfreq u hsep hover v ho,
    mul_zero,sub_zero] at hb
  have hm : 0 ≤ Coulomb.mass v :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  exact (mul_le_mul_of_nonneg_right (manufacturedSpectralLevel_lower hloss) hm).trans hb

end ContinuumCoulomb

end

end OAI
