import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.TensorComplementGap
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedPreciseResidual
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedFockStates

namespace OAI

/-! A fixed positive gap on the actual full-domain tensor complement.
The only analytic inputs are the published planar, oscillator and density
statements; the finite tensor projection and its occupation deficit are proved. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem manufacturedSlab_uniform_tensorComplement_gap
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity)
    {freq rho : ℝ} (hfreq : 1 ≤ freq) (hrho : 0 ≤ rho) (hrelation : freq^2 = 4*Real.pi*rho) :
    ∃ γ R S₀ δ C : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ 8 ≤ R ∧ 1 ≤ S₀ ∧ 0 < δ ∧ 0 < C ∧
      ∀ (m n : ℕ) (D S H scale r ε η : ℝ), R ≤ D →
      (m+1:ℕ) ≤ Real.exp ((19/320:ℝ)*D) → S₀ ≤ S → 1 ≤ H → C*S^3 ≤ H →
      0 ≤ scale → 0 < r → r ≤ H/2 → r ≤ S → 0 ≤ ε → 0 ≤ η → η ≤ δ →
      ∀ u : Fin (m+1) → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      (∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ η) →
      4*(m+1:ℕ)^2*(∑ j, manufacturedOrbitalSquaredError rho H S freq η D r u j) ≤ ε^2 →
      (n:ℝ)*(ε+ε^2/(γ/4)) ≤ γ/8 →
      ∀ v : Coulomb.H1Vector (n+1), Coulomb.Antisymmetric v →
      let hf := lt_of_lt_of_le zero_lt_one hfreq
      let q := finiteTensorRemainder (localizedSpinMode freq u)
        (localizedSpinMode_C1 freq u) (localizedSpinMode_memLp hf u)
        (localizedSpinMode_partial_memLp hf u) v
      ((n+1:ℕ)*((-1/2:ℝ)+freq/2)+γ/8)*Coulomb.mass q ≤
        boundedPotentialForm (fun x => ∑ i, manufacturedSlabPotential rho H S freq scale u
          (Coulomb.position x i)) q := by
  have hf : 0 < freq := lt_of_lt_of_le zero_lt_one hfreq
  obtain ⟨γ,R,S₀,δ,C,hγ,hγsmall,hR,hS₀,hδ,hC,hbound⟩ :=
    manufacturedSlab_uniform_precise_manyElectron_lower hp hv hdensity hfreq hrho hrelation
  obtain ⟨R₂,hR₂,hover⟩ := localizedOverlap_row_threshold
  refine ⟨γ,max R R₂,S₀,δ,C,hγ,hγsmall,hR.trans (le_max_left _ _),hS₀,hδ,hC,
    fun m n D S H scale r ε η hD hm hS hH hCH hscale hr hrH hrS hε hη hηδ u hsep hcoeff herr hsmall v ha => ?_⟩
  let q := finiteTensorRemainder (localizedSpinMode freq u)
    (localizedSpinMode_C1 freq u) (localizedSpinMode_memLp hf u)
    (localizedSpinMode_partial_memLp hf u) v
  have hs := hover D ((le_max_right _ _).trans hD) (m+1) hm
  have hocc := finiteTensorRemainder_totalOccupation (localizedSpinMode freq u)
    (localizedSpinMode_C1 freq u) (localizedSpinMode_memLp hf u)
    (localizedSpinMode_partial_memLp hf u) (localizedSpinMode_inner hf u hsep hs)
    (correctedLocalizedMode freq u) (correctedLocalizedMode_memLp hf u)
    (HubbardGlobal.siteModes m).symm (fun _ => rfl) v ha
  have he := hbound (m+1) D S H scale r ε η ((le_max_left _ _).trans hD) hm
    hS hH hCH hscale hr hrH hrS hε hη hηδ u hsep hcoeff herr n q
  have hg := tensorComplement_energy_gap q
    (fun i => oneElectronOrbitalLp (correctedLocalizedMode freq u i)
      (correctedLocalizedMode_memLp hf u i))
    ((-1/2:ℝ)+freq/2) (γ/4) (ε+ε^2/(γ/4)) _
    (by positivity) (by positivity) hocc (by simpa only [add_assoc] using he)
      (by convert hsmall using 1; ring)
  convert hg using 1
  ring

end ContinuumCoulomb

end

end OAI
