import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CorrectedOneElectronProjection
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedGrowingGap

namespace OAI

/-! The manufactured spectral gap applies to the actual weak-H1 remainder
of the finite corrected-orbital projection, with an exact mass deficit. -/

noncomputable section
namespace ContinuumCoulomb

theorem manufacturedSlab_projected_remainder_gap
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity)
    {freq rho : ℝ} (hfreq : 1 ≤ freq) (hrho : 0 ≤ rho) (hrelation : freq^2 = 4*Real.pi*rho) :
    ∃ γ R S₀ δ C : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ 8 ≤ R ∧ 1 ≤ S₀ ∧ 0 < δ ∧ 0 < C ∧
      ∀ (m : ℕ) (D S H scale : ℝ), R ≤ D → (m : ℝ) ≤ Real.exp ((19/320:ℝ)*D) →
      S₀ ≤ S → 1 ≤ H → C*S^3 ≤ H → 0 ≤ scale → ∀ u : Fin m → PlanarPosition,
      (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      (∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ) →
      ∀ v : Coulomb.H1Vector 1,
      (-1/2+freq/2+γ/2)*(Coulomb.mass v-
        Coulomb.mass (correctedOneElectronProjection (lt_of_lt_of_le zero_lt_one hfreq) u v)) ≤
        boundedPotentialForm (fun x => manufacturedSlabPotential rho H S freq scale u
          (oneElectronCoordinates x))
            (correctedOneElectronRemainder (lt_of_lt_of_le zero_lt_one hfreq) u v) := by
  have hf : 0 < freq := lt_of_lt_of_le zero_lt_one hfreq
  obtain ⟨γ,R,S₀,δ,C,hγ,hγsmall,hR,hS₀,hδ,hC,hgap⟩ :=
    manufacturedSlab_growing_complement_gap hp hv hdensity hfreq hrho hrelation
  obtain ⟨R₂,hR₂,hover⟩ := localizedOverlap_row_threshold
  refine ⟨γ,max R R₂,S₀,δ,C,hγ,hγsmall,hR.trans (le_max_left _ _),hS₀,hδ,hC,
    fun m D S H scale hD hm hS hH hCH hscale u hsep hcoeff v => ?_⟩
  have hs := hover D ((le_max_right _ _).trans hD) m hm
  have hmass := correctedOneElectron_mass_decomposition hf u hsep hs v
  have h := hgap m D S H scale ((le_max_left _ _).trans hD) hm hS hH hCH hscale
    u hsep hcoeff (correctedOneElectronRemainder hf u v)
    (correctedOneElectronRemainder_orthogonal hf u hsep hs v)
  have he : Coulomb.mass v-Coulomb.mass (correctedOneElectronProjection hf u v) =
      Coulomb.mass (correctedOneElectronRemainder hf u v) := by linarith
  rw [he]
  exact h

end ContinuumCoulomb

end

end OAI
