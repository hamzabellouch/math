import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.OneElectronProjectedLower

namespace OAI

/-! Uniform projected lower bound for the actual manufactured Coulomb field.
Only the published planar, oscillator and Sobolev-density inputs occur. -/

noncomputable section
namespace ContinuumCoulomb

theorem manufacturedSlab_uniform_projected_lower
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity)
    {freq rho : ℝ} (hfreq : 1 ≤ freq) (hrho : 0 ≤ rho) (hrelation : freq^2 = 4*Real.pi*rho) :
    ∃ γ R S₀ δ C : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ 8 ≤ R ∧ 1 ≤ S₀ ∧ 0 < δ ∧ 0 < C ∧
      ∀ (m : ℕ) (D S H scale r : ℝ), R ≤ D → (m : ℝ) ≤ Real.exp ((19/320:ℝ)*D) →
      S₀ ≤ S → 1 ≤ H → C*S^3 ≤ H → 0 ≤ scale → 0 < r → r ≤ H/2 → r ≤ S →
      ∀ u : Fin m → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      (∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ) →
      ∀ v : Coulomb.H1Vector 1,
      let hf : 0 < freq := lt_of_lt_of_le zero_lt_one hfreq
      let P := correctedOneElectronProjection hf u v
      let Q := correctedOneElectronRemainder hf u v
      let V := fun x : Configuration 1 =>
        manufacturedSlabPotential rho H S freq scale u (oneElectronCoordinates x)
      boundedPotentialForm V P-((-1/2:ℝ)+freq/2)*Coulomb.mass P+
        (γ/4)*Coulomb.mass Q-
        ((4*(m:ℝ)^2*(∑ j, manufacturedOrbitalSquaredError rho H S freq δ D r u j))/(γ/4))*
          Coulomb.mass P ≤ boundedPotentialForm V v-((-1/2:ℝ)+freq/2)*Coulomb.mass v := by
  have hf : 0 < freq := lt_of_lt_of_le zero_lt_one hfreq
  obtain ⟨γ,R,S₀,δ,C,hγ,hγsmall,hR,hS₀,hδ,hC,hgap⟩ :=
    manufacturedSlab_growing_complement_gap hp hv hdensity hfreq hrho hrelation
  obtain ⟨R₂,hR₂,hover⟩ := localizedOverlap_row_threshold
  refine ⟨γ,max R R₂,S₀,δ,C,hγ,hγsmall,hR.trans (le_max_left _ _),hS₀,hδ,hC,
    fun m D S H scale r hD hm hS hH hCH hscale hr hrH hrS u hsep hcoeff v => ?_⟩
  have hs := hover D ((le_max_right _ _).trans hD) m hm
  have hg := hgap m D S H scale ((le_max_left _ _).trans hD) hm hS hH hCH hscale
    u hsep hcoeff (correctedOneElectronRemainder hf u v)
    (correctedOneElectronRemainder_orthogonal hf u hsep hs v)
  exact manufacturedSlab_projected_lower hdensity hrho
    (lt_of_lt_of_le zero_lt_one hH) (lt_of_lt_of_le zero_lt_one (hS₀.trans hS))
    hf hrelation hr hrH hrS hγ scale u hsep hs hδ.le hcoeff v hg

end ContinuumCoulomb

end

end OAI
