import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CorrectedDiagonalBound
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.ElectronSlotBound

namespace OAI

/-! The residual-controlled one-electron estimate and its integral over all
electron slots. The admitted many-electron state remains unrestricted. -/

noncomputable section
namespace ContinuumCoulomb

theorem manufacturedSlab_residual_finite_rank_lower
    (hdensity : PublishedSobolevSmoothDensity) {rho H S freq δ D R γ ε : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
    (hrelation : freq^2 = 4*Real.pi*rho) (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S)
    (hγ : 0 < γ) (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (hs : m*localizedOverlapBound D ≤ 1/2)
    (hδ : 0 ≤ δ) (hcoeff : ∀ j, 0 ≤ localizedCounterterm freq u j/scale ∧
      localizedCounterterm freq u j/scale ≤ δ)
    (hε : 0 ≤ ε) (herr : 4*(m:ℝ)^2*(∑ j, manufacturedOrbitalSquaredError rho H S freq δ D R u j) ≤ ε^2)
    (hgap : ∀ v : Coulomb.H1Vector 1,
      (∀ s i, inner ℂ (oneElectronOrbitalLp (correctedLocalizedMode freq u i)
        (correctedLocalizedMode_memLp hfreq u i)) (h1Coordinates v (Sum.inl s)) = 0) →
      ((-1/2:ℝ)+freq/2+γ/2)*Coulomb.mass v ≤
        boundedPotentialForm (fun x => manufacturedSlabPotential rho H S freq scale u
          (oneElectronCoordinates x)) v)
    (v : Coulomb.H1Vector 1) :
    ((-1/2:ℝ)+freq/2+γ/4)*Coulomb.mass v-
      (γ/4+ε+ε^2/(γ/4))*graphOrbitalMass
        (fun i => oneElectronOrbitalLp (correctedLocalizedMode freq u i)
          (correctedLocalizedMode_memLp hfreq u i)) (h1Coordinates v) ≤
      boundedPotentialForm (fun x => manufacturedSlabPotential rho H S freq scale u
        (oneElectronCoordinates x)) v := by
  have hg := hgap (correctedOneElectronRemainder hfreq u v)
    (correctedOneElectronRemainder_orthogonal hfreq u hsep hs v)
  have hp := manufacturedSlab_projected_lower hdensity hrho hH hS hfreq hrelation hR hRH hRS
    hγ scale u hsep hs hδ hcoeff v hg
  have hd := corrected_diagonal_lower hdensity hrho hH hS hfreq hrelation hR hRH hRS
    scale u hsep hs hδ hcoeff hε herr (correctedOneElectronCoefficients hfreq u v)
  have hm := correctedOneElectron_mass_decomposition hfreq u hsep hs v
  rw [← correctedOneElectronProjection_mass hfreq u hsep hs v]
  have he := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right herr (by positivity : 0 ≤ γ/4))
    (Coulomb.mass_nonneg (correctedOneElectronProjection hfreq u v))
  change (((-1/2:ℝ)+freq/2)-ε)*Coulomb.mass (correctedOneElectronProjection hfreq u v) ≤
    boundedPotentialForm (fun x => manufacturedSlabPotential rho H S freq scale u
      (oneElectronCoordinates x)) (correctedOneElectronProjection hfreq u v) at hd
  rw [hm] at hp ⊢
  nlinarith only [hp,hd,he]

theorem manufacturedSlab_uniform_residual_manyElectron_lower
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity)
    {freq rho : ℝ} (hfreq : 1 ≤ freq) (hrho : 0 ≤ rho) (hrelation : freq^2 = 4*Real.pi*rho) :
    ∃ γ R S₀ δ C : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ 8 ≤ R ∧ 1 ≤ S₀ ∧ 0 < δ ∧ 0 < C ∧
      ∀ (m : ℕ) (D S H scale r ε : ℝ), R ≤ D → (m : ℝ) ≤ Real.exp ((19/320:ℝ)*D) →
      S₀ ≤ S → 1 ≤ H → C*S^3 ≤ H → 0 ≤ scale → 0 < r → r ≤ H/2 → r ≤ S → 0 ≤ ε →
      ∀ u : Fin m → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      (∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ) →
      4*(m:ℝ)^2*(∑ j, manufacturedOrbitalSquaredError rho H S freq δ D r u j) ≤ ε^2 →
      ∀ (n : ℕ) (v : Coulomb.H1Vector (n+1)),
      (n+1:ℕ)*((-1/2:ℝ)+freq/2+γ/4)*Coulomb.mass v-
        (γ/4+ε+ε^2/(γ/4))*totalOrbitalMass v
          (fun i => oneElectronOrbitalLp (correctedLocalizedMode freq u i)
            (correctedLocalizedMode_memLp (lt_of_lt_of_le zero_lt_one hfreq) u i)) ≤
        boundedPotentialForm (fun x => ∑ i, manufacturedSlabPotential rho H S freq scale u
          (Coulomb.position x i)) v := by
  have hf : 0 < freq := lt_of_lt_of_le zero_lt_one hfreq
  obtain ⟨γ,R,S₀,δ,C,hγ,hγsmall,hR,hS₀,hδ,hC,hgap⟩ :=
    manufacturedSlab_growing_complement_gap hp hv hdensity hfreq hrho hrelation
  obtain ⟨R₂,hR₂,hover⟩ := localizedOverlap_row_threshold
  refine ⟨γ,max R R₂,S₀,δ,C,hγ,hγsmall,hR.trans (le_max_left _ _),hS₀,hδ,hC,
    fun m D S H scale r ε hD hm hS hH hCH hscale hr hrH hrS hε u hsep hcoeff herr n v => ?_⟩
  have hs := hover D ((le_max_right _ _).trans hD) m hm
  have hbound := manufacturedSlab_residual_finite_rank_lower hdensity hrho
    (lt_of_lt_of_le zero_lt_one hH) (lt_of_lt_of_le zero_lt_one (hS₀.trans hS))
    hf hrelation hr hrH hrS hγ scale u hsep hs hδ.le hcoeff hε herr
    (hgap m D S H scale ((le_max_left _ _).trans hD) hm hS hH hCH hscale u hsep hcoeff)
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one (hS₀.trans hS)
  obtain ⟨B,hB⟩ := manufacturedSlabPotential_bounded hrho hHpos.le hSpos freq scale u
  exact manyElectron_projection_lower _
    (manufacturedSlabPotential_continuous hrho hHpos.le hSpos.le freq scale u)
    B hB _ _ _ hbound v

end ContinuumCoulomb

end

end OAI
