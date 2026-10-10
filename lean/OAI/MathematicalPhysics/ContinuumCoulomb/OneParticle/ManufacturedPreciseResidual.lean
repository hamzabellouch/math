import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedResidualGap

namespace OAI

/-! The uniform spectral gap uses a fixed threshold, while residual precision
uses the actual, smaller counterterm ratio chosen by the reduction. -/

noncomputable section
namespace ContinuumCoulomb

theorem manufacturedSlab_uniform_precise_manyElectron_lower
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity)
    {freq rho : ℝ} (hfreq : 1 ≤ freq) (hrho : 0 ≤ rho) (hrelation : freq^2 = 4*Real.pi*rho) :
    ∃ γ R S₀ δ C : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ 8 ≤ R ∧ 1 ≤ S₀ ∧ 0 < δ ∧ 0 < C ∧
      ∀ (m : ℕ) (D S H scale r ε η : ℝ), R ≤ D → (m : ℝ) ≤ Real.exp ((19/320:ℝ)*D) →
      S₀ ≤ S → 1 ≤ H → C*S^3 ≤ H → 0 ≤ scale → 0 < r → r ≤ H/2 → r ≤ S → 0 ≤ ε → 0 ≤ η → η ≤ δ →
      ∀ u : Fin m → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      (∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ η) →
      4*(m:ℝ)^2*(∑ j, manufacturedOrbitalSquaredError rho H S freq η D r u j) ≤ ε^2 →
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
    fun m D S H scale r ε η hD hm hS hH hCH hscale hr hrH hrS hε hη hηδ u hsep hcoeff herr n v => ?_⟩
  have hs := hover D ((le_max_right _ _).trans hD) m hm
  have hbound := manufacturedSlab_residual_finite_rank_lower hdensity hrho
    (lt_of_lt_of_le zero_lt_one hH) (lt_of_lt_of_le zero_lt_one (hS₀.trans hS))
    hf hrelation hr hrH hrS hγ scale u hsep hs hη hcoeff hε herr
    (hgap m D S H scale ((le_max_left _ _).trans hD) hm hS hH hCH hscale u hsep (fun i => ⟨(hcoeff i).1,(hcoeff i).2.trans hηδ⟩))
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one (hS₀.trans hS)
  obtain ⟨B,hB⟩ := manufacturedSlabPotential_bounded hrho hHpos.le hSpos freq scale u
  exact manyElectron_projection_lower _
    (manufacturedSlabPotential_continuous hrho hHpos.le hSpos.le freq scale u)
    B hB _ _ _ hbound v


end ContinuumCoulomb

end

end OAI
