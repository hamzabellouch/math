import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedUniformGap

namespace OAI

/-! The complementary gap remains uniform when the slab thickness grows
to obtain the required orbital residual accuracy. -/

noncomputable section
namespace ContinuumCoulomb

theorem manufacturedSlab_growing_complement_gap
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity)
    {freq rho : ℝ} (hfreq : 1 ≤ freq) (hrho : 0 ≤ rho) (hrelation : freq^2 = 4*Real.pi*rho) :
    ∃ γ R S₀ δ C : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ 8 ≤ R ∧ 1 ≤ S₀ ∧ 0 < δ ∧ 0 < C ∧
      ∀ (m : ℕ) (D S H scale : ℝ), R ≤ D → (m : ℝ) ≤ Real.exp ((19/320:ℝ)*D) →
      S₀ ≤ S → 1 ≤ H → C*S^3 ≤ H → 0 ≤ scale → ∀ u : Fin m → PlanarPosition,
      (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      (∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ) →
      ∀ v : Coulomb.H1Vector 1,
      (∀ s i, inner ℂ (oneElectronOrbitalLp (correctedLocalizedMode freq u i)
        (correctedLocalizedMode_memLp (lt_of_lt_of_le zero_lt_one hfreq) u i))
          (h1Coordinates v (Sum.inl s)) = 0) →
      (-1/2+freq/2+γ/2)*Coulomb.mass v ≤
        boundedPotentialForm (fun x => manufacturedSlabPotential rho H S freq scale u
          (oneElectronCoordinates x)) v := by
  have hf : 0 < freq := lt_of_lt_of_le zero_lt_one hfreq
  obtain ⟨γ,hγ,hsmall,hbound⟩ := manufacturedSlab_corrected_complement_lower hp hv hdensity
  let η := γ/(16*freq)
  obtain ⟨hη,hfreqη,hdom⟩ := manufactured_gap_parameter_bounds hγ hsmall hfreq
  obtain ⟨R₁,hR₁,hplanar⟩ := planar_projection_loss_threshold hγ hη (by positivity : 0 < γ/16)
  obtain ⟨R₂,hR₂,hover⟩ := localizedOverlap_row_threshold
  obtain ⟨S₀,hS₀,hvertical⟩ := vertical_projection_loss_threshold hf η (by positivity : 0 < γ/16)
  let δ := γ/(16*(PlanarSobolev.wellBound+1))
  let C := max 1 (96*Real.pi*rho/γ)
  have hw := PlanarSobolev.wellBound_nonnegative
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨γ,max R₁ R₂,S₀,δ,C,hγ,hsmall,hR₁.trans (le_max_left _ _),hS₀,hδ,hC,
    fun m D S H scale hD hm hS hH hCH hscale u hsep hcoeff v ho => ?_⟩
  have hD₁ : R₁ ≤ D := (le_max_left _ _).trans hD
  have hD₂ : R₂ ≤ D := (le_max_right _ _).trans hD
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one (hS₀.trans hS)
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hδloss : δ*PlanarSobolev.wellBound ≤ γ/16 := by
    have hid : δ*(PlanarSobolev.wellBound+1) = γ/16 := by
      dsimp [δ]
      field_simp
    exact (mul_le_mul_of_nonneg_left (by linarith :
      PlanarSobolev.wellBound ≤ PlanarSobolev.wellBound+1) hδ.le).trans_eq hid
  have hslab : 6*Real.pi*rho*S^3/H ≤ γ/16 := by
    have hh : 96*Real.pi*rho*S^3/γ ≤ H := by
      calc
        _ = (96*Real.pi*rho/γ)*S^3 := by ring
        _ ≤ C*S^3 := mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hSpos.le _)
        _ ≤ H := hCH
    have hh' := (div_le_iff₀ hγ).mp hh
    apply (div_le_iff₀ hHpos).mpr
    nlinarith only [hh']
  have hloss : manufacturedSpectralLoss γ m D η freq S rho H δ ≤ γ/2 := by
    have hp' := hplanar D hD₁ m hm
    have hv' := (hvertical S hS).2
    unfold manufacturedSpectralLoss
    dsimp [η] at hv' ⊢
    linarith [hfreqη]
  exact hbound m D η freq S rho H scale δ (hR₁.trans hD₁) hη hf hSpos hrho hHpos
    hscale hδ.le hrelation (hvertical S hS).1 u hsep hcoeff
    (hdom _ (hover D hD₂ m hm)) (hover D hD₂ m hm) hloss v ho

end ContinuumCoulomb

end

end OAI
