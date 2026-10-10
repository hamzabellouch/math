import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedGapScale

namespace OAI

/-! A single positive complementary gap for every admissible manufactured
configuration. Localization widths and error tolerances are selected before
the instance and before the number of wells. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

theorem localizedOverlap_row_threshold :
    ∃ R : ℝ, 8 ≤ R ∧ ∀ D : ℝ, R ≤ D → ∀ m : ℕ,
      (m : ℝ) ≤ Real.exp ((19/320:ℝ)*D) → m*localizedOverlapBound D ≤ 1/2 := by
  have he : Tendsto (fun D : ℝ => Real.exp (-(269/320:ℝ)*D)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,id_eq,neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<269/320))
  have hl : Tendsto (fun D : ℝ => planarOverlapConstant*Real.exp (-(269/320:ℝ)*D))
      atTop (𝓝 0) := by simpa using he.const_mul planarOverlapConstant
  obtain ⟨R,hR⟩ := Filter.eventually_atTop.1
    (hl.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)))
  refine ⟨max 8 R,le_max_left _ _,fun D hD m hm => ?_⟩
  have hb : (m:ℝ)*localizedOverlapBound D ≤
      planarOverlapConstant*Real.exp (-(269/320:ℝ)*D) := by
    unfold localizedOverlapBound
    calc
      _ ≤ Real.exp ((19/320:ℝ)*D)*(planarOverlapConstant*Real.exp (-(9/10:ℝ)*D)) :=
        mul_le_mul_of_nonneg_right hm
          (mul_nonneg planarOverlapConstant_nonnegative (Real.exp_pos _).le)
      _ = _ := by rw [mul_left_comm,← Real.exp_add]; congr 2; ring
  exact hb.trans (hR D ((le_max_right _ _).trans hD)).le

theorem manufacturedSlab_uniform_complement_gap
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity)
    {freq rho : ℝ} (hfreq : 1 ≤ freq) (hrho : 0 ≤ rho) (hrelation : freq^2 = 4*Real.pi*rho) :
    ∃ γ R S δ H₀ : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ 8 ≤ R ∧ 1 ≤ S ∧ 0 < δ ∧ 0 < H₀ ∧
      ∀ (m : ℕ) (D H scale : ℝ), R ≤ D → (m : ℝ) ≤ Real.exp ((19/320:ℝ)*D) →
      H₀ ≤ H → 0 ≤ scale → ∀ u : Fin m → PlanarPosition,
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
  obtain ⟨S,hS,hvertical⟩ := vertical_projection_loss_threshold hf η (by positivity : 0 < γ/16)
  let δ := γ/(16*(PlanarSobolev.wellBound+1))
  let H₀ := max 1 (96*Real.pi*rho*S^3/γ)
  have hw := PlanarSobolev.wellBound_nonnegative
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hH₀ : 0 < H₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨γ,max R₁ R₂,S,δ,H₀,hγ,hsmall,hR₁.trans (le_max_left _ _),hS,hδ,hH₀,
    fun m D H scale hD hm hH hscale u hsep hcoeff v ho => ?_⟩
  have hD₁ : R₁ ≤ D := (le_max_left _ _).trans hD
  have hD₂ : R₂ ≤ D := (le_max_right _ _).trans hD
  have hHpos : 0 < H := hH₀.trans_le hH
  have hδloss : δ*PlanarSobolev.wellBound ≤ γ/16 := by
    have hid : δ*(PlanarSobolev.wellBound+1) = γ/16 := by
      dsimp [δ]
      field_simp
    exact (mul_le_mul_of_nonneg_left (by linarith :
      PlanarSobolev.wellBound ≤ PlanarSobolev.wellBound+1) hδ.le).trans_eq hid
  have hslab : 6*Real.pi*rho*S^3/H ≤ γ/16 := by
    have hh : 96*Real.pi*rho*S^3/γ ≤ H := (le_max_right _ _).trans hH
    have hh' := (div_le_iff₀ hγ).mp hh
    apply (div_le_iff₀ hHpos).mpr
    nlinarith only [hh']
  have hloss : manufacturedSpectralLoss γ m D η freq S rho H δ ≤ γ/2 := by
    have hp := hplanar D hD₁ m hm
    have hv := (hvertical S le_rfl).2
    unfold manufacturedSpectralLoss
    dsimp [η] at hv ⊢
    linarith [hfreqη]
  exact hbound m D η freq S rho H scale δ (hR₁.trans hD₁) hη hf
    (lt_of_lt_of_le zero_lt_one hS) hrho hHpos hscale hδ.le hrelation
    (hvertical S le_rfl).1 u hsep hcoeff
    (hdom _ (hover D hD₂ m hm)) (hover D hD₂ m hm) hloss v ho

end ContinuumCoulomb

end

end OAI
