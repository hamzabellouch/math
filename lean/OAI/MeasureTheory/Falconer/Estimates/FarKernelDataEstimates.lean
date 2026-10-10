import OAI.MeasureTheory.Falconer.Estimates.FarData

namespace OAI

/-! # The proved analytic estimates on the actual far-branch data -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal ContDiff
open PlanarFalconer (PolicyDescriptor)

 theorem exists_far_data_stationary_band (m K L M : ℕ) (hML : 2*M ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4) :
    ∃ B C : ℝ, 1 ≤ B ∧ 0 ≤ C ∧ ∀ B' : ℝ, B ≤ B' →
      ∀ (D : JetStateFarData m B') (f g : DescriptorJetSymbol (m+1) K L D.F D.Dq)
        (w₀ : Sphere (m+3)) (b : ℕ), b ∈ Finset.Icc (D.a+9) (D.h+6) →
      ENNReal.ofReal D.prefactor *
        (∫⁻ z in comparableFarRegion (m+3) D.a D.h ∩ comparableLengthBand (m+3) b,
          ENNReal.ofReal ‖D.stationaryKernel f g w₀ M Ψ z‖ ∂D.originalMeasure) ≤
        D.collisionTerm w₀ (C*(B^K*D.Z⁻¹)^4) b := by
  obtain ⟨B,C,hB,hC,hbound⟩ := exists_jetState_far_band m K L M hML hΨ hs
  refine ⟨B,C,hB,hC,?_⟩
  intro B' hBB D f g w₀ b hb
  have hbr := Finset.mem_Icc.mp hb
  have hfreq := far_band_frequency_mono hbr.2 D.band_scale
  have hh := hbound D.F w₀ D.Q D.unit D.ρ D.profile D.N D.s D.lam D.regular D.N_pos
    D.policy D.σ D.J D.i D.q D.a b D.t (by omega) (by have := D.ht; have := D.tN; omega)
    (by have := D.ht; omega) D.masks (D.child_list b hb) D.separated
    D.Dq D.Dmask D.E D.Z D.Dq_nonneg D.Dmask_one D.Z_pos D.scale_one D.mask_scale
    (D.list_scale_mono hBB) hfreq f g D.X D.Y D.X_length D.Y_length
    (comparableFarRegion (m+3) D.a D.h ∩ comparableLengthBand (m+3) b)
    ((comparableFarRegion_measurable _ _ _).inter (comparableLengthBand_measurable _ _))
    inter_subset_right
  exact hh

 theorem exists_far_data_replacement
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m K L M : ℕ) (hM : 1 ≤ M) (hML : 2*M+(m+2)+1 ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ s, 0 ≤ Ψ s)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ s, Ψ s ≤ W) :
    ∃ B C : ℝ, 1 ≤ B ∧ 0 ≤ C ∧ ∀ B' : ℝ, B ≤ B' →
      ∀ (D : JetStateFarData m B'), -D.κ*(M:ℝ)+2*(m+3) ≤ -D.loss →
      ∀ (f g : DescriptorJetSymbol (m+1) K L D.F D.Dq) (w₀ : Sphere (m+3))
        (z : (Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3))),
      z ∈ comparableFarRegion (m+3) D.a D.h →
      ‖D.kernel f g w₀ Ψ z-D.stationaryKernel f g w₀ M Ψ z‖ ≤
        C*(B^K*D.Z⁻¹)^4*((2:ℝ)^D.N)^(-D.loss) := by
  obtain ⟨B,C,hB,hC,hbound⟩ := exists_jetState_original_stationary_power hgnomonic hquadratic
    m K L M hM hML hΨ hpos hs hW hΨW
  refine ⟨B,C,hB,hC,?_⟩
  intro B' hBB D horder f g w₀ z hz
  obtain ⟨hd₁,hd₂⟩ := comparableFarRegion_lower hz
  have hregime (d : ℝ) (hd : farMinimumLength (m+3) D.h ≤ d) :=
    shell_regime_of_lower_distance hs (D.t:ℝ) (2*(D.E+D.Dq)) ((2:ℝ)^D.N) D.κ
      (farMinimumLength (m+3) D.h) d D.minimumLength_pos hd
      (by simpa only [Real.rpow_natCast] using D.shell_one)
      (by simpa only [Real.rpow_natCast] using D.shell_scale)
  simpa only [JetStateFarData.kernel,JetStateFarData.stationaryKernel,Real.rpow_natCast] using
    hbound D.F D.Q D.ρ (fun t => D.profile (t/D.N)) D.N D.σ D.J D.i D.masks D.separated
    D.Dq D.Dmask D.E D.Z D.Dq_nonneg D.Dmask_one D.Z_pos D.scale_one D.mask_scale
    (D.list_scale_mono hBB) f g w₀ D.t ((2:ℝ)^D.N) D.κ D.loss D.base_one D.loss_nonneg horder
    D.scale_upper z (fun r hr => ⟨hregime _ hd₁ r hr,hregime _ hd₂ r hr⟩)

 theorem exists_far_data_noncomparable
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m K L M q : ℕ) (hM : 1 ≤ M) (hML : 2*M+(m+2)+1 ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ s, 0 ≤ Ψ s)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ s, Ψ s ≤ W) :
    ∃ B H S : ℝ, 1 ≤ B ∧ 0 ≤ H ∧ 0 ≤ S ∧ ∀ B' : ℝ, B ≤ B' →
      ∀ (D : JetStateFarData m B'), D.loss ≤ D.κ*(((m+2:ℕ):ℝ)/2+(q:ℝ)) →
      -D.κ*(M:ℝ)+2*(m+3) ≤ -D.loss →
      ∀ (f g : DescriptorJetSymbol (m+1) K L D.F D.Dq) (w₀ : Sphere (m+3))
        (z : (Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3))),
      z ∈ leftNoncomparableFar (m+3) D.a D.h ∪ rightNoncomparableFar (m+3) D.a D.h →
      let C₁ := (B^K*D.Z⁻¹)^2
      let C₂ := ((descriptorJetBound (m+3) K)^K*D.Z⁻¹)^2
      let V := (sphereMeasure (m+3)).real univ
      ‖D.kernel f g w₀ Ψ z‖ ≤
        (H*C₁*C₂*V*(2:ℝ)^q+4*W*S*C₁*(2*(max C₁ C₂*V)+S*C₁))*((2:ℝ)^D.N)^(-D.loss) := by
  obtain ⟨B,H,S,hB,hH,hS,hbound⟩ := exists_jetState_noncomparable_original_pointwise
    hgnomonic hquadratic m K L M q hM hML hΨ hpos hs hW hΨW
  refine ⟨B,H,S,hB,hH,hS,?_⟩
  intro B' hBB D hloss horder f g w₀ z hz
  have apply_bound (f g : DescriptorJetSymbol (m+1) K L D.F D.Dq)
      (z : (Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3)))
      (hd : farMinimumLength (m+3) D.h ≤ dist z.1.1 z.1.2)
      (hsep : 2*dist z.2.1 z.2.2 ≤ dist z.1.1 z.1.2) :=
    hbound D.F D.F D.Q D.ρ (fun t => D.profile (t/D.N)) D.N D.σ D.J D.i D.masks
      D.separated D.separated D.Dq D.Dmask D.E D.Z D.Z D.Dq_nonneg D.Dmask_one
      D.Z_pos D.Z_pos D.scale_one D.mask_scale (D.list_scale_mono hBB) f g w₀
      D.t ((2:ℝ)^D.N) D.κ D.loss D.base_one D.loss_nonneg hloss horder D.scale_upper z
      (D.minimumLength_pos.trans_le hd) hsep
      (by simpa only [Real.rpow_natCast] using (D.large_scale.trans
        (mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ (2:ℝ)^D.t))))
      (by simpa only [Real.rpow_natCast] using (D.large_frequency.trans
        (mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ (2:ℝ)^D.t))))
      (shell_regime_of_lower_distance hs D.t (2*(D.E+D.Dq)) ((2:ℝ)^D.N) D.κ
        (farMinimumLength (m+3) D.h) _ D.minimumLength_pos hd
        (by simpa only [Real.rpow_natCast] using D.shell_one)
        (by simpa only [Real.rpow_natCast] using D.shell_scale))
  rcases hz with hz | hz
  · exact apply_bound f g z (leftNoncomparableFar_lower hz) hz.2.le
  · have hh := apply_bound g f (z.2,z.1) (rightNoncomparableFar_lower hz) hz.2.le
    simpa only [JetStateFarData.kernel,jetStateOriginalKernel_swap] using hh

end Falconer

end OAI
