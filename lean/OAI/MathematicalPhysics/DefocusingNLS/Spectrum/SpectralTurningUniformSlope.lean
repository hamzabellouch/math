import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningUniformCone
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarTerminalUniqueness

namespace OAI

/-! The turning-channel logarithmic derivative estimate applies to every
comparison solution with the normalized outgoing terminal data. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_normalized_uniform_slope
    (ell : ℕ → ℕ) (h : ℝ) (b omega gamma r₀ d E : ℕ → ℝ) (R B : ℝ)
    (hh : h^2 = 1) (hR : 0 < R) (hRB : R ≤ B) (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ b n ∧ b n ≤ 1 ∧
      |gamma n| ≤ 8 ∧ 2*r₀ n ≤ E n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n) ∧
      homogeneousSpectralLocalizationFrequency h (b n)
        ((ell n : ℝ)*(ell n+10)) (omega n) (r₀ n) = 0 ∧
      spectralLiouvilleSlope ((ell n : ℝ)*(ell n+10)) (r₀ n)*(d n)^3 = 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop,
      ∀ L ∈ Icc R B, ∀ U : ℝ → ℂ × ℂ, ContinuousOn U (Icc L (E (φ n))) →
      (∀ r ∈ Icc L (E (φ n)), HasDerivAt U (spectralScalarField
        ((homogeneousSpectralLocalizationFrequency h (b (φ n))
          ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) r : ℂ)+Complex.I*(gamma (φ n) : ℂ))
        (U r)) r) →
      U (E (φ n)) = spectralOscillatoryData h (Real.sqrt (Real.sqrt
        (homogeneousSpectralLocalizationFrequency h (b (φ n))
          ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (E (φ n))))) →
      let p := spectralLiouvilleMomentum (-1) h (b (φ n))
        ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (gamma (φ n)) L
      (U L).1 ≠ 0 ∧
        ‖(U L).2/(U L).1+(p-(spectralLiouvilleSlope ((ell (φ n) : ℝ)*(ell (φ n)+10)) L : ℂ)/(4*p^2))‖ ≤
          eps*‖p‖ := by
  obtain ⟨q,φ,hφ,hq,hcone⟩ := spectralTurning_outgoing_uniform_relative_bounds
    ell h b omega gamma r₀ d E R B hh hR hRB hr₀ hdata
  refine ⟨φ,hφ,?_⟩
  intro eps heps
  obtain ⟨M,_hM,hc⟩ := hcone eps heps
  filter_upwards [hc,hφ.tendsto_atTop.eventually hq,
    hφ.tendsto_atTop.eventually hdata,
    (hr₀.comp hφ.tendsto_atTop).eventually (eventually_ge_atTop B)] with n hcn hqn hdn hlarge
  intro L hL U hUc hUD hUE
  have hcn := (hcn L hL).1
  change B ≤ r₀ (φ n) at hlarge
  have hL0 : 0 < L := hR.trans_le hL.1
  have hRE : L ≤ E (φ n) := by linarith [hdn.1,hdn.2.2.2.2.2.1,hL.2]
  let V := fun r => (homogeneousSpectralLocalizationFrequency h (b (φ n))
    ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) r : ℂ)+Complex.I*(gamma (φ n) : ℂ)
  have hV : ContinuousOn V (Icc L (E (φ n))) :=
    (Complex.continuous_ofReal.comp_continuousOn (fun r hr =>
      (homogeneousSpectralLocalizationFrequency_hasDerivAt h (b (φ n))
        ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) r
        (hL0.trans_le hr.1)).continuousAt.continuousWithinAt)).add continuousOn_const
  have heq : q (φ n) L = U L := spectralScalar_unique_left L (E (φ n)) hRE V hV
    (q (φ n)) U hqn.1.continuousOn hUc
    (fun r hr => hqn.2.2.2 r ⟨hL.1.trans hr.1.le,hr.2.le⟩)
    (fun r hr => hUD r ⟨hr.1.le,hr.2.le⟩) (hqn.2.1.trans hUE.symm)
  dsimp only at hcn ⊢
  rw [heq] at hcn
  refine ⟨hcn.1,?_⟩
  let p := spectralLiouvilleMomentum (-1) h (b (φ n))
    ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (gamma (φ n)) L
  let c := p-(spectralLiouvilleSlope ((ell (φ n) : ℝ)*(ell (φ n)+10)) L : ℂ)/(4*p^2)
  change ‖(U L).2/(U L).1+c‖ ≤ eps*‖p‖
  rw [show (U L).2/(U L).1+c = ((U L).2+c*(U L).1)/(U L).1 by
    field_simp [hcn.1]]
  rw [norm_div]
  exact (div_le_iff₀ (norm_pos_iff.mpr hcn.1)).mpr hcn.2

end DefocusingNLS

end OAI
