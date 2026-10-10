import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningInnerCone
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarTerminalUniqueness

namespace OAI

/-! The turning-channel logarithmic derivative estimate applies to every
comparison solution with the normalized outgoing terminal data. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_normalized_slope
    (ell : ℕ → ℕ) (h : ℝ) (b omega gamma r₀ d E : ℕ → ℝ) (R : ℝ)
    (hh : h^2 = 1) (hR : 0 < R) (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ b n ∧ b n ≤ 1 ∧
      |gamma n| ≤ 8 ∧ 2*r₀ n ≤ E n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n) ∧
      homogeneousSpectralLocalizationFrequency h (b n)
        ((ell n : ℝ)*(ell n+10)) (omega n) (r₀ n) = 0 ∧
      spectralLiouvilleSlope ((ell n : ℝ)*(ell n+10)) (r₀ n)*(d n)^3 = 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop,
      ∀ U : ℝ → ℂ × ℂ, ContinuousOn U (Icc R (E (φ n))) →
      (∀ r ∈ Icc R (E (φ n)), HasDerivAt U (spectralScalarField
        ((homogeneousSpectralLocalizationFrequency h (b (φ n))
          ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) r : ℂ)+Complex.I*(gamma (φ n) : ℂ))
        (U r)) r) →
      U (E (φ n)) = spectralOscillatoryData h (Real.sqrt (Real.sqrt
        (homogeneousSpectralLocalizationFrequency h (b (φ n))
          ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (E (φ n))))) →
      let p := spectralLiouvilleMomentum (-1) h (b (φ n))
        ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (gamma (φ n)) R
      (U R).1 ≠ 0 ∧
        ‖(U R).2/(U R).1+(p-(spectralLiouvilleSlope ((ell (φ n) : ℝ)*(ell (φ n)+10)) R : ℂ)/(4*p^2))‖ ≤
          eps*‖p‖ := by
  obtain ⟨q,φ,hφ,hq,hcone⟩ := spectralTurning_outgoing_relative_cone
    ell h b omega gamma r₀ d E R hh hR hr₀ hdata
  refine ⟨φ,hφ,?_⟩
  intro eps heps
  filter_upwards [hcone eps heps,hφ.tendsto_atTop.eventually hq,
    hφ.tendsto_atTop.eventually hdata,
    (hr₀.comp hφ.tendsto_atTop).eventually (eventually_ge_atTop R)] with n hcn hqn hdn hlarge
  intro U hUc hUD hUE
  change R ≤ r₀ (φ n) at hlarge
  have hRE : R ≤ E (φ n) := by linarith [hdn.1,hdn.2.2.2.2.2.1]
  let V := fun r => (homogeneousSpectralLocalizationFrequency h (b (φ n))
    ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) r : ℂ)+Complex.I*(gamma (φ n) : ℂ)
  have hV : ContinuousOn V (Icc R (E (φ n))) :=
    (Complex.continuous_ofReal.comp_continuousOn (fun r hr =>
      (homogeneousSpectralLocalizationFrequency_hasDerivAt h (b (φ n))
        ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) r
        (hR.trans_le hr.1)).continuousAt.continuousWithinAt)).add continuousOn_const
  have heq : q (φ n) R = U R := spectralScalar_unique_left R (E (φ n)) hRE V hV
    (q (φ n)) U hqn.1.continuousOn hUc
    (fun r hr => hqn.2.2.2 r ⟨hr.1.le,hr.2.le⟩)
    (fun r hr => hUD r ⟨hr.1.le,hr.2.le⟩) (hqn.2.1.trans hUE.symm)
  dsimp only at hcn ⊢
  rw [heq] at hcn
  refine ⟨hcn.1,?_⟩
  let p := spectralLiouvilleMomentum (-1) h (b (φ n))
    ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (gamma (φ n)) R
  let c := p-(spectralLiouvilleSlope ((ell (φ n) : ℝ)*(ell (φ n)+10)) R : ℂ)/(4*p^2)
  change ‖(U R).2/(U R).1+c‖ ≤ eps*‖p‖
  rw [show (U R).2/(U R).1+c = ((U R).2+c*(U R).1)/(U R).1 by
    field_simp [hcn.1]]
  rw [norm_div]
  exact (div_le_iff₀ (norm_pos_iff.mpr hcn.1)).mpr hcn.2

end DefocusingNLS

end OAI
