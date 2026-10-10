import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningUniformGreen
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNormalizedBoundarySystem

namespace OAI

/-! The constructed turning comparison supplies a scalar boundary system
and a uniform extension bound, ready for coupled absorption. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_uniform_boundary_systems
    (ell : ℕ → ℕ) (h : ℝ) (b omega gamma r₀ d E : ℕ → ℝ) (R B : ℝ)
    (hh : h^2 = 1) (hR : 0 < R) (hRB : R ≤ B) (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ b n ∧ b n ≤ 1 ∧
      |gamma n| ≤ 8 ∧ 2*r₀ n ≤ E n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n) ∧
      homogeneousSpectralLocalizationFrequency h (b n)
        ((ell n : ℝ)*(ell n+10)) (omega n) (r₀ n) = 0 ∧
      spectralLiouvilleSlope ((ell n : ℝ)*(ell n+10)) (r₀ n)*(d n)^3 = 1) :
    ∃ (φ : ℕ → ℕ) (K J : ℝ), StrictMono φ ∧ 0 ≤ K ∧ 0 ≤ J ∧ ∀ᶠ n in atTop, ∀ L ∈ Icc R B,
      ∃ S : SpectralScalarBoundarySystem L (E (φ n)) K,
        S.k = spectralTurningRegularizedWeight h (b (φ n))
          ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (gamma (φ n)) (d (φ n)) ∧
        S.V = (fun r => (homogeneousSpectralLocalizationFrequency h (b (φ n))
          ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) r : ℂ)+Complex.I*(gamma (φ n) : ℂ)) ∧
        S.beta = (h : ℂ)*Complex.I*(Real.sqrt (homogeneousSpectralLocalizationFrequency h
          (b (φ n)) ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (E (φ n))) : ℂ) ∧
        S.U (E (φ n)) = spectralOscillatoryData h (Real.sqrt (Real.sqrt
          (homogeneousSpectralLocalizationFrequency h (b (φ n))
            ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (E (φ n))))) ∧
        ∀ z : ℂ, ∀ r ∈ Icc L (E (φ n)),
          spectralShellNorm (S.k r) (S.extension z r) ≤ J*S.k L*‖z‖ := by
  obtain ⟨q,φ,hφ,hq,K,J,hK,hJ,hall⟩ := spectralTurning_outgoing_green_extension_uniform_inner
    ell h b omega gamma r₀ d E R B hh hR hRB hr₀ hdata
  refine ⟨φ,K,J,hφ,hK,hJ,?_⟩
  filter_upwards [hall,hφ.tendsto_atTop.eventually hq,hφ.tendsto_atTop.eventually hdata,
    (hr₀.comp hφ.tendsto_atTop).eventually (eventually_ge_atTop B)] with n hn hqn hdn hlarge
  intro L hL
  obtain ⟨Y,W,hYc,hYR,hYD,hW,hdet,hgreen,hext⟩ := hn L hL
  obtain ⟨hrp,hd,hb,hb1,hg,hRE',hscale,hroot,hdscale⟩ := hdn
  change B ≤ r₀ (φ n) at hlarge
  have hL0 : 0 < L := hR.trans_le hL.1
  have hRE : L ≤ E (φ n) := by linarith [hL.2]
  have hdp : 0 < d (φ n) := by
    apply lt_of_le_of_ne hd
    intro he
    rw [← he] at hdscale
    norm_num at hdscale
  let k := spectralTurningRegularizedWeight h (b (φ n))
    ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (gamma (φ n)) (d (φ n))
  let V := fun r => (homogeneousSpectralLocalizationFrequency h (b (φ n))
    ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) r : ℂ)+Complex.I*(gamma (φ n) : ℂ)
  have hk : ContinuousOn k (Icc L (E (φ n))) :=
    (spectralTurningRegularizedWeight_continuousOn h (b (φ n))
      ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (gamma (φ n)) (d (φ n))).mono
      (fun r hr => hL0.trans_le hr.1)
  have hkp : ∀ r ∈ Icc L (E (φ n)), 0 < k r := fun r _ =>
    spectralTurningRegularizedWeight_pos h (b (φ n))
      ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (gamma (φ n)) (d (φ n)) r hdp
  let S := spectralNormalizedBoundarySystem L (E (φ n)) K h
    (homogeneousSpectralLocalizationFrequency h (b (φ n))
      ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (E (φ n))) hRE
    k V Y (q (φ n)) W hk hkp hYc.continuousOn hqn.1.continuousOn hYD (fun t ht => hqn.2.2.2 t ⟨hL.1.trans ht.1,ht.2⟩)
    hYR hqn.2.1 hW hdet hgreen
  exact ⟨S,rfl,rfl,rfl,hqn.2.1,hext⟩

end DefocusingNLS

end OAI
