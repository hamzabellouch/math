import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningBoundarySystem
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningBoundaryCoercive
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningOuterWeight
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningScaleLimit

namespace OAI

/-! The actual normalized turning comparison has an inward boundary slope
in the same regularized norm used by the coupled Green estimate. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_inward_systems
    (ell : ℕ → ℕ) (h : ℝ) (b omega gamma r₀ d E : ℕ → ℝ) (R : ℝ)
    (hh : h^2 = 1) (hR : 0 < R) (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ b n ∧ b n ≤ 1 ∧
      |gamma n| ≤ 8 ∧ 2*r₀ n ≤ E n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n) ∧
      homogeneousSpectralLocalizationFrequency h (b n)
        ((ell n : ℝ)*(ell n+10)) (omega n) (r₀ n) = 0 ∧
      spectralLiouvilleSlope ((ell n : ℝ)*(ell n+10)) (r₀ n)*(d n)^3 = 1) :
    ∃ (φ : ℕ → ℕ) (K J : ℝ), StrictMono φ ∧ 0 ≤ K ∧ 0 ≤ J ∧ ∀ᶠ n in atTop,
      ∃ S : SpectralScalarBoundarySystem R (E (φ n)) K,
        S.k = spectralTurningRegularizedWeight h (b (φ n))
          ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (gamma (φ n)) (d (φ n)) ∧
        S.V = (fun r => (homogeneousSpectralLocalizationFrequency h (b (φ n))
          ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) r : ℂ)+Complex.I*(gamma (φ n) : ℂ)) ∧
        S.beta = (h : ℂ)*Complex.I*(Real.sqrt (homogeneousSpectralLocalizationFrequency h
          (b (φ n)) ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (E (φ n))) : ℂ) ∧
        (∀ z : ℂ, ∀ r ∈ Icc R (E (φ n)),
          spectralShellNorm (S.k r) (S.extension z r) ≤ J*S.k R*‖z‖) ∧
        ((S.U R).2/(S.U R).1).re ≤ -(1/24 : ℝ)*(S.k R)^2 ∧
        S.U (E (φ n)) = spectralOscillatoryData h (Real.sqrt (Real.sqrt
          (homogeneousSpectralLocalizationFrequency h (b (φ n))
            ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (E (φ n))))) := by
  have hddata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧
      0 ≤ (ell n : ℝ)*(ell n+10) ∧ |gamma n| ≤ 8 ∧
      homogeneousSpectralLocalizationFrequency h (b n) ((ell n : ℝ)*(ell n+10))
        (omega n) (r₀ n) = 0 ∧
      (r₀ n/8+2*((ell n : ℝ)*(ell n+10)+99/4)/(r₀ n)^3)*(d n)^3 = 1 := by
    filter_upwards [hdata] with n hn
    exact ⟨hn.1,hn.2.1,by positivity,hn.2.2.2.2.1,hn.2.2.2.2.2.2.2.1,hn.2.2.2.2.2.2.2.2⟩
  have hd0 := spectralTurningScale_tendsto (fun n => (ell n : ℝ)*(ell n+10)) r₀ d hr₀
    (hddata.mono (fun _ hn => ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.2.2⟩))
  have hout := spectralTurning_regularized_outer_weights h b
    (fun n => (ell n : ℝ)*(ell n+10)) omega gamma r₀ d 2 8 (by norm_num) hr₀ hddata
  have hinner : ∀ᶠ n in atTop,
      (spectralTurningRegularizedWeight h (b n) ((ell n : ℝ)*(ell n+10))
        (omega n) (gamma n) (d n) R)^2 =
      ‖spectralLiouvilleMomentum (-1) h (b n) ((ell n : ℝ)*(ell n+10)) (omega n) (gamma n) R‖ := by
    filter_upwards [hout,hr₀.eventually (eventually_ge_atTop (R+2)),
      hd0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn hr hd
    rw [hn.1 R hR (by linarith),Real.sq_sqrt (norm_nonneg _)]
  obtain ⟨φ,hφ,hin⟩ := spectralTurning_normalized_inward ell h b omega gamma r₀ d E R hh hR hr₀ hdata
  obtain ⟨ψ,K,J,hψ,hK,hJ,hsys⟩ := spectralTurning_boundary_systems
    (ell ∘ φ) h (b ∘ φ) (omega ∘ φ) (gamma ∘ φ) (r₀ ∘ φ) (d ∘ φ) (E ∘ φ) R hh hR
    (hr₀.comp hφ.tendsto_atTop) (hφ.tendsto_atTop.eventually hdata)
  refine ⟨φ ∘ ψ,K,J,hφ.comp hψ,hK,hJ,?_⟩
  filter_upwards [hsys,hψ.tendsto_atTop.eventually hin,
    (hφ.comp hψ).tendsto_atTop.eventually hinner] with n hsn hinn hkn
  obtain ⟨S,hk,hV,hbeta,hUE,hext⟩ := hsn
  refine ⟨S,hk,hV,hbeta,hext,?_,hUE⟩
  have hi := hinn S.U S.continuous_U (by simpa only [hV,Function.comp_def] using S.ode_U) hUE
  rw [hk]
  simp only [Function.comp_def] at hkn ⊢
  rw [hkn]
  exact hi

end DefocusingNLS

end OAI
