import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningInnerCone
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRobinRelative

namespace OAI

/-! The same actual scalar outgoing family has relative logarithmic slope
minus one at every fixed inner radius along its selected subsequence. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_outgoing_logarithmic_limit
    (ell : ℕ → ℕ) (h : ℝ) (b omega gamma r₀ d E : ℕ → ℝ) (R : ℝ)
    (hh : h^2 = 1) (hR : 0 < R) (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ b n ∧ b n ≤ 1 ∧
      |gamma n| ≤ 8 ∧ 2*r₀ n ≤ E n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n) ∧
      homogeneousSpectralLocalizationFrequency h (b n)
        ((ell n : ℝ)*(ell n+10)) (omega n) (r₀ n) = 0 ∧
      spectralLiouvilleSlope ((ell n : ℝ)*(ell n+10)) (r₀ n)*(d n)^3 = 1) :
    ∃ (q : ℕ → ℝ → ℂ × ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ᶠ n in atTop, Continuous (q n) ∧
        q n (E n) = spectralOscillatoryData h (Real.sqrt (Real.sqrt
          (homogeneousSpectralLocalizationFrequency h (b n)
            ((ell n : ℝ)*(ell n+10)) (omega n) (E n)))) ∧
        spectralScalarFlux (q n (E n)) = h ∧
        ∀ t ∈ Icc R (E n), HasDerivAt (q n) (spectralScalarField
          ((homogeneousSpectralLocalizationFrequency h (b n)
            ((ell n : ℝ)*(ell n+10)) (omega n) t : ℂ)+Complex.I*(gamma n : ℂ))
          (q n t)) t) ∧
      (∀ᶠ n in atTop, (q (φ n) R).1 ≠ 0) ∧
      Tendsto (fun n => ((q (φ n) R).2/(q (φ n) R).1)/
        spectralLiouvilleMomentum (-1) h (b (φ n)) ((ell (φ n) : ℝ)*(ell (φ n)+10))
          (omega (φ n)) (gamma (φ n)) R) atTop (𝓝 (-1)) := by
  obtain ⟨q,φ,hφ,hq,hcone⟩ := spectralTurning_outgoing_relative_cone
    ell h b omega gamma r₀ d E R hh hR hr₀ hdata
  refine ⟨q,φ,hφ,hq,(hcone 1 (by norm_num)).mono (fun _ hn => hn.1),?_⟩
  have hrt := hr₀.comp hφ.tendsto_atTop
  have hcorr : Tendsto (fun n => 16/(R*r₀ (φ n))) atTop (𝓝 0) := by
    convert (tendsto_inv_atTop_zero.comp hrt).const_mul (16/R) using 1
    · funext n
      simp only [Function.comp_def,div_eq_mul_inv,mul_inv_rev]
      ring
    · ring_nf
  rw [Metric.tendsto_nhds]
  intro eps heps
  filter_upwards [hcone (eps/2) (by positivity), hφ.tendsto_atTop.eventually hdata,
    hrt.eventually (eventually_ge_atTop (2*R)),
    hcorr.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < eps/2))] with n hn hd hl hcn
  dsimp only [Function.comp_def] at hl
  let eta := (ell (φ n) : ℝ)*(ell (φ n)+10)
  let p := spectralLiouvilleMomentum (-1) h (b (φ n)) eta (omega (φ n)) (gamma (φ n)) R
  let c : ℂ := (spectralLiouvilleSlope eta R : ℂ)/(4*p^2)
  have heta : 0 ≤ eta := by dsimp only [eta]; positivity
  have hRh : R ≤ r₀ (φ n)/2 := by linarith
  have hz : homogeneousSpectralLocalizationFrequency h (b (φ n)) eta (omega (φ n))
      (r₀ (φ n)) = 0 := hd.2.2.2.2.2.2.2.1
  have hpre := spectralTurning_far_momentum_re_lower h (b (φ n)) eta (omega (φ n))
    (gamma (φ n)) (r₀ (φ n)) R heta hd.1 hR hRh hz
  have hp : p ≠ 0 := by
    intro hp0
    change r₀ (φ n)/16 ≤ p.re at hpre
    rw [hp0,Complex.zero_re] at hpre
    linarith [hd.1]
  have hc : ‖c/p‖ ≤ 16/(R*r₀ (φ n)) :=
    spectralTurning_log_correction_bound h (b (φ n)) eta (omega (φ n))
      (gamma (φ n)) (r₀ (φ n)) R heta hd.1 hR hRh hz
  have he := spectralRobin_relative_residual p c (q (φ n) R) (eps/2) hn.1 hp hn.2
  change dist (((q (φ n) R).2/(q (φ n) R).1)/p) (-1) < eps
  rw [dist_eq_norm,sub_neg_eq_add]
  exact (he.trans (add_le_add le_rfl hc)).trans_lt (by linarith)

end DefocusingNLS

end OAI
