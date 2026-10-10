import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningConeError
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleUniformError

namespace OAI

/-! A single cutoff controls the reflected error at every left endpoint
of a fixed shell. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_eventual_uniform_error
    (eps : ℝ) (heps : 0 < eps) (h : ℝ) (b eta omega gamma r₀ d : ℕ → ℝ)
    (R B : ℝ) (hR : 0 < R) (hRB : R ≤ B)
    (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ eta n ∧
      homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n) = 0 ∧
      spectralLiouvilleSlope (eta n) (r₀ n)*(d n)^3 = 1) :
    ∀ᶠ M : ℝ in atTop, 32 ≤ M ∧ ∀ᶠ n in atTop,
      ∀ r ∈ Icc R B,
        spectralLiouvilleConeError h (b n) (eta n) (omega n) (gamma n) r (r₀ n-M*d n) ≤ eps := by
  have hlow := spectralTurning_eventual_relative_error (eps/2) (by positivity)
    h b eta omega gamma r₀ d R hR hr₀ hdata
  have hhigh := spectralTurning_eventual_relative_error (eps/2) (by positivity)
    h b eta omega gamma r₀ d B (hR.trans_le hRB) hr₀ hdata
  have hd := spectralTurningScale_tendsto eta r₀ d hr₀
    (hdata.mono (fun _ hn => ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.2⟩))
  filter_upwards [hlow,hhigh] with M hMl hMh
  refine ⟨hMl.1,?_⟩
  filter_upwards [hMl.2,hMh.2,hdata,
    hd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hr₀.eventually (eventually_ge_atTop (B+M+1))] with n hln hhn hdn hds hrn
  have hdp : 0 < d n := by
    apply lt_of_le_of_ne hdn.2.1
    intro he
    have hx := hdn.2.2.2.2
    rw [← he] at hx
    norm_num at hx
  have hMp : 0 < M := by linarith [hMl.1]
  have hBc : B ≤ r₀ n-M*d n := by nlinarith
  have hF : ∀ t ∈ Icc R (r₀ n-M*d n),
      0 < (-1)*homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) t := by
    intro t ht
    have hlt : t < r₀ n := by nlinarith [ht.2]
    have hm := homogeneousSpectralLocalizationFrequency_strictMono h (b n) (eta n) (omega n)
      hdn.2.2.1 (hR.trans_le ht.1) hdn.1 hlt
    rw [hdn.2.2.2.1] at hm
    linarith
  have hh := spectralLiouvilleConeError_uniform h (b n) (eta n) (omega n) (gamma n)
    R B (r₀ n-M*d n) (eps/2) hR hRB hBc hF hln hhn
  rw [show 2*(eps/2) = eps by ring] at hh
  exact hh

end DefocusingNLS

end OAI
