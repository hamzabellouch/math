import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleFrequencyJet
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralComplexSqrtScale
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningUniformLimit

namespace OAI

/-! The complex forbidden-side momentum, after the actual turning scaling,
converges to the positive Airy momentum at every fixed observation point. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_negative_momentum_tendsto
    (h : ℝ) (b eta omega gamma r₀ d : ℕ → ℝ) (T G : ℝ) (hT : 0 < T)
    (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ eta n ∧ |gamma n| ≤ G ∧
      homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n) = 0 ∧
      (r₀ n/8+2*(eta n+99/4)/(r₀ n)^3)*(d n)^3 = 1) :
    Tendsto (fun n => (d n : ℂ)*spectralLiouvilleMomentum (-1) h (b n) (eta n)
      (omega n) (gamma n) (r₀ n-d n*T)) atTop (𝓝 (Real.sqrt T : ℂ)) := by
  let Z := fun n => -spectralTurningCoefficient h (b n) (eta n) (omega n) (gamma n) (r₀ n) (d n) (-T)
  have hu := (spectralTurningCoefficient_uniform_limit h b eta omega gamma r₀ d T G hT.le
    hr₀ hdata).tendsto_at (show -T ∈ Icc (-T) T from ⟨le_rfl,by linarith⟩)
  have hZ : Tendsto Z atTop (𝓝 (T : ℂ)) := by
    simpa only [Z,Complex.ofReal_neg,neg_neg] using hu.neg
  have hroot : Tendsto (fun n => Complex.sqrt (Z n)) atTop (𝓝 (Real.sqrt T : ℂ)) := by
    have hs := (Complex.continuousAt_sqrt (z := (T : ℂ)) (Or.inl (by simpa using hT.le))).tendsto.comp hZ
    have he : Complex.sqrt (T : ℂ) = (Real.sqrt T : ℂ) := by
      apply Complex.sqrt_of_nonneg
      exact_mod_cast hT.le
    simpa only [he,Function.comp_def] using hs
  apply hroot.congr'
  filter_upwards [hdata,((Complex.continuous_re.tendsto (T : ℂ)).comp hZ).eventually
    (lt_mem_nhds hT)] with n hn hre
  have hdp : 0 < d n := by
    apply lt_of_le_of_ne hn.2.1
    intro he
    have hs := hn.2.2.2.2.2
    rw [← he] at hs
    norm_num at hs
  let z := spectralWKBSquaredMomentum (-1)
    (homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n-d n*T)) (gamma n)
  have he : Z n = (d n : ℂ)^2*z := by
    dsimp only [Z,z,spectralTurningCoefficient,spectralWKBSquaredMomentum]
    simp only [mul_neg,sub_eq_add_neg]
    push_cast
    ring
  have hz : 0 < z.re := by
    dsimp only [Function.comp_def] at hre
    rw [he] at hre
    simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero] at hre
    nlinarith [sq_nonneg (d n)]
  rw [he,spectralComplexSqrt_scale (d n) hdp z hz]
  rfl

end DefocusingNLS

end OAI
