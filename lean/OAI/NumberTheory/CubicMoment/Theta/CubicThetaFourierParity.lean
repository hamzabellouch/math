import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGaussParity
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRegularizedFourier

namespace OAI

/-! Evenness of the literal finite-row coefficients propagates to their
arithmetic continuation and to the actual theta residue. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

theorem cubicThetaFrequencyContinuation_neg_germ {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 1<s.re) :
    cubicThetaFrequencyContinuation (-h)=ᶠ[𝓝[≠] s] cubicThetaFrequencyContinuation h := by
  apply cubicThetaMeromorphic_identity
    (fun z hz => cubicThetaFrequencyContinuation_meromorphic (neg_ne_zero.mpr hh) hz)
    (fun z hz => cubicThetaFrequencyContinuation_meromorphic hh hz)
    (convex_halfSpace_re_gt 1).isPreconnected (z₀:=(4:ℂ))
    (by change 1<(4:ℂ).re; norm_num) hs
  have hn : ∀ᶠ z : ℂ in 𝓝 4, 3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hn] with z hz
  rw [cubicThetaFrequencyContinuation_right _ hz,cubicThetaFrequencyContinuation_right _ hz]
  exact cubicThetaFrequencyDirichlet_neg h z

theorem cubicThetaArithmeticFourierResidue_neg {h : Eisenstein} (hh : h≠0) :
    cubicThetaArithmeticFourierResidue (-h) (4/3)=cubicThetaArithmeticFourierResidue h (4/3) := by
  have hn := cubicThetaFrequencyContinuation_residue (neg_ne_zero.mpr hh)
    (σ:=(4/3:ℝ)) (by norm_num) (by norm_num)
  have hp := cubicThetaFrequencyContinuation_residue hh
    (σ:=(4/3:ℝ)) (by norm_num) (by norm_num)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hn hp
  have he : (fun z : ℂ => (z-4/3)*cubicThetaFrequencyContinuation (-h) z)=ᶠ[𝓝[≠] (4/3:ℂ)]
      (fun z => (z-4/3)*cubicThetaFrequencyContinuation h z) := by
    filter_upwards [cubicThetaFrequencyContinuation_neg_germ hh (s:=(4/3:ℂ)) (by norm_num)]
      with z hz
    rw [hz]
  exact tendsto_nhds_unique (hn.congr' he) hp

theorem cubicThetaRegularizedFrequency_neg {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 1<s.re) :
    cubicThetaRegularizedFrequency (-h) s=cubicThetaRegularizedFrequency h s := by
  have hn := (cubicThetaRegularizedFrequency_analytic (neg_ne_zero.mpr hh) s hs).continuousAt
  have hp := (cubicThetaRegularizedFrequency_analytic hh s hs).continuousAt
  have he : cubicThetaRegularizedFrequency (-h)=ᶠ[𝓝[≠] s] cubicThetaRegularizedFrequency h := by
    filter_upwards [cubicThetaRegularizedFrequency_germ (neg_ne_zero.mpr hh) hs,
      cubicThetaRegularizedFrequency_germ hh hs,cubicThetaFrequencyContinuation_neg_germ hh hs]
      with z hz₁ hz₂ hz₃
    rw [hz₁,hz₂,hz₃]
  exact tendsto_nhds_unique ((hn.tendsto.mono_left nhdsWithin_le_nhds).congr' he)
    (hp.tendsto.mono_left nhdsWithin_le_nhds)

end CubicFirstMoment

end

end OAI
