import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveRadialMellin
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFrequencyResidue

namespace OAI

/-! Exact arithmetic normalization of the residue against every positive
compact Fourier test. The full low-height incoming correction is entire. -/
noncomputable section
open Set Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaPositiveFourierObservable_continued {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0)
    {s : ℂ} (hs : 1<s.re) :
    cubicThetaPositiveFourierObservable h W hε hW =ᶠ[𝓝[≠] s]
      (fun z => ((Real.pi:ℂ)/Complex.Gamma z)*cubicThetaFrequencyContinuation h z*
        cubicThetaPositiveRadialTest h W ε z) := by
  have hobs : MeromorphicOn (cubicThetaPositiveFourierObservable h W hε hW)
      {z : ℂ | 1<z.re} := fun z hz => cubicThetaPositiveFourierObservable_meromorphic h W hε hW hz
  have hrhs : MeromorphicOn (fun z =>
      ((Real.pi:ℂ)/Complex.Gamma z)*cubicThetaFrequencyContinuation h z*
        cubicThetaPositiveRadialTest h W ε z) {z : ℂ | 1<z.re} := by
    intro z hz
    change 1<z.re at hz
    exact (((MeromorphicAt.const (Real.pi:ℂ) z).div
      (cubicThetaGamma_analytic_right (by linarith)).meromorphicAt).mul
        (cubicThetaFrequencyContinuation_meromorphic hh hz)).mul
          ((cubicThetaPositiveRadialTest_entire hh W hε).analyticAt z).meromorphicAt
  apply cubicThetaMeromorphic_identity hobs hrhs (convex_halfSpace_re_gt 1).isPreconnected
    (z₀:=(4:ℂ)) (by norm_num) hs
  have hn : ∀ᶠ z in 𝓝 (4:ℂ),3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hn] with z hz
  rw [cubicThetaFrequencyContinuation_right h hz]
  exact cubicThetaPositiveFourierObservable_normalized hh W hε hW hz

theorem cubicThetaPositiveResidue_fourier_observation {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    inner ℂ (cubicThetaPositiveFourierProfileL2 h W hε hW)
        (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3)))=
      ((Real.pi:ℂ)/Complex.Gamma (4/3))*cubicThetaArithmeticFourierResidue h (4/3)*
        cubicThetaPositiveRadialTest h W ε (4/3) := by
  have hG : ContinuousAt (fun s : ℂ => (Real.pi:ℂ)/Complex.Gamma s) (4/3:ℂ) :=
    continuousAt_const.div (cubicThetaGamma_analytic_right (by norm_num)).continuousAt
      (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  have hR := (cubicThetaPositiveRadialTest_entire hh W hε).continuous.continuousAt (x:=(4/3:ℂ))
  have hF := cubicThetaFrequencyContinuation_residue hh (σ:=(4/3:ℝ))
    (by norm_num) (by norm_num)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hF
  have ht := ((hG.tendsto.mono_left nhdsWithin_le_nhds).mul hF).mul
    (hR.tendsto.mono_left nhdsWithin_le_nhds)
  apply tendsto_nhds_unique (cubicThetaPositiveFourierObservable_residue h W hε hW)
  apply ht.congr'
  filter_upwards [cubicThetaPositiveFourierObservable_continued hh W hε hW
    (s:=(4/3:ℂ)) (by norm_num)] with s hs
  rw [hs]
  ring

end CubicFirstMoment

end

end OAI
