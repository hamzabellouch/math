import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFrequencyContinuation
import Mathlib.Analysis.Meromorphic.Order

namespace OAI

/-! Identity propagation for the actual meromorphic coefficient observations. -/
noncomputable section
open Set Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaMeromorphic_identity {f g : ℂ → ℂ} {U : Set ℂ} {z₀ z : ℂ}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) (hU : IsPreconnected U)
    (h₀ : z₀∈U) (hz : z∈U) (he : f =ᶠ[𝓝[≠] z₀] g) :
    f =ᶠ[𝓝[≠] z] g := by
  have hd : MeromorphicOn (f-g) U := hf.sub hg
  have hzero : (f-g) =ᶠ[𝓝[≠] z₀] 0 := by
    filter_upwards [he] with x hx
    exact sub_eq_zero.mpr hx
  have htop := meromorphicOrderAt_eq_top_iff.mpr hzero
  have hzTop := hd.meromorphicOrderAt_eq_top_of_isPreconnected hU h₀ hz htop
  have hez := meromorphicOrderAt_eq_top_iff.mp hzTop
  filter_upwards [hez] with x hx
  exact sub_eq_zero.mp hx

theorem cubicThetaCuspFourierObservable_continued {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {s : ℂ} (hs : 1<s.re) :
    cubicThetaCuspFourierObservable h W =ᶠ[𝓝[≠] s]
      (fun z => ((Real.pi:ℂ)/Complex.Gamma z)*cubicThetaFrequencyContinuation h z*
        cubicThetaFourierRadialTest h W z) := by
  have hobs : MeromorphicOn (cubicThetaCuspFourierObservable h W) {z : ℂ | 1<z.re} :=
    fun z hz => cubicThetaCuspFourierObservable_meromorphic h W hz
  have hrhs : MeromorphicOn (fun z =>
      ((Real.pi:ℂ)/Complex.Gamma z)*cubicThetaFrequencyContinuation h z*
        cubicThetaFourierRadialTest h W z) {z : ℂ | 1<z.re} := by
    intro z hz
    change 1<z.re at hz
    exact (((MeromorphicAt.const (Real.pi:ℂ) z).div
      (cubicThetaGamma_analytic_right (by linarith)).meromorphicAt).mul
        (cubicThetaFrequencyContinuation_meromorphic hh hz)).mul
          ((cubicThetaFourierRadialTest_entire hh W).analyticAt z).meromorphicAt
  apply cubicThetaMeromorphic_identity hobs hrhs (convex_halfSpace_re_gt 1).isPreconnected
    (z₀:=(4:ℂ)) (by norm_num) hs
  have hn : ∀ᶠ z in 𝓝 (4:ℂ), 3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hn] with z hz
  rw [cubicThetaFrequencyContinuation_right h hz]
  exact cubicThetaCuspFourierObservable_normalized hh W hz

end CubicFirstMoment

end

end OAI
