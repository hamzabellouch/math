import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInvertedFourierObservable

namespace OAI

/-! The middle primary twist has the actual theta residue. This follows
from inversion of the global residue and actual Fourier observations. -/
noncomputable section
open Set Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaInvertedFourier_regularized_germ {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {s : ℂ} (hs : 1<s.re) :
    (fun z => (z-4/3)*cubicThetaInvertedFourierObservable h W z)=ᶠ[𝓝[≠] s]
      (fun z => ((Real.pi:ℂ)/Complex.Gamma z)*cubicThetaRegularizedPrimaryOne h z*
        cubicThetaFourierRadialTest h W z) := by
  have hL : MeromorphicOn (fun z => (z-4/3)*cubicThetaInvertedFourierObservable h W z)
      {z : ℂ | 1<z.re} := by
    intro z hz
    exact (analyticAt_id.sub analyticAt_const).meromorphicAt.mul
      (cubicThetaInvertedCuspObservable_meromorphic _ hz)
  have hR : MeromorphicOn (fun z => ((Real.pi:ℂ)/Complex.Gamma z)*
      cubicThetaRegularizedPrimaryOne h z*cubicThetaFourierRadialTest h W z)
      {z : ℂ | 1<z.re} := by
    intro z hz
    change 1<z.re at hz
    exact (((MeromorphicAt.const (Real.pi:ℂ) z).div
      (cubicThetaGamma_analytic_right (by linarith)).meromorphicAt).mul
      (cubicThetaRegularizedPrimaryOne_analytic hh z hz).meromorphicAt).mul
      ((cubicThetaFourierRadialTest_entire hh W).analyticAt z).meromorphicAt
  apply cubicThetaMeromorphic_identity hL hR (convex_halfSpace_re_gt 1).isPreconnected
    (z₀:=(4:ℂ)) (by norm_num) hs
  have hn : ∀ᶠ z in 𝓝 (4:ℂ), 3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hn] with z hz
  rw [cubicThetaInvertedFourierObservable_normalized hh W hz,
    cubicThetaRegularizedInvertedFrequency_right hh hz]
  ring

theorem cubicThetaInvertedFourier_residue {h : Eisenstein} (hh : h≠0) (W : C_c(ℝ,ℂ)) :
    inner ℂ (cubicThetaCuspFourierTest h W)
      (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy (4/3)))=
      ((Real.pi:ℂ)/Complex.Gamma (4/3))*cubicThetaRegularizedPrimaryOne h (4/3)*
        cubicThetaFourierRadialTest h W (4/3) := by
  have hc : ContinuousAt (fun z => ((Real.pi:ℂ)/Complex.Gamma z)*
      cubicThetaRegularizedPrimaryOne h z*cubicThetaFourierRadialTest h W z) (4/3:ℂ) :=
    ((continuousAt_const.div (cubicThetaGamma_analytic_right (by norm_num : (0:ℝ)<(4/3:ℂ).re)).continuousAt
      (Complex.Gamma_ne_zero_of_re_pos (by norm_num))).mul
      (cubicThetaRegularizedPrimaryOne_analytic hh (4/3) (by norm_num)).continuousAt).mul
      ((cubicThetaFourierRadialTest_entire hh W).analyticAt (4/3)).continuousAt
  have ht : Tendsto (fun z : ℂ => (z-4/3)*cubicThetaInvertedFourierObservable h W z)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (((Real.pi:ℂ)/Complex.Gamma (4/3))*
        cubicThetaRegularizedPrimaryOne h (4/3)*cubicThetaFourierRadialTest h W (4/3))) := by
    apply (hc.tendsto.mono_left nhdsWithin_le_nhds).congr'
    exact (cubicThetaInvertedFourier_regularized_germ hh W (s:=(4/3:ℂ)) (by norm_num)).symm
  exact tendsto_nhds_unique
    (cubicThetaInvertedCuspObservable_residue (cubicThetaCuspFourierTest h W)) ht

theorem cubicThetaRegularizedPrimaryOne_residue_eq {h : Eisenstein} (hh : h≠0) :
    cubicThetaRegularizedPrimaryOne h (4/3)=cubicThetaArithmeticFourierResidue h (4/3) := by
  have hI := cubicThetaInvertedFourier_residue hh cubicThetaRadialTestWeight
  have hR := cubicThetaResidue_fourier_observation hh cubicThetaRadialTestWeight
    (σ:=(4/3:ℝ)) (by norm_num) (by norm_num)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hR
  have hB : cubicThetaFourierRadialTest h cubicThetaRadialTestWeight (4/3:ℂ)≠0 := by
    intro hz
    have hp := cubicThetaFourierRadialTest_real_pos hh (4/3)
    norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hp
    rw [hz,Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  have hK : (Real.pi:ℂ)/Complex.Gamma (4/3)≠0 :=
    div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  exact mul_left_cancel₀ hK (mul_right_cancel₀ hB (hI.symm.trans hR))

theorem cubicThetaArithmeticFourierResidue_ramified_step {h : Eisenstein} (hh : h≠0) :
    3*cubicThetaArithmeticFourierResidue (lambdaE^3*h) (4/3)=
      (cubicThetaRamifiedTrace h+1)*cubicThetaArithmeticFourierResidue h (4/3) := by
  have he := cubicThetaRegularizedPrimaryOne_pole hh
  rw [cubicThetaRegularizedPrimaryOne_residue_eq hh] at he
  have ht := (eq_div_iff (cubicThetaRamifiedTrace_ne_zero h)).mp he
  linear_combination -ht

theorem cubicThetaArithmeticFourierResidue_ramified_primary_cube {h : Eisenstein} (hh : primary h) :
    cubicThetaArithmeticFourierResidue (lambdaE^3*h) (4/3)=
      cubicThetaArithmeticFourierResidue h (4/3) := by
  have he := cubicThetaArithmeticFourierResidue_ramified_step (primary_ne_zero hh)
  rw [cubicThetaRamifiedTrace_primary hh] at he
  linear_combination (1/3:ℂ)*he

end CubicFirstMoment

end

end OAI
