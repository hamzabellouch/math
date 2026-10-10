import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMeromorphicIdentity
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialRealPositive

namespace OAI

/-! The arithmetic coefficient residue is a genuine Fourier observation
of the finite-rank spectral residue. No theta coefficient is assumed. -/
noncomputable section
open Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaArithmeticFourierResidue (h : Eisenstein) (σ : ℝ) : ℂ :=
  Complex.Gamma (σ:ℂ)/
    ((Real.pi:ℂ)*cubicThetaFourierRadialTest h cubicThetaRadialTestWeight σ)*
      inner ℂ (cubicThetaCuspFourierTest h cubicThetaRadialTestWeight)
        (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy σ))

theorem cubicThetaFrequencyContinuation_residue {h : Eisenstein} (hh : h≠0)
    {σ : ℝ} (hσ : 1<σ) (hσ2 : σ<2) :
    Tendsto (fun s : ℂ => (s-(σ:ℂ))*cubicThetaFrequencyContinuation h s)
      (𝓝[≠] (σ:ℂ)) (𝓝 (cubicThetaArithmeticFourierResidue h σ)) := by
  have hG : ContinuousAt Complex.Gamma (σ:ℂ) :=
    (cubicThetaGamma_analytic_right (by simpa using lt_trans zero_lt_one hσ)).continuousAt
  have hR := (cubicThetaFourierRadialTest_entire hh cubicThetaRadialTestWeight).continuous.continuousAt
    (x:=(σ:ℂ))
  have hRn : cubicThetaFourierRadialTest h cubicThetaRadialTestWeight (σ:ℂ)≠0 := by
    intro hz
    have hp := cubicThetaFourierRadialTest_real_pos hh σ
    rw [hz,Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  have hπ : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  have hfactor : ContinuousAt (fun s : ℂ => Complex.Gamma s/
      ((Real.pi:ℂ)*cubicThetaFourierRadialTest h cubicThetaRadialTestWeight s)) (σ:ℂ) :=
    hG.div (continuousAt_const.mul hR) (mul_ne_zero hπ hRn)
  have ht := (hfactor.tendsto.mono_left nhdsWithin_le_nhds).mul
    (cubicThetaCuspObservable_residue (cubicThetaCuspFourierTest h cubicThetaRadialTestWeight) hσ hσ2)
  apply ht.congr'
  have hn : ∀ᶠ s in 𝓝 (σ:ℂ), s.re<3 :=
    (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by simp; linarith)
  filter_upwards [nhdsWithin_le_nhds hn] with s hs
  simp only [cubicThetaFrequencyContinuation,ite_eq_right (not_lt.mpr hs.le),
    cubicThetaFrequencyQuotient,cubicThetaCuspFourierObservable]
  ring

theorem cubicThetaResidue_fourier_observation {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {σ : ℝ} (hσ : 1<σ) (hσ2 : σ<2) :
    inner ℂ (cubicThetaCuspFourierTest h W)
        (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy σ))=
      ((Real.pi:ℂ)/Complex.Gamma (σ:ℂ))*cubicThetaArithmeticFourierResidue h σ*
        cubicThetaFourierRadialTest h W σ := by
  have hG : ContinuousAt (fun s : ℂ => (Real.pi:ℂ)/Complex.Gamma s) (σ:ℂ) :=
    continuousAt_const.div
      (cubicThetaGamma_analytic_right (by simpa using lt_trans zero_lt_one hσ)).continuousAt
      (Complex.Gamma_ne_zero_of_re_pos (by simpa using lt_trans zero_lt_one hσ))
  have hW := (cubicThetaFourierRadialTest_entire hh W).continuous.continuousAt (x:=(σ:ℂ))
  have ht := ((hG.tendsto.mono_left nhdsWithin_le_nhds).mul
    (cubicThetaFrequencyContinuation_residue hh hσ hσ2)).mul
      (hW.tendsto.mono_left nhdsWithin_le_nhds)
  have ho := cubicThetaCuspObservable_residue (cubicThetaCuspFourierTest h W) hσ hσ2
  apply tendsto_nhds_unique ho
  apply ht.congr'
  filter_upwards [cubicThetaCuspFourierObservable_continued hh W (by simpa using hσ)] with s hs
  change cubicThetaCuspObservable (cubicThetaCuspFourierTest h W) s=_ at hs
  rw [hs]
  ring

end CubicFirstMoment

end

end OAI
