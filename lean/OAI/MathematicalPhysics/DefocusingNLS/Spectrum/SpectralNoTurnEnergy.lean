import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOscillatoryEnergyBound
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralForcedGronwall
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnGeometry

namespace OAI

/-! Oscillatory energy propagation for the actual no-turn frequency. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralNoTurn_energy_propagation
    (beta eta omega gamma C R a b : ℝ)
    (hbeta : 0 ≤ beta) (heta : 0 ≤ eta) (hw : 2 ≤ omega) (hgamma : |gamma| ≤ 8)
    (hC : 0 ≤ C) (hR : 0 < R) (hRa : R ≤ a) (hab : a ≤ b)
    (hL : eta+99/4 ≤ C*omega) (hCR : 2*C ≤ R^2)
    (q : ℝ → ℂ × ℂ) (forcing : ℝ → ℂ)
    (hq : ContinuousOn q (Icc a b)) (hf : ContinuousOn forcing (Icc a b))
    (hD : ∀ r ∈ Icc a b, HasDerivAt q (spectralScalarField
      ((homogeneousSpectralLocalizationFrequency (-1) beta eta omega r : ℂ)+
        Complex.I*(gamma : ℂ)) (q r)+(0,forcing r)) r) :
    ∀ r ∈ Icc a b,
      spectralOscillatoryEnergy (homogeneousSpectralLocalizationFrequency (-1) beta eta omega r) (q r) ≤
      (spectralOscillatoryEnergy (homogeneousSpectralLocalizationFrequency (-1) beta eta omega a) (q a)+
        ∫ t in a..b, ‖forcing t‖^2)*Real.exp ((2/R+4*C/R^3+17)*(r-a)) := by
  let F := homogeneousSpectralLocalizationFrequency (-1) beta eta omega
  let K := 2/R+4*C/R^3
  let y := fun r => spectralOscillatoryEnergy (F r) (q r)
  let dy := fun r => spectralLiouvilleSlope eta r*Complex.normSq (q r).1-
    2*gamma*spectralScalarFlux (q r)+2*(star (q r).2*forcing r).re
  have hFp : ∀ r ∈ Icc a b, 0 < r := fun r hr => hR.trans_le (hRa.trans hr.1)
  have hcF : ContinuousOn F (Icc a b) := fun r hr =>
    (homogeneousSpectralLocalizationFrequency_hasDerivAt (-1) beta eta omega r (hFp r hr)).continuousAt.continuousWithinAt
  have hcFp : ContinuousOn (spectralLiouvilleSlope eta) (Icc a b) := fun r hr =>
    (spectralLiouvilleSlope_hasDerivAt eta r (hFp r hr)).continuousAt.continuousWithinAt
  have hc1 := Complex.continuous_normSq.comp_continuousOn hq.fst
  have hc2 := Complex.continuous_normSq.comp_continuousOn hq.snd
  have hflux : ContinuousOn (fun r => spectralScalarFlux (q r)) (Icc a b) :=
    Complex.continuous_im.comp_continuousOn (hq.fst.star.mul hq.snd)
  have hcy : ContinuousOn y (Icc a b) := hc2.add (hcF.mul hc1)
  have hcdy : ContinuousOn dy (Icc a b) :=
    ((hcFp.mul hc1).sub (hflux.const_mul (2*gamma))).add
      ((Complex.continuous_re.comp_continuousOn (hq.snd.star.mul hf)).const_mul 2)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hyD : ∀ r ∈ Ioo a b, HasDerivAt y (dy r) r := by
    intro r hr
    exact spectralOscillatoryEnergy_hasDerivAt q F _ gamma (forcing r) r
      (homogeneousSpectralLocalizationFrequency_hasDerivAt (-1) beta eta omega r
        (hFp r ⟨hr.1.le,hr.2.le⟩)) (hD r ⟨hr.1.le,hr.2.le⟩)
  have hbnd : ∀ r ∈ Icc a b, dy r ≤ (K+17)*y r+‖forcing r‖^2 := by
    intro r hr
    have hRr := hRa.trans hr.1
    have hFlo := spectralNoTurn_frequency_lower beta eta omega C R r hbeta
      (by linarith) hR hRr hL hCR
    have hslope := spectralNoTurn_slope_bound beta eta omega C R r hbeta heta
      (by linarith) hC hR hRr hL hCR
    have h := spectralOscillatoryEnergy_deriv_bound (F r) (spectralLiouvilleSlope eta r)
      gamma K 8 (q r) (forcing r) (by dsimp only [F]; nlinarith [sq_nonneg r]) hK hslope hgamma
    convert h using 1
    dsimp only [y]
    ring
  exact spectral_forced_gronwall a b (K+17) hab (by linarith) y dy (fun r => ‖forcing r‖^2)
    hcy hcdy (hf.norm.pow 2) (fun _ _ => sq_nonneg _) hyD hbnd

end DefocusingNLS

end OAI
