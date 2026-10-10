import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialDilationPairingLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialDilationBoundaryLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialDilationBulkBound
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexEnergy

namespace OAI

/-! Along the actual escaping-frequency family, the shifted dilation identity
forces the complete radial-plus-angular gradient energy to vanish. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_dilation_energy_limit (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall) (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0)
    (R M A : ℝ) (hR : innerBoundaryRadius < R) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (lam : ℕ → ℂ) (eta : ℕ → ℝ) (he : ∀ i, 0 ≤ eta i)
    (hl : ∀ i, -(1/32 : ℝ) ≤ (lam i).re) (hu : ∀ i, (lam i).re ≤ 4)
    (hw : Tendsto (fun i => (lam i).im) atTop atTop)
    (hang : ∀ᶠ i in atTop, eta i ≤ A*(lam i).im)
    (f g : ℕ → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i)) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (hEq : ∀ i, IsRadialLogGaugeEigenpair (s i+radialInnerShootingThreshold)
      (radialMatchedEvenProfile (s i) (z i)) (eta i : ℂ) (lam i) (f i) (g i))
    (hfull : ∀ᶠ i in atTop, (∫ r in (0 : ℝ)..R, radialMatchedMassFunction (s i) (z i) r*
      spectralRadialEnergyDensity (eta i) (f i) (g i) r) ≤ M)
    (hfirst : Tendsto (fun i => ∫ r in (0 : ℝ)..R,
      r^11*radialMatchedMassFunction (s i) (z i) r*‖f i r‖^2) atTop (𝓝 0))
    (hboundary : Tendsto (fun i => radialMassDensity (s i) (z i) R*
      spectralWeightedCauchyEnergy (lam i).im (f i) (g i) R) atTop (𝓝 0)) :
    Tendsto (fun i => radialComplexAngularForm (s i) (z i) (eta i) R (fun _ => 0) (f i)+
      radialComplexAngularForm (s i) (z i) (eta i) R (fun _ => 0) (g i)) atTop (𝓝 0) := by
  have hR0 : 0 < R := by linarith [innerBoundaryRadius_bounds.1]
  let I := fun i => radialComplexDilationPairing (s i) (z i) R
    ((6-2*radialShootingA (s i))/2) (f i) (g i)
  obtain ⟨hIr,hIi⟩ := radialMatched_dilation_pairing_limit s hs z z₀ hz hX hm R M hR0.le hM
    (fun i => (lam i).im) eta hw he f g hf hg hfull hfirst hboundary
  obtain ⟨hBf,hBg⟩ := radialMatched_dilation_boundary_limit s hs z z₀ hz hX hm R A hR hA
    (fun i => (lam i).im) eta hw he hang f g
    (fun i => (hf i).of_le (by norm_num)) (fun i => (hg i).of_le (by norm_num)) hboundary
  have hcoef : ∀ i, |(lam i).re-(6-2*radialShootingA (s i))/2| ≤ 8 := by
    intro i
    have ha := radialShootingA_bounds (s i) (profileMatchingParameter (z i))
    apply abs_le.mpr
    constructor <;> linarith [hl i,hu i]
  have hreal : Tendsto (fun i => ((lam i).re-(6-2*radialShootingA (s i))/2)*(I i).re) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa only [Real.norm_eq_abs,norm_zero,mul_zero] using hIr.norm.const_mul 8)
    exact Eventually.of_forall (fun i => by
      simp only [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_right (hcoef i) (abs_nonneg _))
  have hcross : Tendsto (fun i => ((lam i-(((6-2*radialShootingA (s i))/2 : ℝ) : ℂ))*I i).re)
      atTop (𝓝 0) := by
    have ht := hreal.sub hIi
    simpa only [Complex.mul_re,Complex.sub_re,Complex.ofReal_re,Complex.sub_im,Complex.ofReal_im,
      sub_zero] using ht
  let H := fun i => ((lam i-(((6-2*radialShootingA (s i))/2 : ℝ) : ℂ))*I i).re-
    radialComplexAngularBoundary (s i) (z i) (eta i) R ((6-2*radialShootingA (s i))/2)
      (radialSpectralPressure (s i) (z i)) (f i)-
    radialComplexAngularBoundary (s i) (z i) (eta i) R ((6-2*radialShootingA (s i))/2)
      (fun _ => 0) (g i)+800*(∫ r in (0 : ℝ)..R,
        r^11*radialMatchedMassFunction (s i) (z i) r*‖f i r‖^2)
  have hH : Tendsto H atTop (𝓝 0) := by
    simpa only [sub_zero,add_zero,mul_zero] using ((hcross.sub hBf).sub hBg).add (hfirst.const_mul 800)
  obtain ⟨k,hk,hbulk⟩ := radialMatched_dilation_bulk_bound
  apply squeeze_zero' (Eventually.of_forall (fun i => add_nonneg
    (radialComplexAngularForm_zero_nonneg (s i) (z i) (eta i) R (he i) hR0.le (f i))
    (radialComplexAngularForm_zero_nonneg (s i) (z i) (eta i) R (he i) hR0.le (g i)))) _
    (by simpa only [zero_div] using hH.div_const k)
  filter_upwards [hs.tendsto_atTop.eventually hbulk] with i hi
  apply (le_div_iff₀ hk).mpr
  have hb := hi (z i) (hX i) (hm i) (eta i) R (he i) hR0.le (lam i) (f i) (g i) (hf i) (hg i) (hEq i)
  simpa only [H,I,radialMassDensity,radialMatchedMassFunction,mul_comm] using hb

end DefocusingNLS

end OAI
