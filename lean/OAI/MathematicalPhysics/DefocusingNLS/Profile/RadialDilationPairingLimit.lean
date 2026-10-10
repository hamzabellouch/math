import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialDilationPairingVolume
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialDilationCrossBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWeightedProductLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeComponentEnergy

namespace OAI

/-! First-component L2 vanishing controls the real volume pairing; the
frequency-weighted imaginary part is entirely a vanishing boundary term. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_dilation_pairing_limit (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall) (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0)
    (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M) (omega eta : ℕ → ℝ)
    (hw : Tendsto omega atTop atTop) (he : ∀ i, 0 ≤ eta i)
    (f g : ℕ → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i)) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (hfull : ∀ᶠ i in atTop, (∫ r in (0 : ℝ)..R, radialMatchedMassFunction (s i) (z i) r*
      spectralRadialEnergyDensity (eta i) (f i) (g i) r) ≤ M)
    (hfirst : Tendsto (fun i => ∫ r in (0 : ℝ)..R,
      r^11*radialMatchedMassFunction (s i) (z i) r*‖f i r‖^2) atTop (𝓝 0))
    (hboundary : Tendsto (fun i => radialMassDensity (s i) (z i) R*
      spectralWeightedCauchyEnergy (omega i) (f i) (g i) R) atTop (𝓝 0)) :
    Tendsto (fun i => (radialComplexDilationPairing (s i) (z i) R
      ((6-2*radialShootingA (s i))/2) (f i) (g i)).re) atTop (𝓝 0) ∧
    Tendsto (fun i => omega i*(radialComplexDilationPairing (s i) (z i) R
      ((6-2*radialShootingA (s i))/2) (f i) (g i)).im) atTop (𝓝 0) := by
  let mu := fun i => radialMatchedMassFunction (s i) (z i)
  let A := fun i => radialMatchedTransportFunction (s i) (z i)
  have hmuc i : Continuous (mu i) := radialMatchedMassFunction_continuous (s i) (z i) (hX i) (hm i)
  have hAc i : Continuous (A i) := radialMatchedTransportFunction_continuous (s i) (z i) (hX i) (hm i)
  have hmu0 i r (_hr : r ∈ Icc 0 R) : 0 ≤ mu i r := sq_nonneg _
  have hcomponents : ∀ᶠ i in atTop,
      (∫ r in (0 : ℝ)..R, r^11*mu i r*‖g i r‖^2) ≤ M ∧
      (∫ r in (0 : ℝ)..R, r^11*mu i r*‖deriv (g i) r‖^2) ≤ M := by
    filter_upwards [hfull] with i hi
    have h := spectralGauge_second_component_energy_le (eta i) R (he i) hR (mu i)
      (hmuc i) (hmu0 i) (f i) (g i) (hf i) (hg i)
    exact ⟨h.1.trans hi,h.2.trans hi⟩
  obtain ⟨C,hC,hA⟩ := radialMatched_uniform_transport_bound s hs z z₀ hz hX hm R hR
  have hprodA := spectralWeightedProduct_tendsto_zero R C M hR hC hM mu A
    (fun i => deriv (g i)) f (fun i => (hmuc i).continuousOn) (fun i => (hAc i).continuousOn)
    (fun i => ((hg i).continuous_deriv (by norm_num)).continuousOn)
    (fun i => (hf i).continuous.continuousOn) hmu0
    (hA.mono (fun i hi r hr => (hi r hr).2)) (hcomponents.mono (fun _ h => h.2)) hfirst
  have hprodM := spectralWeightedProduct_tendsto_zero R 1 M hR (by norm_num) hM mu mu g f
    (fun i => (hmuc i).continuousOn) (fun i => (hmuc i).continuousOn)
    (fun i => (hg i).continuous.continuousOn) (fun i => (hf i).continuous.continuousOn) hmu0
    (Eventually.of_forall (fun i r hr => by rw [abs_of_nonneg (hmu0 i r hr),one_mul]))
    (hcomponents.mono (fun _ h => h.1)) hfirst
  have hP : Tendsto (fun i => ∫ r in (0 : ℝ)..R,
      (radialMassFlux (s i) (z i) r : ℂ)*star (deriv (g i) r)*f i r) atTop (𝓝 0) := by
    apply hprodA.congr
    intro i
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hR] at hr
    dsimp only [A]
    rw [radialMatched_mass_transport_eq (s i) (z i) (hX i) (hm i) r hr.1]
    push_cast
    ring
  have hQ : Tendsto (fun i => ∫ r in (0 : ℝ)..R,
      (radialMassDensity (s i) (z i) r : ℂ)*star (g i r)*f i r) atTop (𝓝 0) := by
    apply hprodM.congr
    intro i
    apply intervalIntegral.integral_congr
    intro r _
    dsimp only [mu,radialMassDensity,radialMatchedMassFunction]
    push_cast
    ring
  have hshift : Tendsto (fun i => (6-2*radialShootingA (s i))/2) atTop (𝓝 (3 : ℝ)) := by
    have hc : Tendsto (fun i => (6 : ℝ)-2*radialShootingA (s i)) atTop (𝓝 (6 : ℝ)) := by
      simpa only [Function.comp_def,mul_zero,sub_zero] using
        (tendsto_const_nhds (x := (6 : ℝ))).sub ((radialShootingA_tendsto_zero.comp hs.tendsto_atTop).const_mul 2)
    convert hc.div_const 2 using 1
    norm_num
  obtain ⟨hB,hBw⟩ := radialMatched_dilation_cross_boundary_limit s hs z z₀ hz hX hm R hR omega hw f g hboundary
  have hPr := (Complex.continuous_re.tendsto 0).comp hP
  have hQr := (Complex.continuous_re.tendsto 0).comp hQ
  have hBr := (Complex.continuous_re.tendsto 0).comp hB
  have hBwi := (Complex.continuous_im.tendsto 0).comp hBw
  constructor
  · have ht := ((hPr.add (hshift.mul hQr)).const_mul 2).sub hBr
    simp only [Complex.zero_re,mul_zero,add_zero,sub_zero] at ht
    apply ht.congr
    intro i
    exact (radialMatched_dilation_pairing_re (s i) (z i) (hX i) (hm i) R hR (f i) (g i)
      ((hf i).of_le (by norm_num)) ((hg i).of_le (by norm_num))).symm
  · have ht := hBwi.neg
    simp only [Complex.zero_im,neg_zero] at ht
    apply ht.congr
    intro i
    rw [radialMatched_dilation_pairing_boundary (s i) (z i) (hX i) (hm i) R hR (f i) (g i)
      ((hf i).of_le (by norm_num)) ((hg i).of_le (by norm_num))]
    simp only [Function.comp_def,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.sub_im,zero_mul,zero_sub,add_zero]
    ring

end DefocusingNLS

end OAI
