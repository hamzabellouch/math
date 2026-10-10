import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicMultiplier
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicCoordinates
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialCoreLocality
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCutoffDerivativeLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralL2CutoffLimit

namespace OAI

/-! Strong convergence of collar cutoffs in the full harmonic H¹ norm. -/

open Set MeasureTheory Filter Topology
namespace DefocusingNLS

noncomputable def spectralHarmonicCutoff (ell : ℕ) (R l ε : ℝ) (hε : 0 < ε) :
    SpectralHarmonicEnergy ell R →L[ℂ] SpectralHarmonicEnergy ell R :=
  spectralHarmonicMultiplier ell R (spectralCollarWeight R l ε)
    (spectralCollarDerivativeWeight R l ε hε) (spectralCollarCutoff_temperate l ε)
    (spectralCollarCutoff_hasDerivAt l ε)

theorem spectralHarmonicCutoff_value (ell : ℕ) (R l ε : ℝ) (hε : 0 < ε)
    (u : SpectralHarmonicEnergy ell R) :
    spectralHarmonicValue ell R (spectralHarmonicCutoff ell R l ε hε u)=
      spectralL2ComplexMultiplier (radialPressureMeasure R) (spectralCollarWeight R l ε).density
        (spectralCollarWeight R l ε).radial_measurable (spectralCollarWeight R l ε).bound
        (spectralCollarWeight R l ε).radial_bound (spectralHarmonicValue ell R u) := rfl

theorem spectralHarmonicCutoff_derivative (ell : ℕ) (R l ε : ℝ) (hε : 0 < ε)
    (u : SpectralHarmonicEnergy ell R) :
    spectralHarmonicDerivative ell R (spectralHarmonicCutoff ell R l ε hε u)=
      spectralRadialCutoffError R l ε hε (spectralHarmonicRadialForget ell R u)+
      spectralL2ComplexMultiplier (radialPressureMeasure R) (spectralCollarWeight R l ε).density
        (spectralCollarWeight R l ε).radial_measurable (spectralCollarWeight R l ε).bound
        (spectralCollarWeight R l ε).radial_bound (spectralHarmonicDerivative ell R u) := rfl

theorem spectralHarmonicCutoff_angular (ell : ℕ) (R l ε : ℝ) (hε : 0 < ε)
    (u : SpectralHarmonicEnergy ell R) :
    spectralHarmonicAngularValue ell R (spectralHarmonicCutoff ell R l ε hε u)=
      spectralL2ComplexMultiplier (spectralAngularMeasure R) (spectralCollarWeight R l ε).density
        (spectralCollarWeight R l ε).angular_measurable (spectralCollarWeight R l ε).bound
        (spectralCollarWeight R l ε).angular_bound (spectralHarmonicAngularValue ell R u) := rfl

theorem spectralHarmonicCutoff_tendsto (ell : ℕ) (R l : ℝ) (hR : 0 < R) (hl : 0 < l)
    (ε : ℕ → ℝ) (he : ∀ n, 0 < ε n) (hU : ∀ n, l+2*ε n ≤ R)
    (hε : Tendsto ε atTop (𝓝 0)) (u : SpectralHarmonicEnergy ell R)
    (hu : (fun r => spectralHarmonicValue ell R u r) =ᵐ[(radialPressureMeasure R).restrict (Iic l)] 0) :
    Tendsto (fun n => spectralHarmonicCutoff ell R l (ε n) (he n) u) atTop (𝓝 u) := by
  let v := fun n => spectralHarmonicCutoff ell R l (ε n) (he n) u
  let w := fun n => spectralCollarWeight R l (ε n)
  have hlR : l ≤ R := by linarith [hU 0,he 0]
  have hp : ∀ r, l < r → Tendsto (fun n => (w n).density r) atTop (𝓝 1) :=
    fun r hr => spectralCollarCutoff_tendsto_one l r hr ε he hε
  have hv : Tendsto (fun n => spectralHarmonicValue ell R (v n)) atTop
      (𝓝 (spectralHarmonicValue ell R u)) := by
    exact spectralL2_cutoff_tendsto (radialPressureMeasure R) l (fun n => (w n).density)
      (fun n => (w n).radial_measurable) (fun n => (w n).radial_bound) hp _ hu
  have hcoreD := spectralRadialCore_derivative_zero R l hR hlR
    (spectralHarmonicRadialForget ell R u) hu
  have hdq := spectralL2_cutoff_tendsto (radialPressureMeasure R) l (fun n => (w n).density)
    (fun n => (w n).radial_measurable) (fun n => (w n).radial_bound) hp
    (spectralHarmonicDerivative ell R u) hcoreD
  have herror := spectralRadialCutoffError_tendsto_zero R l hR hl ε he hU hε
    (spectralHarmonicRadialForget ell R u)
    (spectralRadialCore_point_zero R l hR hl hlR _ hu)
  have hd : Tendsto (fun n => spectralHarmonicDerivative ell R (v n)) atTop
      (𝓝 (spectralHarmonicDerivative ell R u)) := by
    simpa only [v,w,spectralHarmonicCutoff_derivative,spectralCollarWeight,
      spectralContinuousWeight,zero_add] using herror.add hdq
  have hg : Tendsto (fun n => spectralHarmonicAngularValue ell R (v n)) atTop
      (𝓝 (spectralHarmonicAngularValue ell R u)) := by
    exact spectralL2_cutoff_tendsto (spectralAngularMeasure R) l (fun n => (w n).density)
      (fun n => (w n).angular_measurable) (fun n => (w n).angular_bound) hp _
      (spectralHarmonicCore_angular_zero ell R l u hu)
  have hvs := (tendsto_iff_norm_sub_tendsto_zero.mp hv).pow 2
  have hds := (tendsto_iff_norm_sub_tendsto_zero.mp hd).pow 2
  have hgs := (tendsto_iff_norm_sub_tendsto_zero.mp hg).pow 2
  have hs : Tendsto (fun n => ‖v n-u‖^2) atTop (𝓝 0) := by
    have h := (hvs.add hds).add hgs
    simp only [zero_pow (by decide : (2 : ℕ) ≠ 0),add_zero] at h
    convert h using 1
    funext n
    rw [spectralHarmonicEnergy_norm_sq,spectralRadialEnergy_norm_sq]
    change ‖spectralHarmonicValue ell R (v n-u)‖^2+
      ‖spectralHarmonicDerivative ell R (v n-u)‖^2+
      ‖spectralHarmonicAngularValue ell R (v n-u)‖^2=_
    simp only [map_sub]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hh

end DefocusingNLS

end OAI
