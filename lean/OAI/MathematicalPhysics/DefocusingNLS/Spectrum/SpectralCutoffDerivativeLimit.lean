import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCutoffWeights
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialCollarMultiplier

namespace OAI

/-! The derivative-error coordinate of a shrinking smooth cutoff tends to zero. -/

open Set MeasureTheory Filter Topology
namespace DefocusingNLS

noncomputable def spectralRadialCutoffError (R l ε : ℝ) (hε : 0 < ε)
    (u : SpectralRadialEnergy R) : SpectralRadialL2 R :=
  let d := spectralCollarDerivativeWeight R l ε hε
  spectralL2ComplexMultiplier (radialPressureMeasure R) d.density d.radial_measurable
    d.bound d.radial_bound (spectralRadialValue R u)

theorem spectralRadialCutoffError_bound (R l ε : ℝ) (hR : 0 < R) (hl : 0 < l)
    (hε : 0 < ε) (hU : l+2*ε ≤ R) (u : SpectralRadialEnergy R)
    (hu : spectralRadialPointValue R hR l hl u=0) :
    ‖spectralRadialCutoffError R l ε hε u‖^2 ≤
      (4*spectralTransitionBound^2*R^11*(l^11)⁻¹)*
        ‖spectralRadialIntervalMask R l (l+2*ε) (spectralRadialDerivative R u)‖^2 := by
  let d := spectralCollarDerivativeWeight R l ε hε
  have h := spectralRadialCollarMultiplier_bound R l (l+2*ε) hR hl (by linarith) hU
    d.density d.radial_measurable d.bound d.radial_bound
    (spectralCollarCutoffDerivative_zero l ε · hε) u hu
  have heq : (spectralTransitionBound/ε)^2*(l+2*ε-l)^2=4*spectralTransitionBound^2 := by
    have he : l+2*ε-l=2*ε := by ring
    rw [he,← mul_pow]
    have hr : spectralTransitionBound/ε*(2*ε)=2*spectralTransitionBound := by
      field_simp [hε.ne']
    rw [hr]
    ring
  change _ ≤ (spectralTransitionBound/ε)^2*(l+2*ε-l)^2*R^11*(l^11)⁻¹*_ at h
  rw [heq] at h
  exact h

theorem spectralRadialCutoffError_tendsto_zero (R l : ℝ) (hR : 0 < R) (hl : 0 < l)
    (ε : ℕ → ℝ) (he : ∀ n, 0 < ε n) (hU : ∀ n, l+2*ε n ≤ R)
    (hε : Tendsto ε atTop (𝓝 0)) (u : SpectralRadialEnergy R)
    (hu : spectralRadialPointValue R hR l hl u=0) :
    Tendsto (fun n => spectralRadialCutoffError R l (ε n) (he n) u) atTop (𝓝 0) := by
  have hUp : Tendsto (fun n => l+2*ε n) atTop (𝓝 l) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hε)
  have hE := spectralRadialIntervalMask_tendsto_zero R l _ hUp (spectralRadialDerivative R u)
  have hs : Tendsto (fun n => ‖spectralRadialCutoffError R l (ε n) (he n) u‖^2)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _)
      (fun n => spectralRadialCutoffError_bound R l (ε n) hR hl (he n) (hU n) u hu)
    simpa using (tendsto_const_nhds.mul (hE.norm.pow 2))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hh

end DefocusingNLS

end OAI
