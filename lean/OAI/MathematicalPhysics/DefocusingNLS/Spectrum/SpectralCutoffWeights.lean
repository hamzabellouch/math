import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCutoffProfile

namespace OAI

/-! The explicit collar cutoffs as bounded coefficients of the harmonic form. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS

noncomputable def spectralTransitionBound : ℝ := Classical.choose spectralTransition_deriv_bound

theorem spectralTransitionBound_nonneg : 0 ≤ spectralTransitionBound :=
  (Classical.choose_spec spectralTransition_deriv_bound).1

theorem spectralTransitionBound_deriv (r : ℝ) :
    ‖deriv Real.smoothTransition r‖ ≤ spectralTransitionBound :=
  (Classical.choose_spec spectralTransition_deriv_bound).2 r

theorem spectralCollarCutoffDerivative_continuous (l ε : ℝ) :
    Continuous (spectralCollarCutoffDerivative l ε) := by
  have hs : ContDiff ℝ 1 Real.smoothTransition := Real.smoothTransition.contDiff
  have hd := hs.continuous_deriv_one
  exact (hd.comp ((continuous_id.sub continuous_const).sub continuous_const |>.div_const ε)).div_const ε

theorem spectralCollarCutoffDerivative_zero (l ε r : ℝ) (hε : 0 < ε)
    (hr : r ∉ Icc l (l+2*ε)) : spectralCollarCutoffDerivative l ε r=0 := by
  have hx : (r-l-ε)/ε ∉ Icc (0 : ℝ) 1 := by
    intro hx
    have h1 := (le_div_iff₀ hε).mp hx.1
    have h2 := (div_le_iff₀ hε).mp hx.2
    exact hr ⟨by linarith,by linarith⟩
  have h := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) (spectralTransition_fderiv_zero _ hx)
  have hd : deriv Real.smoothTransition ((r-l-ε)/ε)=0 := by
    simpa only [fderiv_eq_smul_deriv,one_smul,zero_apply] using h
  simp only [spectralCollarCutoffDerivative,hd,zero_div]

noncomputable def spectralCollarWeight (R l ε : ℝ) : SpectralHarmonicWeight R :=
  spectralContinuousWeight R (spectralCollarCutoff l ε)
    (spectralCollarCutoff_temperate l ε).1.continuous 1 (fun r _ => by
      rw [Real.norm_eq_abs,abs_of_nonneg (spectralCollarCutoff_bounds l ε r).1]
      exact (spectralCollarCutoff_bounds l ε r).2)

noncomputable def spectralCollarDerivativeWeight (R l ε : ℝ) (hε : 0 < ε) :
    SpectralHarmonicWeight R :=
  spectralContinuousWeight R (spectralCollarCutoffDerivative l ε)
    (spectralCollarCutoffDerivative_continuous l ε) (spectralTransitionBound/ε)
    (fun r _ => spectralCollarCutoffDerivative_bound spectralTransitionBound
      spectralTransitionBound_deriv l ε r hε)

theorem spectralCollarCutoff_tendsto_one (l r : ℝ) (hr : l < r) (ε : ℕ → ℝ)
    (he : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => spectralCollarCutoff l (ε n) r) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [hε.eventually (Iio_mem_nhds (show (0 : ℝ) < (r-l)/2 by linarith))] with n hn
  exact (spectralCollarCutoff_one l (ε n) r (he n) (by linarith)).symm

end DefocusingNLS

end OAI
