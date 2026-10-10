import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralC1SchwartzApprox
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSmoothHarmonicBound
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicRepresentative
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWeightedPairing
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralC1IntervalExtension
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Classical C1 radial data define actual vectors in the harmonic completion. -/

open Set Filter Topology MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralC1HarmonicJet (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) :
    ∃ u : SpectralHarmonicEnergy ell R,
      (∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u r=f r) ∧
      spectralHarmonicDerivative ell R u =ᵐ[radialPressureMeasure R] deriv f := by
  let e := fun n : ℕ => 1/((n : ℝ)+1)
  have he (n : ℕ) : 0 < e n := by dsimp only [e]; positivity
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hS (n : ℕ) := spectralC1SchwartzApprox f hf R (e n) hR.le (he n)
  choose S hS using hS
  obtain ⟨C,hC,hbound⟩ := spectralSmoothHarmonic_uniform_bound ell R
  let u := fun n => spectralHarmonicSmoothEmbedding ell R (S n)
  have hdiff (n m : ℕ) : ‖u n-u m‖ ≤ C*(R+1)*(e n+e m) := by
    have hsum : 0 ≤ e n+e m := add_nonneg (he n).le (he m).le
    have hv (r : ℝ) (hr : r ∈ Icc 0 R) : ‖(S n-S m) r‖ ≤ (R+1)*(e n+e m) := by
      change ‖S n r-S m r‖ ≤ _
      calc
        _ = ‖(S n r-f r)-(S m r-f r)‖ := by congr 1; abel
        _ ≤ ‖S n r-f r‖+‖S m r-f r‖ := norm_sub_le _ _
        _ ≤ e n*R+e m*R := add_le_add (hS n r hr).1 (hS m r hr).1
        _ ≤ (R+1)*(e n+e m) := by nlinarith
    have hd (r : ℝ) (hr : r ∈ Icc 0 R) :
        ‖deriv (S n-S m) r‖ ≤ (R+1)*(e n+e m) := by
      have hdsub : deriv (S n-S m) r=deriv (S n) r-deriv (S m) r :=
        ((S n).hasDerivAt r |>.sub ((S m).hasDerivAt r)).deriv
      rw [hdsub]
      calc
        _ = ‖(deriv (S n) r-deriv f r)-(deriv (S m) r-deriv f r)‖ := by congr 1; abel
        _ ≤ ‖deriv (S n) r-deriv f r‖+‖deriv (S m) r-deriv f r‖ := norm_sub_le _ _
        _ ≤ e n+e m := add_le_add (hS n r hr).2 (hS m r hr).2
        _ ≤ (R+1)*(e n+e m) := by nlinarith [mul_nonneg hR.le hsum]
    have hb := hbound (S n-S m) ((R+1)*(e n+e m)) (by positivity) hv hd
    simpa only [map_sub,mul_assoc] using hb
  have hc : CauchySeq u := by
    apply cauchySeq_of_le_tendsto_0' (fun n => 2*C*(R+1)*e n)
    · intro n m hnm
      have hem : e m ≤ e n := by
        apply one_div_le_one_div_of_le
        · positivity
        · exact_mod_cast Nat.add_le_add_right hnm 1
      rw [dist_eq_norm]
      exact (hdiff n m).trans (by nlinarith [mul_nonneg hC.le (by linarith : 0 ≤ R+1)])
    · simpa only [mul_zero] using he0.const_mul (2*C*(R+1))
  obtain ⟨v,hv⟩ := cauchySeq_tendsto_of_complete hc
  have hderiv : spectralHarmonicDerivative ell R v =ᵐ[radialPressureMeasure R] deriv f := by
    have hlim : Tendsto (fun n => spectralHarmonicDerivative ell R (u n)) atTop
        (𝓝 (spectralHarmonicDerivative ell R v)) :=
      (spectralHarmonicDerivative ell R).continuous.continuousAt.tendsto.comp hv
    obtain ⟨φ,hφ,hpoint⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
    have hsmooth : ∀ᵐ r ∂radialPressureMeasure R, ∀ n,
        spectralHarmonicDerivative ell R (u (φ n)) r=deriv (S (φ n)) r :=
      ae_all_iff.mpr (fun n => spectralHarmonicDerivative_smooth_ae ell R (S (φ n)))
    filter_upwards [hpoint,hsmooth,radialPressureMeasure_ae_positive R] with r hp hs hr
    have hz : Tendsto (fun n => deriv (S (φ n)) r-deriv f r) atTop (𝓝 0) := by
      apply squeeze_zero_norm (a := fun n => e (φ n))
      · intro n
        exact (hS (φ n) r ⟨hr.1.le,hr.2⟩).2
      · exact he0.comp hφ.tendsto_atTop
    have hd : Tendsto (fun n => deriv (S (φ n)) r) atTop (𝓝 (deriv f r)) := by
      simpa only [sub_add_cancel,zero_add] using hz.add_const (deriv f r)
    have hp' : Tendsto (fun n => deriv (S (φ n)) r) atTop
        (𝓝 (spectralHarmonicDerivative ell R v r)) := by
      simpa only [hs] using hp
    exact tendsto_nhds_unique hp' hd
  refine ⟨v,?_,hderiv⟩
  intro r hr
  have ht : Tendsto (fun n => S n r) atTop
      (𝓝 (spectralHarmonicRepresentative ell R hR v r)) := by
    have hp := ((spectralRadialPointValue R hR r hr.1).comp
      (spectralHarmonicRadialForget ell R)).continuous.continuousAt.tendsto.comp hv
    simpa only [u,Function.comp_def,ContinuousLinearMap.comp_apply,
      spectralHarmonicRadialForget_smooth,spectralRadialPointValue_smooth R hR r hr.1 hr.2,
      spectralHarmonicRepresentative,spectralRadialRepresentative,dite_eq_left hr.1] using hp
  have hz : Tendsto (fun n => S n r-f r) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n => e n*R)
    · intro n
      exact (hS n r ⟨hr.1.le,hr.2⟩).1
    · simpa only [zero_mul] using he0.mul_const R
  have hfval : Tendsto (fun n => S n r) atTop (𝓝 (f r)) := by
    simpa only [sub_add_cancel,zero_add] using hz.add_const (f r)
  exact tendsto_nhds_unique ht hfval

theorem spectralC1HarmonicMembership (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) :
    ∃ u : SpectralHarmonicEnergy ell R,
      ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u r=f r := by
  obtain ⟨u,hu,_⟩ := spectralC1HarmonicJet ell R hR f hf
  exact ⟨u,hu⟩

theorem spectralC1OnHarmonicMembership (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (f : ℝ → ℂ) (hf : ∀ r ∈ Icc 0 R, DifferentiableAt ℝ f r)
    (hd : ContinuousOn (deriv f) (Icc 0 R)) :
    ∃ u : SpectralHarmonicEnergy ell R,
      ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u r=f r := by
  obtain ⟨F,hF,he⟩ := spectralC1IntervalExtension f R hR.le hf hd
  obtain ⟨u,hu⟩ := spectralC1HarmonicMembership ell R hR F hF
  exact ⟨u,fun r hr => (hu r hr).trans (he ⟨hr.1.le,hr.2⟩)⟩

end DefocusingNLS

end OAI
