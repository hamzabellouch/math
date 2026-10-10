import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularPhysicalBasis
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-! # Twice differentiable regular Volterra primitives at the origin -/

open Set Filter MeasureTheory Topology
open scoped ContDiff
namespace DefocusingNLS

theorem homogeneousRegularSlope_hasDerivAt (d : ℕ) (h : ℝ) (f : ℝ → ℂ)
    (hf : Continuous f) (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => (s : ℂ)*spectralRegularAverage d h f s)
      (f r-((d : ℂ)/(r : ℂ)+Complex.I*(h*r/2 : ℝ))*
        ((r : ℂ)*spectralRegularAverage d h f r)) r := by
  let F : ℝ → ℂ := fun s => spectralRegularDensity d h s*f s
  let J : ℝ → ℂ := fun s => ∫ t in (0 : ℝ)..s, F t
  have hF : Continuous F := by unfold F spectralRegularDensity; fun_prop
  have hJ : HasDerivAt J (F r) r :=
    intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable 0 r)
      hF.stronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt
  have he (s : ℝ) (hs : s ≠ 0) :
      J s/spectralRegularDensity d h s=(s : ℂ)*spectralRegularAverage d h f s := by
    apply (div_eq_iff (spectralRegularDensity_ne_zero d h s hs)).mpr
    have hi := spectralRegularAverage_scaling d h s f
    change _=∫ t in (0 : ℝ)..s, F t at hi
    change _=J s at hi
    rw [← hi]
    unfold spectralRegularDensity
    rw [pow_succ]
    ring
  have hevent : (fun s => J s/spectralRegularDensity d h s) =ᶠ[nhds r]
      (fun s : ℝ => (s : ℂ)*spectralRegularAverage d h f s) := by
    filter_upwards [eventually_ne_nhds hr] with s hs
    exact he s hs
  have hd := (hJ.div (spectralRegularDensity_hasDerivAt d h r hr)
    (spectralRegularDensity_ne_zero d h r hr)).congr_of_eventuallyEq hevent.symm
  apply hd.congr_deriv
  change (spectralRegularDensity d h r*f r*spectralRegularDensity d h r-
      J r*(spectralRegularDensity d h r*
        ((d : ℂ)/(r : ℂ)+Complex.I*(h*r/2 : ℝ))))/(spectralRegularDensity d h r)^2=_
  rw [← he r hr]
  field_simp [spectralRegularDensity_ne_zero d h r hr]

theorem homogeneousRegularAverage_zero (d : ℕ) (h : ℝ) (f : ℝ → ℂ) :
    spectralRegularAverage d h f 0 = f 0 / (d + 1 : ℂ) := by
  simp only [spectralRegularAverage, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, zero_mul, zero_div, Complex.ofReal_zero, Complex.exp_zero, mul_one]
  rw [intervalIntegral.integral_mul_const]
  have hi : (∫ t in (0 : ℝ)..1, (t : ℂ)^d) = 1 / (d + 1 : ℂ) := by
    simp_rw [← Complex.ofReal_pow]
    rw [intervalIntegral.integral_ofReal]
    simp only [integral_pow, one_pow, zero_pow (Nat.succ_ne_zero d), sub_zero]
    push_cast
    rfl
  rw [hi]
  ring

theorem homogeneousRegular_mul_at_zero (A : ℝ → ℂ) (hA : ContinuousAt A 0) :
    HasDerivAt (fun r : ℝ => (r : ℂ) * A r) (A 0) 0 := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  apply (hA.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  simp only [zero_add, Complex.ofReal_zero, zero_mul, sub_zero, Complex.real_smul,
    Complex.ofReal_inv]
  have hn : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem homogeneousRegularPrimitive_contDiff_two (d : ℕ) (h : ℝ) (f : ℝ → ℂ)
    (hf : Continuous f) : ContDiff ℝ 2 (spectralRegularPrimitive d h f) := by
  let A := spectralRegularAverage d h f
  let S := fun r : ℝ => (r : ℂ) * A r
  let D := fun r : ℝ => f r - ((d : ℂ) + Complex.I * (h * r ^ 2 / 2 : ℝ)) * A r
  have hA : Continuous A := spectralRegularAverage_continuous d h f hf
  have hD : Continuous D := by dsimp only [D]; fun_prop
  have hS (r : ℝ) : HasDerivAt S (D r) r := by
    by_cases hr : r = 0
    · subst r
      have he : D 0 = A 0 := by
        dsimp only [D, A]
        rw [homogeneousRegularAverage_zero]
        simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_div,
          Complex.ofReal_zero, mul_zero, add_zero]
        field_simp [show (d + 1 : ℂ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero d]
        ring
      rw [he]
      exact homogeneousRegular_mul_at_zero A hA.continuousAt
    · apply (homogeneousRegularSlope_hasDerivAt d h f hf r hr).congr_deriv
      dsimp only [S, D, A]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hr]
  have hSder : deriv S = D := funext (fun r => (hS r).deriv)
  have hSC : ContDiff ℝ 1 S := contDiff_one_iff_deriv.mpr
    ⟨fun r => (hS r).differentiableAt, by rw [hSder]; exact hD⟩
  have hp : deriv (spectralRegularPrimitive d h f) = S :=
    funext (fun r => (spectralRegularPrimitive_hasDerivAt d h f hf r).deriv)
  rw [show (2 : ℕ∞ω) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun r => (spectralRegularPrimitive_hasDerivAt d h f hf r).differentiableAt,
    by norm_num, ?_⟩
  rw [hp]
  exact hSC

theorem homogeneousRegularLift_contDiff_two (d : ℕ) (α : ℝ) (c : ℂ × ℂ)
    (s : RegularSpectralSpace) : ContDiff ℝ 2 (spectralRegularLift d α c s) := by
  exact (contDiff_const.add (homogeneousRegularPrimitive_contDiff_two d 1 _
    (spectralRegularWeightedSource_continuous α s.1))).prodMk
      (contDiff_const.add (homogeneousRegularPrimitive_contDiff_two d (-1) _
        (spectralRegularWeightedSource_continuous α s.2)))

theorem homogeneousRegularPhysical_contDiff_two (ell d : ℕ) (α : ℝ) (c : ℂ × ℂ)
    (s : RegularSpectralSpace) :
    ContDiff ℝ 2 (fun r => (spectralAngularPair ell (spectralRegularState d α c s) r).1.1) ∧
      ContDiff ℝ 2 (fun r => (spectralAngularPair ell (spectralRegularState d α c s) r).2.1) := by
  have hp : ContDiff ℝ 2 (fun r : ℝ => (r : ℂ)^ell) :=
    Complex.ofRealCLM.contDiff.pow ell
  have hL := homogeneousRegularLift_contDiff_two d α c s
  exact ⟨hp.mul hL.fst, hp.mul hL.snd⟩

end DefocusingNLS

end OAI
