import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularResolvent
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularEquation
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularAverageOperator

namespace OAI

/-! Recovering a regular radial solution and its initial jet from the weighted resolvent. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS

noncomputable def spectralRegularWeight (R α : ℝ) (hα : 0 ≤ α) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun r => (Real.exp (-α*(radialClamp R r)^2) : ℂ))
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul ((continuous_radialClamp R).pow 2)))) 1 (fun r => by
        rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα)
          (sq_nonneg _)))

noncomputable def spectralRegularInitial (R α : ℝ) (hα : 0 ≤ α) (c : ℂ × ℂ) :
    RegularSpectralSpace :=
  (c.1 • spectralRegularWeight R α hα,c.2 • spectralRegularWeight R α hα)

noncomputable def spectralRegularLift (d : ℕ) (α : ℝ) (c : ℂ × ℂ)
    (s : RegularSpectralSpace) (r : ℝ) : ℂ × ℂ :=
  (c.1+spectralRegularPrimitive d 1 (spectralRegularWeightedSource α s.1) r,
   c.2+spectralRegularPrimitive d (-1) (spectralRegularWeightedSource α s.2) r)

theorem spectralRegularLift_continuous (d : ℕ) (α : ℝ) (c : ℂ × ℂ)
    (s : RegularSpectralSpace) : Continuous (spectralRegularLift d α c s) := by
  exact (continuous_const.add (spectralRegularPrimitive_continuous d 1 _
    (spectralRegularWeightedSource_continuous α s.1))).prodMk
      (continuous_const.add (spectralRegularPrimitive_continuous d (-1) _
        (spectralRegularWeightedSource_continuous α s.2)))

theorem spectralRegularLift_hasDerivAt (d : ℕ) (α : ℝ) (c : ℂ × ℂ)
    (s : RegularSpectralSpace) (r : ℝ) :
    HasDerivAt (spectralRegularLift d α c s)
      ((r : ℂ)*spectralRegularAverage d 1 (spectralRegularWeightedSource α s.1) r,
       (r : ℂ)*spectralRegularAverage d (-1) (spectralRegularWeightedSource α s.2) r) r := by
  exact ((spectralRegularPrimitive_hasDerivAt d 1 _
    (spectralRegularWeightedSource_continuous α s.1) r).const_add c.1).prodMk
      ((spectralRegularPrimitive_hasDerivAt d (-1) _
        (spectralRegularWeightedSource_continuous α s.2) r).const_add c.2)

theorem spectralRegularLift_initial (d : ℕ) (α : ℝ) (c : ℂ × ℂ)
    (s : RegularSpectralSpace) :
    spectralRegularLift d α c s 0=c ∧ deriv (spectralRegularLift d α c s) 0=0 := by
  constructor
  · simp [spectralRegularLift,spectralRegularPrimitive]
  · rw [(spectralRegularLift_hasDerivAt d α c s 0).deriv]
    simp

theorem spectralRegularLift_weighted (d : ℕ) (R α : ℝ) (hR : 0 ≤ R) (hα : 0 < α)
    (c : ℂ × ℂ) (v s : RegularSpectralSpace)
    (hv : v=spectralRegularInitial R α hα.le c+spectralRegularPairKernel d R α hR hα s)
    (r : ℝ) (hr : r ∈ Icc 0 R) :
    (v.1 r,v.2 r)=(Real.exp (-α*r^2) : ℂ) • spectralRegularLift d α c s r := by
  have he := congrArg (fun u : RegularSpectralSpace => (u.1 r,u.2 r)) hv
  change (v.1 r,v.2 r)=
    (c.1*(Real.exp (-α*(radialClamp R r)^2) : ℂ)+
       (Real.exp (-α*(radialClamp R r)^2) : ℂ)*
         spectralRegularPrimitive d 1 (spectralRegularWeightedSource α s.1) (radialClamp R r),
     c.2*(Real.exp (-α*(radialClamp R r)^2) : ℂ)+
       (Real.exp (-α*(radialClamp R r)^2) : ℂ)*
         spectralRegularPrimitive d (-1) (spectralRegularWeightedSource α s.2) (radialClamp R r)) at he
  rw [radialClamp_eq R r hr] at he
  rw [he]
  apply Prod.ext <;> simp only [spectralRegularLift,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  all_goals ring

theorem spectralRegularLift_unweight (d : ℕ) (R α : ℝ) (hR : 0 ≤ R) (hα : 0 < α)
    (c : ℂ × ℂ) (v s : RegularSpectralSpace)
    (hv : v=spectralRegularInitial R α hα.le c+spectralRegularPairKernel d R α hR hα s)
    (r : ℝ) (hr : r ∈ Icc 0 R) :
    (Real.exp (α*r^2) : ℂ) • (v.1 r,v.2 r)=spectralRegularLift d α c s r := by
  rw [spectralRegularLift_weighted d R α hR hα c v s hv r hr,smul_smul]
  have he : (Real.exp (α*r^2) : ℂ)*(Real.exp (-α*r^2) : ℂ)=1 := by
    rw [← Complex.ofReal_mul,← Real.exp_add]
    simp
  rw [he,one_smul]

end DefocusingNLS

end OAI
