import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBConstruction
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBSqrtApproximation

namespace OAI

/-! The action is monotone after choosing the orientation of the WKB pair.
For an oscillatory branch the choice depends only on the sign of gamma. -/

open Set
namespace DefocusingNLS

theorem spectralComplexSqrt_re_pos (x y : ℝ) (hx : 0<x) :
    0<(Complex.sqrt ((x : ℂ)+Complex.I*(y : ℂ))).re := by
  let p := Complex.sqrt ((x : ℂ)+Complex.I*(y : ℂ))
  have hp := spectralComplexSqrt_sq ((x : ℂ)+Complex.I*(y : ℂ))
  have hn := spectralComplexSqrt_re_nonneg ((x : ℂ)+Complex.I*(y : ℂ))
  change p^2=(x : ℂ)+Complex.I*(y : ℂ) at hp
  have he := congrArg Complex.re hp
  simp only [pow_two,Complex.mul_re,Complex.add_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,zero_mul,mul_zero,sub_self,add_zero] at he
  change 0≤p.re at hn
  change 0<p.re
  nlinarith [sq_nonneg p.im]

theorem spectralComplexSqrt_im_sign (x y : ℝ) (hx : 0<x) :
    (0≤y → 0≤(Complex.sqrt ((x : ℂ)+Complex.I*(y : ℂ))).im) ∧
    (y≤0 → (Complex.sqrt ((x : ℂ)+Complex.I*(y : ℂ))).im≤0) := by
  let p := Complex.sqrt ((x : ℂ)+Complex.I*(y : ℂ))
  have hr : 0<p.re := spectralComplexSqrt_re_pos x y hx
  have he := congrArg Complex.im (spectralComplexSqrt_sq ((x : ℂ)+Complex.I*(y : ℂ)))
  simp only [pow_two,Complex.mul_im,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,one_mul,zero_add] at he
  change p.re*p.im+p.im*p.re=y at he
  constructor <;> intro hy <;> nlinarith

theorem spectralWKBPhase_monotone (R E : ℝ) (hRE : R≤E) (chi : ℂ)
    (p : ℝ → ℂ) (hp : ContinuousOn p (Icc R E))
    (hpositive : ∀ r ∈ Ioo R E, 0≤(chi*p r).re) :
    MonotoneOn (fun r => (spectralWKBPhase R chi p r).re) (Icc R E) := by
  have hc := Complex.continuous_re.comp_continuousOn
    (spectralWKBPhase_continuousOn R E hRE chi p hp)
  have hd (r : ℝ) (hr : r ∈ Ioo R E) :
      HasDerivAt (fun t => (spectralWKBPhase R chi p t).re) (chi*p r).re r :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt r (spectralWKBPhase_hasDerivAt R E chi p hp r hr)
  apply monotoneOn_of_deriv_nonneg (convex_Icc R E) hc
  · intro r hr
    exact (hd r (by simpa only [interior_Icc] using hr)).differentiableAt.differentiableWithinAt
  · intro r hr
    have hri : r ∈ Ioo R E := by simpa only [interior_Icc] using hr
    change 0≤deriv (fun t => (spectralWKBPhase R chi p t).re) r
    rw [(hd r hri).deriv]
    exact hpositive r hri

end DefocusingNLS

end OAI
