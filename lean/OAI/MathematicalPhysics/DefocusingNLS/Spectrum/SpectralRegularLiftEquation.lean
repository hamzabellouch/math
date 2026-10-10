import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularLift

namespace OAI

/-! The recovered regular columns satisfy the coupled radial spectral equation. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem spectralRegularLift_source (d : ℕ) (R α : ℝ) (hR : 0 ≤ R) (hα : 0 < α)
    (A B : ℝ →ᵇ ℂ) (cp cm : ℂ) (c : ℂ × ℂ) (v s : RegularSpectralSpace)
    (hv : v=spectralRegularInitial R α hα.le c+spectralRegularPairKernel d R α hR hα s)
    (hs : s=spectralRegularSourceCLM A B cp cm v) (r : ℝ) (hr : r ∈ Icc 0 R) :
    let w := spectralRegularLift d α c s r
    (spectralRegularWeightedSource α s.1 r,spectralRegularWeightedSource α s.2 r)=
      (A r*w.1+B r*w.2-cp*w.1,star (B r)*w.1+star (A r)*w.2-cm*w.2) := by
  intro w
  have he := spectralRegularLift_unweight d R α hR hα c v s hv r hr
  have hp : (Real.exp (α*r^2) : ℂ)*v.1 r=w.1 := congrArg Prod.fst he
  have hm : (Real.exp (α*r^2) : ℂ)*v.2 r=w.2 := congrArg Prod.snd he
  rw [hs]
  change ((Real.exp (α*r^2) : ℂ)*(A r*v.1 r+B r*v.2 r-cp*v.1 r),
    (Real.exp (α*r^2) : ℂ)*(star (B r)*v.1 r+star (A r)*v.2 r-cm*v.2 r))=_
  apply Prod.ext
  · calc
      _ = A r*((Real.exp (α*r^2) : ℂ)*v.1 r)+
          B r*((Real.exp (α*r^2) : ℂ)*v.2 r)-cp*((Real.exp (α*r^2) : ℂ)*v.1 r) := by ring
      _ = _ := by rw [hp,hm]
  · calc
      _ = star (B r)*((Real.exp (α*r^2) : ℂ)*v.1 r)+
          star (A r)*((Real.exp (α*r^2) : ℂ)*v.2 r)-cm*((Real.exp (α*r^2) : ℂ)*v.2 r) := by ring
      _ = _ := by rw [hp,hm]

theorem spectralRegularLift_equation (d : ℕ) (α : ℝ) (c : ℂ × ℂ)
    (s : RegularSpectralSpace) (r : ℝ) (hr : 0 < r) :
    let wp := fun t => (spectralRegularLift d α c s t).1
    let wm := fun t => (spectralRegularLift d α c s t).2
    (deriv (deriv wp) r+((d : ℂ)/(r : ℂ)+Complex.I*(r/2 : ℝ))*deriv wp r,
     deriv (deriv wm) r+((d : ℂ)/(r : ℂ)-Complex.I*(r/2 : ℝ))*deriv wm r)=
      (spectralRegularWeightedSource α s.1 r,spectralRegularWeightedSource α s.2 r) := by
  dsimp only [spectralRegularLift]
  simp only [deriv_const_add']
  apply Prod.ext
  · simpa only [one_mul] using spectralRegularPrimitive_equation d 1 _
      (spectralRegularWeightedSource_continuous α s.1) r hr
  · have hm := spectralRegularPrimitive_equation d (-1) _
      (spectralRegularWeightedSource_continuous α s.2) r hr
    convert! hm using 1
    push_cast
    ring

theorem spectralRegularLift_coupled_equation (d : ℕ) (R α : ℝ)
    (hR : 0 ≤ R) (hα : 0 < α) (A B : ℝ →ᵇ ℂ) (cp cm : ℂ) (c : ℂ × ℂ)
    (v s : RegularSpectralSpace)
    (hv : v=spectralRegularInitial R α hα.le c+spectralRegularPairKernel d R α hR hα s)
    (hs : s=spectralRegularSourceCLM A B cp cm v) (r : ℝ) (hr : r ∈ Ioc 0 R) :
    let wp := fun t => (spectralRegularLift d α c s t).1
    let wm := fun t => (spectralRegularLift d α c s t).2
    (deriv (deriv wp) r+((d : ℂ)/(r : ℂ)+Complex.I*(r/2 : ℝ))*deriv wp r,
     deriv (deriv wm) r+((d : ℂ)/(r : ℂ)-Complex.I*(r/2 : ℝ))*deriv wm r)=
      (A r*wp r+B r*wm r-cp*wp r,star (B r)*wp r+star (A r)*wm r-cm*wm r) :=
  (spectralRegularLift_equation d α c s r hr.1).trans
    (spectralRegularLift_source d R α hR hα A B cp cm c v s hv hs r ⟨hr.1.le,hr.2⟩)

end DefocusingNLS

end OAI
