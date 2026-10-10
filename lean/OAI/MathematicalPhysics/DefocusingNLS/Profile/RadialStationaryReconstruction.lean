import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialClampedPhase
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPolarBalance
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPolarEquation

namespace OAI

/-! The coupled positive inner amplitude reconstructs an actual complex stationary solution. -/

open Set
namespace DefocusingNLS

noncomputable def radialInnerPhase (R a : ℝ) (A : ℝ → ℝ) : ℝ → ℝ :=
  radialPhase (6-2*a) (radialClampedAmplitude R A)

noncomputable def radialInnerComplex (R a : ℝ) (A : ℝ → ℝ) : ℝ → ℂ :=
  radialPolar A (radialInnerPhase R a A)

theorem radialInnerComplex_stationary (p : ℕ) (hp : 1 ≤ p) (R a b : ℝ) (hR : 0 ≤ R)
    (A : ℝ → ℝ) (hA : Differentiable ℝ A)
    (hAP : ∀ r ∈ Icc 0 R, 0 < A r)
    (hDA : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv A) r)
    (hEq : ∀ r ∈ Ioo 0 R, -deriv (deriv A) r-11/r*deriv A r+(A r)^p=
      radialAmplitudePotential (6-2*a) b A r*A r) :
    ∀ r ∈ Ioo 0 R,
      deriv (deriv (radialInnerComplex R a A)) r+
      (11/r : ℝ)*deriv (radialInnerComplex R a A) r+
      Complex.I*((r/2 : ℝ)*deriv (radialInnerComplex R a A) r+
        (a : ℂ)*radialInnerComplex R a A r)+
      (b : ℂ)*radialInnerComplex R a A r=
        ((A r)^(p-1) : ℝ)*radialInnerComplex R a A r := by
  let B := radialClampedAmplitude R A
  let φ := radialInnerPhase R a A
  have hB : Continuous B := radialClampedAmplitude_continuous R A hA.continuous
  have hBP : ∀ t, B t ≠ 0 := by
    intro t
    exact (hAP _ (radialClamp_mem R t hR)).ne'
  have hφ : Differentiable ℝ φ := radialPhase_differentiable (6-2*a) B hB hBP
  intro r hr
  have hrne : r ≠ 0 := hr.1.ne'
  have hrC : r ∈ Icc 0 R := ⟨hr.1.le,hr.2.le⟩
  have hAr : A r ≠ 0 := (hAP r hrC).ne'
  let w := radialVelocity (6-2*a) B r
  let w₁ := 6-2*a-11*radialVelocityRatio (6-2*a) B r-2*w*deriv A r/A r
  have hBr : B r=A r := radialClampedAmplitude_eq R A r hrC
  have hφ₁ : deriv φ r=(w-r/2)/2 := (radialPhase_hasDerivAt (6-2*a) B hB hBP r).deriv
  have hφ₂ : HasDerivAt (deriv φ) ((w₁-1/2)/2) r := by
    have h := radialPhase_deriv_hasDerivAt (6-2*a) (deriv A r) B hB hBP r hrne
      (radialClampedAmplitude_hasDerivAt R A hA r hr)
    change HasDerivAt (deriv (radialPhase (6-2*a) B))
      ((6-2*a-11*radialVelocityRatio (6-2*a) B r-
        2*radialVelocity (6-2*a) B r*deriv A r/A r-1/2)/2) r
    simpa only [hBr] using h
  have hw : w₁=6-2*a-11/r*w-2*w*deriv A r/A r := by
    dsimp only [w₁,w,radialVelocity]
    field_simp [hrne]
  have hV : radialAmplitudePotential (6-2*a) b A r=b+r^2/16-w^2/4 := by
    dsimp only [w]
    rw [radialVelocity_clamped_eq (6-2*a) R A r hrC]
    unfold radialAmplitudePotential radialVelocity
    ring
  have hpow : (A r)^p=(A r)^(p-1)*A r := by
    rw [← pow_succ]
    congr 1
    omega
  have hReal := radialPolar_real_balance (A r) (deriv A r) (deriv (deriv A) r) w r b ((A r)^(p-1)) (by
    have h := hEq r hr
    rwa [hV,hpow] at h)
  have hImag := radialPolar_imag_balance (A r) (deriv A r) w w₁ r a hAr hrne hw
  apply radialPolar_stationary_of_balances A φ hA hφ r a b ((A r)^(p-1)) (hDA r hr)
    hφ₂.differentiableAt
  · rwa [hφ₁]
  · rwa [hφ₁,hφ₂.deriv]

theorem radialInnerComplex_origin (R a : ℝ) (A : ℝ → ℝ) :
    radialInnerComplex R a A 0=(A 0 : ℂ) := by
  simp only [radialInnerComplex,radialPolar,radialInnerPhase,radialPhase_origin,
    Complex.ofReal_zero,mul_zero,Complex.exp_zero,mul_one]

theorem radialInnerComplex_norm (R a : ℝ) (A : ℝ → ℝ) (r : ℝ) (hA : 0 ≤ A r) :
    ‖radialInnerComplex R a A r‖=A r := by
  rw [radialInnerComplex,radialPolar_norm,abs_of_nonneg hA]

end DefocusingNLS

end OAI
