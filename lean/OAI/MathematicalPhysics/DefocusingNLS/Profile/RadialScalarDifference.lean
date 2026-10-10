import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSmallInverse
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPowerSlope

namespace OAI

/-! The small inverse bounds the difference of two genuine scalar outputs. -/

open Set
namespace DefocusingNLS

theorem radial_scalar_difference_equation (p : ℕ) (V W A B : ℝ → ℝ)
    (hA : Differentiable ℝ A) (hB : Differentiable ℝ B) (r : ℝ)
    (hDA : DifferentiableAt ℝ (deriv A) r) (hDB : DifferentiableAt ℝ (deriv B) r)
    (hAE : -deriv (deriv A) r-11/r*deriv A r+(A r)^p=V r*A r)
    (hBE : -deriv (deriv B) r-11/r*deriv B r+(B r)^p=W r*B r) :
    radialLinearOperator V (fun t => radialPowerSlope p (A t) (B t)) (A-B) r=
      (V r-W r)*B r := by
  rw [radialLinearOperator_sub V _ A B hA hB r hDA hDB]
  unfold radialLinearOperator
  have hp := radialPowerSlope_identity p (A r) (B r)
  nlinarith

theorem radial_scalar_difference_bound (p : ℕ) (hp : 10 ≤ p) (R m D : ℝ)
    (hR : 1 ≤ R) (hR2 : R^2 ≤ 11) (hD : 0 ≤ D)
    (hm : 0 ≤ m) (hmp : m^(p-1)=(1/5 : ℝ))
    (V W A B : ℝ → ℝ) (hA : Differentiable ℝ A) (hB : Differentiable ℝ B)
    (hDA : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv A) r)
    (hDB : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv B) r)
    (hA0 : deriv A 0=0) (hB0 : deriv B 0=0) (hAR : A R=B R)
    (hAN : ∀ r ∈ Icc 0 R, 0 ≤ A r) (hBN : ∀ r ∈ Icc 0 R, B r ∈ Icc 0 1)
    (hcoreA : ∀ r ∈ Icc 0 R, r ≤ R-7/10000 → m ≤ A r)
    (hcoreB : ∀ r ∈ Icc 0 R, r ≤ R-7/10000 → m ≤ B r)
    (hV : ∀ r ∈ Ioo 0 R, V r ≤ (1/2 : ℝ))
    (hVW : ∀ r ∈ Ioo 0 R, |V r-W r| ≤ D)
    (hAE : ∀ r ∈ Ioo 0 R, -deriv (deriv A) r-11/r*deriv A r+(A r)^p=V r*A r)
    (hBE : ∀ r ∈ Ioo 0 R, -deriv (deriv B) r-11/r*deriv B r+(B r)^p=W r*B r) :
    ∀ r ∈ Icc 0 R, |A r-B r| ≤ D*(10/(p : ℝ)+(8/10000 : ℝ)^2) := by
  have hd : deriv (A-B)=fun r => deriv A r-deriv B r := by
    funext r
    exact ((hA r).hasDerivAt.sub (hB r).hasDerivAt).deriv
  have hDAB : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv (A-B)) r := by
    intro r hr
    rw [hd]
    exact (hDA r hr).sub (hDB r hr)
  have hd0 : deriv (A-B) 0=0 := by
    rw [hd]
    change deriv A 0-deriv B 0=0
    rw [hA0,hB0,sub_self]
  have hq : ∀ r ∈ Ioo 0 R, 0 ≤ radialPowerSlope p (A r) (B r) := by
    intro r hr
    exact radialPowerSlope_nonneg p _ _ (hAN r ⟨hr.1.le,hr.2.le⟩) (hBN r ⟨hr.1.le,hr.2.le⟩).1
  have hqc : ∀ r ∈ Ioo 0 R, r ≤ R-7/10000 → (p : ℝ)/5 ≤ radialPowerSlope p (A r) (B r) := by
    intro r hr hc
    have h := radialPowerSlope_lower p m (A r) (B r) hm
      (hcoreA r ⟨hr.1.le,hr.2.le⟩ hc) (hcoreB r ⟨hr.1.le,hr.2.le⟩ hc)
    simpa only [hmp,mul_one_div] using h
  apply radial_small_inverse_bound p hp R D hR hR2 hD V
    (fun r => radialPowerSlope p (A r) (B r)) (A-B) (hA.sub hB) hDAB hd0
    (by change A R-B R=0; exact sub_eq_zero.2 hAR) hV hq hqc
  intro r hr
  rw [radial_scalar_difference_equation p V W A B hA hB r (hDA r hr) (hDB r hr) (hAE r hr) (hBE r hr),abs_mul]
  have hb := hBN r ⟨hr.1.le,hr.2.le⟩
  rw [abs_of_nonneg hb.1]
  calc
    |V r-W r| *B r ≤ D*1 := mul_le_mul (hVW r hr) hb.2 hb.1 hD
    _ = D := mul_one _

end DefocusingNLS

end OAI
