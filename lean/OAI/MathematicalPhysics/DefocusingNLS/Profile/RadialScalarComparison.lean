import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPowerSlope
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialLinearComparison

namespace OAI

/-! Order and uniqueness for the nonlinear scalar inner problem. -/

open Set
namespace DefocusingNLS

theorem radial_scalar_sub_super_comparison (p : ℕ) (R : ℝ) (hR : 0 < R) (hR2 : R^2 ≤ 11)
    (A B V : ℝ → ℝ) (hA : Differentiable ℝ A) (hB : Differentiable ℝ B)
    (hDA : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv A) r)
    (hDB : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv B) r)
    (hA0 : deriv A 0=0) (hB0 : deriv B 0=0) (hboundary : A R ≤ B R)
    (hAN : ∀ r ∈ Icc 0 R, 0 ≤ A r) (hBN : ∀ r ∈ Icc 0 R, 0 ≤ B r)
    (hV : ∀ r ∈ Ioo 0 R, V r ≤ (1/2 : ℝ))
    (hAE : ∀ r ∈ Ioo 0 R, -deriv (deriv A) r-11/r*deriv A r+(A r)^p≤V r*A r)
    (hBE : ∀ r ∈ Ioo 0 R, -deriv (deriv B) r-11/r*deriv B r+(B r)^p≥V r*B r) :
    ∀ r ∈ Icc 0 R, A r ≤ B r := by
  let d := B-A
  let q := fun r => radialPowerSlope p (B r) (A r)
  have hd : Differentiable ℝ d := hB.sub hA
  have hd1 : deriv d=fun r => deriv B r-deriv A r := by
    funext r
    exact ((hB r).hasDerivAt.sub (hA r).hasDerivAt).deriv
  have hdd (r : ℝ) (hr : r ∈ Ioo 0 R) :
      deriv (deriv d) r=deriv (deriv B) r-deriv (deriv A) r := by
    rw [hd1]
    exact ((hDB r hr).hasDerivAt.sub (hDA r hr).hasDerivAt).deriv
  have hdreg : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv d) r := by
    intro r hr
    rw [hd1]
    exact (hDB r hr).sub (hDA r hr)
  have hd0 : deriv d 0=0 := by rw [hd1]; change deriv B 0-deriv A 0=0; rw [hB0,hA0,sub_self]
  have hdR : 0 ≤ d R := sub_nonneg.2 hboundary
  have hq : ∀ r ∈ Ioo 0 R, 0 ≤ q r := by
    intro r hr
    exact radialPowerSlope_nonneg p _ _ (hBN r ⟨hr.1.le,hr.2.le⟩) (hAN r ⟨hr.1.le,hr.2.le⟩)
  have hOp : ∀ r ∈ Ioo 0 R,
      0 ≤ -deriv (deriv d) r-11/r*deriv d r+(q r-V r)*d r := by
    intro r hr
    rw [hdd r hr,hd1]
    change 0 ≤ -(deriv (deriv B) r-deriv (deriv A) r)-11/r*(deriv B r-deriv A r)+
      (q r-V r)*(B r-A r)
    have hpow := radialPowerSlope_identity p (B r) (A r)
    change q r*(B r-A r)=(B r)^p-(A r)^p at hpow
    nlinarith [hAE r hr,hBE r hr]
  have hpos := radial_linear_comparison R hR hR2 d V q hd hdreg hd0 hdR hV hq hOp
  intro r hr
  exact sub_nonneg.1 (hpos r hr)

theorem radial_scalar_comparison (p : ℕ) (R : ℝ) (hR : 0 < R) (hR2 : R^2 ≤ 11)
    (A B V : ℝ → ℝ) (hA : Differentiable ℝ A) (hB : Differentiable ℝ B)
    (hDA : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv A) r)
    (hDB : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv B) r)
    (hA0 : deriv A 0=0) (hB0 : deriv B 0=0) (hboundary : A R ≤ B R)
    (hAN : ∀ r ∈ Icc 0 R, 0 ≤ A r) (hBN : ∀ r ∈ Icc 0 R, 0 ≤ B r)
    (hV : ∀ r ∈ Ioo 0 R, V r ≤ (1/2 : ℝ))
    (hAE : ∀ r ∈ Ioo 0 R, -deriv (deriv A) r-11/r*deriv A r+(A r)^p=V r*A r)
    (hBE : ∀ r ∈ Ioo 0 R, -deriv (deriv B) r-11/r*deriv B r+(B r)^p=V r*B r) :
    ∀ r ∈ Icc 0 R, A r ≤ B r := by
  exact radial_scalar_sub_super_comparison p R hR hR2 A B V hA hB hDA hDB hA0 hB0
    hboundary hAN hBN hV (fun r hr => (hAE r hr).le) (fun r hr => (hBE r hr).ge)

theorem radial_scalar_unique (p : ℕ) (R : ℝ) (hR : 0 < R) (hR2 : R^2 ≤ 11)
    (A B V : ℝ → ℝ) (hA : Differentiable ℝ A) (hB : Differentiable ℝ B)
    (hDA : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv A) r)
    (hDB : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv B) r)
    (hA0 : deriv A 0=0) (hB0 : deriv B 0=0) (hboundary : A R=B R)
    (hAN : ∀ r ∈ Icc 0 R, 0 ≤ A r) (hBN : ∀ r ∈ Icc 0 R, 0 ≤ B r)
    (hV : ∀ r ∈ Ioo 0 R, V r ≤ (1/2 : ℝ))
    (hAE : ∀ r ∈ Ioo 0 R, -deriv (deriv A) r-11/r*deriv A r+(A r)^p=V r*A r)
    (hBE : ∀ r ∈ Ioo 0 R, -deriv (deriv B) r-11/r*deriv B r+(B r)^p=V r*B r) :
    EqOn A B (Icc 0 R) := by
  have hle := radial_scalar_comparison p R hR hR2 A B V hA hB hDA hDB hA0 hB0 hboundary.le hAN hBN hV hAE hBE
  have hge := radial_scalar_comparison p R hR hR2 B A V hB hA hDB hDA hB0 hA0 hboundary.ge hBN hAN hV hBE hAE
  intro r hr
  exact le_antisymm (hle r hr) (hge r hr)

end DefocusingNLS

end OAI
