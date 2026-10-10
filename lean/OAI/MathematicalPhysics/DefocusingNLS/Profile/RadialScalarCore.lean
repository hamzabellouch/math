import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCoreBarrier

namespace OAI

/-! The actual scalar solution lies above the constant core of the smooth barrier. -/

open Set
namespace DefocusingNLS

theorem radial_scalar_core_lower (p : ℕ) (hp : 2 ≤ p) (R m lo : ℝ)
    (hR : 1 ≤ R) (hR2 : R^2 ≤ 11) (hm : (999/1000 : ℝ) ≤ m) (hm1 : m ≤ 1)
    (hmp : m^(p-1)=(1/5 : ℝ)) (hlo : 1-(1/10000 : ℝ)^2/5 ≤ lo)
    (A V : ℝ → ℝ) (hA : Differentiable ℝ A)
    (hDA : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv A) r)
    (hA0 : deriv A 0=0) (hAR : A R=lo)
    (hAN : ∀ r ∈ Icc 0 R, 0 ≤ A r)
    (hV : ∀ r ∈ Ioo 0 R, V r ∈ Icc (3/10 : ℝ) (1/2))
    (hAE : ∀ r ∈ Ioo 0 R, -deriv (deriv A) r-11/r*deriv A r+(A r)^p=V r*A r) :
    ∀ r ∈ Icc 0 R, r ≤ R-7/10000 → m ≤ A r := by
  have hB := radial_scalar_sub_super_comparison p R (by linarith) hR2
    (radialCoreBarrier R m) A V
    (differentiable_radialLowerBarrier _ _ _ (by norm_num)) hA
    (fun r _ => differentiable_deriv_radialLowerBarrier _ _ _ (by norm_num) r) hDA
    (radialCoreBarrier_origin R m hR) hA0
    (by rw [hAR]; exact radialCoreBarrier_boundary R m lo hm1 hlo)
    (fun r hr => le_trans (by norm_num) (radialCoreBarrier_bounds R m r hm hr).1)
    hAN (fun r hr => (hV r hr).2)
    (radialCoreBarrier_subsolution p hp R m hR hm hmp V (fun r hr => (hV r hr).1))
    (fun r hr => (hAE r hr).ge)
  intro r hr hc
  have hb := hB r hr
  rwa [radialCoreBarrier_flat R m r hc] at hb

end DefocusingNLS

end OAI
