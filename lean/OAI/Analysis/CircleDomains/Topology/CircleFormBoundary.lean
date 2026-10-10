import OAI.Analysis.CircleDomains.Topology.FiniteCircleStokes
import OAI.Analysis.CircleDomains.Modulus.CircleBoundaryOscillation
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace OAI

/-! Actual boundary terms for the finite-circle Stokes formula. Smoothness
and integrability of real lifts follow from the circle coordinate, rather
than being extra analytic hypotheses on each boundary. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem contDiff_unitCircleParam (c : ℂ) (r : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (unitCircleParam c r) :=
  (contDiff_circleMap c r).comp (contDiff_const.mul contDiff_id)

 theorem lipschitzWith_unitCircleParam (c : ℂ) (r : ℝ) :
    LipschitzWith (Real.nnabs r * ‖(2 * Real.pi : ℝ)‖₊) (unitCircleParam c r) := by
  exact (lipschitzWith_circleMap c r).comp (lipschitzWith_smul (2 * Real.pi : ℝ))

 theorem contDiff_real_lift_along
    {O : Set ℂ} {u : ℂ → UnitAddCircle} (hu : SmoothCircleOn u O)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγO : ∀ t, γ t ∈ O)
    {v : ℝ → ℝ} (hv : Continuous v) (hproj : ∀ t, (v t : UnitAddCircle) = u (γ t)) :
    ContDiff ℝ (⊤ : ℕ∞) v := by
  apply contDiffOn_univ.mp
  apply contDiffOn_real_lift isOpen_univ _ hv.continuousOn (fun t _ => hproj t)
  intro t _ a ha
  exact (hu (γ t) (hγO t) a ha).comp t hγ.contDiffAt

 theorem circleFormIntegral_unitCircle_zero_period
    {O : Set ℂ} (hO : IsOpen O) {u : ℂ → UnitAddCircle} (hu : SmoothCircleOn u O)
    (φ : ℂ → ℝ) (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ O) (hφlip : LipschitzWith 1 φ)
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hcircle : ∀ t, unitCircleParam c r t ∈ O)
    (v : ℝ → ℝ) (hv : Continuous v)
    (hproj : ∀ t, (v t : UnitAddCircle) = u (unitCircleParam c r t))
    (hperiod : v 1 = v 0) (A : ℝ) (hA : ∀ t ∈ Icc (0 : ℝ) 1, |v t - v 0| ≤ A) :
    |circleFormIntegral φ u (unitCircleParam c r)| ≤ 2 * Real.pi * r * A := by
  have hc := contDiff_unitCircleParam c r
  have hvs := contDiff_real_lift_along hu hc hcircle hv hproj
  have hφs : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ unitCircleParam c r) := by
    apply contDiffOn_univ.mp
    intro t _
    exact ((hφ.contDiffAt (hO.mem_nhds (hcircle t))).comp t hc.contDiffAt).contDiffWithinAt
  rw [circleFormIntegral_eq_real_lift hO hu φ _ (hc.differentiable (by simp)) hcircle v hv hproj]
  have hb := zero_period_weighted_integral_bound (K := 2 * Real.pi * r) (φ ∘ unitCircleParam c r)
    (deriv (φ ∘ unitCircleParam c r)) v (deriv v) zero_le_one
    (fun t _ => (hφs.differentiable (by simp) t).hasDerivAt)
    (fun t _ => (hvs.differentiable (by simp) t).hasDerivAt)
    ((hφs.continuous_deriv (by simp)).intervalIntegrable 0 1)
    ((hvs.continuous_deriv (by simp)).intervalIntegrable 0 1) hperiod ?_ hA
  · simpa only [one_mul, Function.comp_apply] using hb
  · intro t _
    have hd := (hφs.differentiable (by simp) t).hasDerivAt.le_of_lipschitz
      (hφlip.comp (lipschitzWith_unitCircleParam c r))
    have hb : |deriv (φ ∘ unitCircleParam c r) t| ≤ r * (2 * Real.pi) := by
      simpa only [Real.norm_eq_abs, NNReal.coe_mul, NNReal.coe_one, one_mul,
        Real.coe_nnabs, coe_nnnorm, abs_of_nonneg hr,
        abs_of_pos (show (0 : ℝ) < 2 * Real.pi by positivity)] using hd
    calc
      _ ≤ r * (2 * Real.pi) := hb
      _ = _ := by ring

 theorem circleFormIntegral_constant_weight
    {O : Set ℂ} (hO : IsOpen O) {u : ℂ → UnitAddCircle} (hu : SmoothCircleOn u O)
    (φ : ℂ → ℝ) (γ : ℝ → ℂ) (hγ : ContDiff ℝ (⊤ : ℕ∞) γ)
    (hγO : ∀ t, γ t ∈ O) (v : ℝ → ℝ) (hv : Continuous v)
    (hproj : ∀ t, (v t : UnitAddCircle) = u (γ t))
    (ρ : ℝ) (hφ : ∀ t ∈ Icc (0 : ℝ) 1, φ (γ t) = ρ) :
    circleFormIntegral φ u γ = ρ * (v 1 - v 0) := by
  have hvs := contDiff_real_lift_along hu hγ hγO hv hproj
  rw [circleFormIntegral_eq_real_lift hO hu φ γ (hγ.differentiable (by simp)) hγO v hv hproj]
  calc
    _ = ∫ t in (0 : ℝ)..1, ρ * deriv v t := by
      apply intervalIntegral.integral_congr
      intro t ht
      change φ (γ t) * deriv v t = ρ * deriv v t
      rw [hφ t (by simpa only [uIcc_of_le zero_le_one] using ht)]
    _ = ρ * (v 1 - v 0) := constant_weight_integral_eq_period v (deriv v) 1 ρ
      (fun t _ => (hvs.differentiable (by simp) t).hasDerivAt)
      ((hvs.continuous_deriv (by simp)).intervalIntegrable 0 1)

end CircleDomainRigidity

end

end OAI
