import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HighAngularGeometry
import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowGaugeDerivativeGrowth
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! Exponential decay on the actual outgoing rays, with a polynomial weight. -/

open Filter Topology
namespace DefocusingNLS

theorem highRay_norm_bounds (Z h t : ℝ) (hh : h=1 ∨ h= -1)
    (hZ : 2704/1000 ≤ Z) (hZ' : Z ≤ 2706/1000) (ht : 2 ≤ t) :
    1 ≤ ‖highRayPoint Z h t‖ ∧ ‖highRayPoint Z h t‖ ≤ 5*t ∧
      (98/100)*t ≤ (highRayPoint Z h t).re := by
  obtain ⟨hu,hu',hv,hv',_⟩ := highRay_bounds Z t hZ hZ' (by linarith)
  have hure : (highRayPoint Z h t).re=highRayU t := highRayPoint_re Z h t
  have hlower : (highRayPoint Z h t).re ≤ ‖highRayPoint Z h t‖ :=
    (le_abs_self _).trans (Complex.abs_re_le_norm _)
  refine ⟨by linarith,?_,by linarith⟩
  have hn := Complex.norm_le_abs_re_add_abs_im (highRayPoint Z h t)
  have hu0 : 0 ≤ highRayU t := by linarith
  rcases hh with rfl | rfl <;>
    simp [highRayPoint,abs_of_nonneg hu0,abs_of_pos hv] at hn ⊢ <;> linarith

theorem highRay_envelope_tendsto_zero (f : ℂ → ℂ) (p C : ℝ) (k : ℕ)
    (hp : 0 ≤ p) (hC : 0 ≤ C)
    (hbound : ∀ x : ℂ, 0 ≤ x.re → 1 ≤ ‖x‖ →
      ‖f x‖ ≤ C*Real.exp (-x.re/2)*‖x‖^p)
    (Z h : ℝ) (hh : h=1 ∨ h= -1)
    (hZ : 2704/1000 ≤ Z) (hZ' : Z ≤ 2706/1000) :
    Tendsto (fun t : ℝ => (t : ℂ)^k*f (highRayPoint Z h t)) atTop (𝓝 0) := by
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((k : ℝ)+p) (49/100) (by norm_num)).const_mul (C*5^p)
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
  obtain ⟨hn,hn',hr⟩ := highRay_norm_bounds Z h t hh hZ hZ' ht
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 ≤ (highRayPoint Z h t).re := by linarith
  have hexp : Real.exp (-(highRayPoint Z h t).re/2) ≤ Real.exp (-(49/100)*t) :=
    Real.exp_le_exp.mpr (by linarith)
  have hpbound := Real.rpow_le_rpow (norm_nonneg (highRayPoint Z h t)) hn' hp
  calc
    _ = t^k*‖f (highRayPoint Z h t)‖ := by
      rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg ht0]
    _ ≤ t^k*(C*Real.exp (-(highRayPoint Z h t).re/2)*‖highRayPoint Z h t‖^p) :=
      mul_le_mul_of_nonneg_left (hbound _ hx0 hn) (pow_nonneg ht0 k)
    _ ≤ t^k*(C*Real.exp (-(49/100)*t)*(5*t)^p) := by
      gcongr
    _ = C*5^p*(t^((k : ℝ)+p)*Real.exp (-(49/100)*t)) := by
      rw [Real.mul_rpow (by norm_num) ht0,Real.rpow_add (by linarith : 0 < t),
        Real.rpow_natCast]
      ring

theorem highRay_gaugedSlowSolution_decay (q : ℂ) (M k : ℕ) (hq : -1 < q.re)
    (Z h : ℝ) (hh : h=1 ∨ h= -1)
    (hZ : 2704/1000 ≤ Z) (hZ' : Z ≤ 2706/1000) :
    Tendsto (fun t : ℝ => (t : ℂ)^k*gaugedSlowSolution q M (highRayPoint Z h t))
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := gaugedSlowSolution_polynomial_envelope q M hq
  exact highRay_envelope_tendsto_zero _ _ C k (by positivity) hC hbound Z h hh hZ hZ'

theorem highRay_gaugedSlowSolution_derivative_decay (q : ℂ) (M k : ℕ)
    (hq : -1 < q.re) (Z h : ℝ) (hh : h=1 ∨ h= -1)
    (hZ : 2704/1000 ≤ Z) (hZ' : Z ≤ 2706/1000) :
    Tendsto (fun t : ℝ => (t : ℂ)^k*deriv (gaugedSlowSolution q M) (highRayPoint Z h t))
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := gaugedSlowSolution_derivative_polynomial_envelope q M hq
  exact highRay_envelope_tendsto_zero _ _ C k (by positivity) hC hbound Z h hh hZ hZ'

end DefocusingNLS

end OAI
