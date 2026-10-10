import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSmoothBarrierRegular
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialLinearOperator

namespace OAI

/-! An explicit small supersolution for the inner linearized scalar operator. -/

open Set
namespace DefocusingNLS

noncomputable def radialSmallInverseBarrier (p : ℕ) (R : ℝ) : ℝ → ℝ :=
  radialInverseBarrier (1/10000) (R-8/10000) R (10/(p : ℝ))

theorem radialSmallInverseBarrier_bounds (p : ℕ) (R r : ℝ) (hr : r ∈ Icc 0 R) :
    10/(p : ℝ) ≤ radialSmallInverseBarrier p R r ∧
      radialSmallInverseBarrier p R r ≤ 10/(p : ℝ)+(8/10000 : ℝ)^2 := by
  simpa only [radialSmallInverseBarrier,sub_sub_cancel] using
    radialInverseBarrier_bounds (1/10000) (R-8/10000) R (10/(p : ℝ))
      (by norm_num) (by linarith) r hr

theorem radialSmallInverseBarrier_origin (p : ℕ) (R : ℝ) (hR : 1 ≤ R) :
    deriv (radialSmallInverseBarrier p R) 0=0 := by
  rw [show radialSmallInverseBarrier p R=radialInverseBarrier (1/10000) (R-8/10000) R (10/(p : ℝ)) from rfl,
    (hasDerivAt_radialInverseBarrier _ _ _ _ _ (by norm_num)).deriv]
  have hf := (radialSmoothRamp_flat (1/10000) (0-(R-8/10000)) (by linarith)).2.1
  rw [hf,neg_zero]

theorem radialSmallInverseBarrier_supersolution (p : ℕ) (hp : 10 ≤ p)
    (R : ℝ) (V q : ℝ → ℝ)
    (hV : ∀ r ∈ Ioo 0 R, V r ≤ (1/2 : ℝ))
    (hq : ∀ r ∈ Ioo 0 R, 0 ≤ q r)
    (hcore : ∀ r ∈ Ioo 0 R, r ≤ R-7/10000 → (p : ℝ)/5 ≤ q r) :
    ∀ r ∈ Ioo 0 R, 1 ≤ radialLinearOperator V q (radialSmallInverseBarrier p R) r := by
  intro r hr
  have hpR : (10 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hSb := radialSmallInverseBarrier_bounds p R r ⟨hr.1.le,hr.2.le⟩
  have ha : 0 ≤ 10/(p : ℝ) := by positivity
  have hS0 : 0 ≤ radialSmallInverseBarrier p R r := ha.trans hSb.1
  have hS2 : radialSmallInverseBarrier p R r ≤ 2 := by
    have hpa : 10/(p : ℝ) ≤ 1 := (div_le_one hp0).2 hpR
    linarith [hSb.2]
  have hVS : V r*radialSmallInverseBarrier p R r ≤ 1 := by
    have hv := mul_le_mul_of_nonneg_right (hV r hr) hS0
    linarith
  have hqS : 0 ≤ q r*radialSmallInverseBarrier p R r := mul_nonneg (hq r hr) hS0
  have hlap : -deriv (deriv (radialSmallInverseBarrier p R)) r-
      11/r*deriv (radialSmallInverseBarrier p R) r=
      radialSmoothRampDD (1/10000) (r-(R-8/10000))+
        11/r*radialSmoothRampD (1/10000) (r-(R-8/10000)) :=
    radialInverseBarrier_laplacian _ _ _ _ _ (by norm_num)
  have hf := radialSmoothRamp_bounds (1/10000) (by norm_num) (r-(R-8/10000))
  have hprod : 0 ≤ 11/r*radialSmoothRampD (1/10000) (r-(R-8/10000)) :=
    mul_nonneg (div_nonneg (by norm_num) hr.1.le) hf.2.2.1
  unfold radialLinearOperator
  rw [hlap]
  by_cases hc : r ≤ R-7/10000
  · have he : (p : ℝ)/5*(10/(p : ℝ))=2 := by field_simp; ring
    have hbulk := mul_le_mul (hcore r hr hc) hSb.1 ha (hq r hr)
    rw [he] at hbulk
    nlinarith [hf.2.2.2.2.1]
  · have hx : (1/10000 : ℝ) < r-(R-8/10000) := by linarith
    have hDD := (radialSmoothRamp_quadratic (1/10000) _ (by norm_num) hx).2.2
    rw [hDD]
    nlinarith

theorem radial_small_inverse_bound (p : ℕ) (hp : 10 ≤ p) (R M : ℝ)
    (hR : 1 ≤ R) (hR2 : R^2 ≤ 11) (hM : 0 ≤ M) (V q u : ℝ → ℝ)
    (hu : Differentiable ℝ u)
    (hdu : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv u) r)
    (hu0 : deriv u 0=0) (huR : u R=0)
    (hV : ∀ r ∈ Ioo 0 R, V r ≤ (1/2 : ℝ))
    (hq : ∀ r ∈ Ioo 0 R, 0 ≤ q r)
    (hcore : ∀ r ∈ Ioo 0 R, r ≤ R-7/10000 → (p : ℝ)/5 ≤ q r)
    (hLu : ∀ r ∈ Ioo 0 R, |radialLinearOperator V q u r| ≤ M) :
    ∀ r ∈ Icc 0 R, |u r| ≤ M*(10/(p : ℝ)+(8/10000 : ℝ)^2) := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hb : 0 ≤ radialSmallInverseBarrier p R R := by
    change 0 ≤ radialInverseBarrier (1/10000) (R-8/10000) R (10/(p : ℝ)) R
    rw [radialInverseBarrier_boundary]
    positivity
  have h := radialLinearOperator_abs_bound R M (by linarith) hR2 hM V q u
    (radialSmallInverseBarrier p R) hu
    (differentiable_radialInverseBarrier _ _ _ _ (by norm_num)) hdu
    (fun r _ => differentiable_deriv_radialInverseBarrier _ _ _ _ (by norm_num) r)
    hu0 (radialSmallInverseBarrier_origin p R hR) huR hb hV hq hLu
    (radialSmallInverseBarrier_supersolution p hp R V q hV hq hcore)
  intro r hr
  exact (h r hr).trans (mul_le_mul_of_nonneg_left (radialSmallInverseBarrier_bounds p R r hr).2 hM)

end DefocusingNLS

end OAI
