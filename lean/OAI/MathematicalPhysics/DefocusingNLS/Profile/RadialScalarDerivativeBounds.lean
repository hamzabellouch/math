import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialVelocityBounds

namespace OAI

/-! Uniform first and second derivative bounds from the exact radial integral equation. -/

open Set
namespace DefocusingNLS

theorem radial_scalar_forcing_bound (p : ℕ) (hp : 1 ≤ p) (R : ℝ) (A V : ℝ → ℝ)
    (hA : ∀ r ∈ Icc 0 R, A r ∈ Icc 0 1)
    (hP : ∀ r ∈ Icc 0 R, (A r)^(p-1) ≤ (1/2 : ℝ))
    (hV : ∀ r ∈ Icc 0 R, V r ∈ Icc (3/10 : ℝ) (1/2)) :
    ∀ r ∈ Icc 0 R, ‖(A r)^p-V r*A r‖ ≤ (1/2 : ℝ) := by
  intro r hr
  have ha := hA r hr
  have hpw := hP r hr
  have hv := hV r hr
  have he : (A r)^p=(A r)^(p-1)*A r := by
    rw [← pow_succ]
    congr 1
    omega
  rw [he,Real.norm_eq_abs]
  have hPn := pow_nonneg ha.1 (p-1)
  have hPV := mul_le_mul_of_nonneg_right hpw ha.1
  have hVV := mul_le_mul_of_nonneg_right hv.2 ha.1
  have hPA := mul_nonneg hPn ha.1
  have hVA := mul_nonneg (le_trans (by norm_num) hv.1) ha.1
  exact abs_le.2 ⟨by nlinarith [ha.2],by nlinarith [ha.2]⟩

theorem radial_scalar_first_derivative_bound (p : ℕ) (hp : 1 ≤ p) (R : ℝ) (A V : ℝ → ℝ)
    (hA : ∀ r ∈ Icc 0 R, A r ∈ Icc 0 1)
    (hP : ∀ r ∈ Icc 0 R, (A r)^(p-1) ≤ (1/2 : ℝ))
    (hV : ∀ r ∈ Icc 0 R, V r ∈ Icc (3/10 : ℝ) (1/2))
    (hInt : ∀ r ∈ Icc 0 R, deriv A r=r*radialAverage (fun t => (A t)^p-V t*A t) r) :
    ∀ r ∈ Icc 0 R, ‖deriv A r‖ ≤ r/24 := by
  intro r hr
  rw [hInt r hr,norm_mul,Real.norm_eq_abs,abs_of_nonneg hr.1]
  have h := radialAverage_norm_le (fun t => (A t)^p-V t*A t) R (1/2) r hr.1 hr.2
    (radial_scalar_forcing_bound p hp R A V hA hP hV)
  calc
    r*‖radialAverage (fun t => (A t)^p-V t*A t) r‖ ≤ r*((1/2)/12) :=
      mul_le_mul_of_nonneg_left h hr.1
    _ = r/24 := by ring

theorem radial_scalar_second_derivative_bound (p : ℕ) (hp : 1 ≤ p) (R : ℝ) (A V : ℝ → ℝ)
    (hA : ∀ r ∈ Icc 0 R, A r ∈ Icc 0 1)
    (hP : ∀ r ∈ Icc 0 R, (A r)^(p-1) ≤ (1/2 : ℝ))
    (hV : ∀ r ∈ Icc 0 R, V r ∈ Icc (3/10 : ℝ) (1/2))
    (hInt : ∀ r ∈ Icc 0 R, deriv A r=r*radialAverage (fun t => (A t)^p-V t*A t) r)
    (hEq : ∀ r ∈ Ioo 0 R,
      -deriv (deriv A) r-11/r*deriv A r+(A r)^p=V r*A r) :
    ∀ r ∈ Ioo 0 R, ‖deriv (deriv A) r‖ ≤ (23/24 : ℝ) := by
  intro r hr
  have hrC : r ∈ Icc 0 R := ⟨hr.1.le,hr.2.le⟩
  have hF := radial_scalar_forcing_bound p hp R A V hA hP hV r hrC
  have hD := radial_scalar_first_derivative_bound p hp R A V hA hP hV hInt r hrC
  have hden : ‖11/r*deriv A r‖ ≤ (11/24 : ℝ) := by
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (by norm_num) hr.1.le)]
    calc
      11/r*‖deriv A r‖ ≤ 11/r*(r/24) := mul_le_mul_of_nonneg_left hD (div_nonneg (by norm_num) hr.1.le)
      _ = 11/24 := by field_simp [hr.1.ne']
  have he : deriv (deriv A) r=((A r)^p-V r*A r)-11/r*deriv A r := by linarith [hEq r hr]
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

end DefocusingNLS

end OAI
