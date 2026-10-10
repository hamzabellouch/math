import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeTaylor

namespace OAI

/-! The manuscript's boundary modulus gap follows from the quantitative free Taylor estimate. -/

open Set
namespace DefocusingNLS

theorem radial_free_boundary_gap (b h : ℝ) (z : ℂ)
    (hb : b ∈ Icc (334/1000 : ℝ) (335/1000))
    (hh : h ∈ Icc (1/10000-1/100000000 : ℝ) (1/10000+1/100000000))
    (he : ‖z-1+(b : ℂ)/2*(h : ℂ)^2‖ ≤ (3/2000 : ℝ)*h^2) :
    1-(1/5 : ℝ)*(1/10000)^2 < ‖z‖ ∧
      ‖z‖ < 1-(3/20 : ℝ)*(1/10000)^2 := by
  have hh0 : 0 ≤ h := by linarith [hh.1]
  have hslo : (1/10000-1/100000000 : ℝ)^2 ≤ h^2 :=
    pow_le_pow_left₀ (by norm_num) hh.1 2
  have hshi : h^2 ≤ (1/10000+1/100000000 : ℝ)^2 :=
    pow_le_pow_left₀ hh0 hh.2 2
  have hb0 : 0 ≤ b := by linarith [hb.1]
  have hbhi : b/2*h^2 ≤ (335/2000 : ℝ)*h^2 :=
    mul_le_mul_of_nonneg_right (by linarith [hb.2]) (sq_nonneg h)
  have hblo : (334/2000 : ℝ)*h^2 ≤ b/2*h^2 :=
    mul_le_mul_of_nonneg_right (by linarith [hb.1]) (sq_nonneg h)
  have ht : 0 ≤ 1-b/2*h^2 := by nlinarith
  have heq : z-((1-b/2*h^2 : ℝ) : ℂ)=z-1+(b : ℂ)/2*(h : ℂ)^2 := by
    push_cast
    ring
  have hnorm : ‖((1-b/2*h^2 : ℝ) : ℂ)‖=1-b/2*h^2 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht]
  have hup := norm_sub_norm_le z (((1-b/2*h^2 : ℝ) : ℂ))
  have hlo := norm_sub_norm_le (((1-b/2*h^2 : ℝ) : ℂ)) z
  rw [hnorm,heq] at hup
  rw [hnorm,norm_sub_rev,heq] at hlo
  constructor <;> nlinarith

end DefocusingNLS

end OAI
