import OAI.Geometry.RCD.Heat.GaussianScaleAbsorption
import OAI.Geometry.RCD.Heat.GaussianLinearGrowth

namespace OAI

/-! # A Gaussian second moment is dominated by an integrable exponential -/

namespace RegularPointCoordinates

theorem gaussian_moment_exponential_bound {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      Real.exp (-c*r^2)*r^2 ≤ C*Real.exp (-a*r) := by
  obtain ⟨B,hB,hpoly⟩ := exists_gaussian_polynomial_bound 2 (half_pos hc)
  let C := Real.exp (a^2/(2*c))*B+Real.exp a
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro r hr
  have hrew : Real.exp (-c*r^2)*r^2 =
      (r^2*Real.exp (a*r-c*r^2))*Real.exp (-a*r) := by
    calc
      Real.exp (-c*r^2)*r^2 = r^2*Real.exp (-c*r^2) := mul_comm _ _
      _ = (r^2*Real.exp (a*r-c*r^2))*Real.exp (-a*r) := by
        rw [mul_assoc,← Real.exp_add]
        congr 2
        ring
  rw [hrew]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  by_cases hlarge : 1 ≤ r
  · have hcomp := linear_sub_quadratic_le a r hc
    calc
      r^2*Real.exp (a*r-c*r^2) ≤ r^2*Real.exp (a^2/(2*c)-(c/2)*r^2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hcomp) (sq_nonneg r)
      _ = Real.exp (a^2/(2*c))*(r^2*Real.exp (-(c/2)*r^2)) := by
        rw [sub_eq_add_neg,Real.exp_add]
        ring_nf
      _ ≤ Real.exp (a^2/(2*c))*B :=
        mul_le_mul_of_nonneg_left (hpoly r hlarge) (Real.exp_pos _).le
      _ ≤ C := by
        dsimp only [C]
        linarith [Real.exp_pos a]
  · have hr1 : r ≤ 1 := le_of_not_ge hlarge
    have hp : r^2 ≤ 1 := by nlinarith
    have he : a*r-c*r^2 ≤ a := by
      have hh := mul_le_mul_of_nonneg_left hr1 ha
      nlinarith
    calc
      r^2*Real.exp (a*r-c*r^2) ≤ 1*Real.exp a :=
        mul_le_mul hp (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by norm_num)
      _ ≤ C := by
        dsimp only [C]
        have hnonneg : 0 ≤ Real.exp (a^2/(2*c))*B := by positivity
        linarith

theorem gaussian_density_power_tail {B r u : ℝ} (hB : 0 < B) (hu : 0 ≤ u)
    (hub : u ≤ B*Real.exp (-r^2/40)) (hlog : Real.log B ≤ r^2/80)
    {q : ℕ} (hq : 2 ≤ q) : u^q ≤ Real.exp (-r^2/40) := by
  have hsmall : u ≤ Real.exp (-r^2/80) := by
    apply hub.trans
    calc
      B*Real.exp (-r^2/40) = Real.exp (Real.log B+ -r^2/40) := by
        rw [Real.exp_add,Real.exp_log hB]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hh := pow_le_pow_left₀ hu hsmall q
  rw [← Real.exp_nat_mul] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  have hq' : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hm := mul_le_mul_of_nonpos_right hq' (show -r^2/80 ≤ 0 by nlinarith [sq_nonneg r])
  linarith

end RegularPointCoordinates

end OAI
