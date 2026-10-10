import OAI.MeasureTheory.Falconer.Graphs.ProductEnergyMaximum

namespace OAI

namespace PlanarFalconer

theorem comparable_profile_factor (N : ℕ) (hN : 0 < N)
    (m : ℝ → ℝ) (a b v lam : ℝ) :
    ((2:ℝ)^(2*(v-a))/(((2:ℝ)^N)^(-m a))^4) *
      ((((2:ℝ)^N)^(-m b))^4*(2:ℝ)^(-2*(v-b))) *
      (4096*((2:ℝ)^N)^(2*(m b-m a)+12*lam)) =
    4096*((2:ℝ)^N)^(-2*(m b-b/N-(m a-a/N))+12*lam) := by
  have hR : 0 < (2:ℝ)^N := by positivity
  have hMa : ((2:ℝ)^N)^(-m a) ≠ 0 := (Real.rpow_pos_of_pos hR _).ne'
  have rearrange :
      ((2:ℝ)^(2*(v-a))/(((2:ℝ)^N)^(-m a))^4) *
        ((((2:ℝ)^N)^(-m b))^4*(2:ℝ)^(-2*(v-b))) *
        (4096*((2:ℝ)^N)^(2*(m b-m a)+12*lam)) =
      4096*((2:ℝ)^(2*(v-a))*(2:ℝ)^(-2*(v-b))) *
        (((2:ℝ)^N)^(-m b)/((2:ℝ)^N)^(-m a))^4 *
        ((2:ℝ)^N)^(2*(m b-m a)+12*lam) := by field_simp
  rw [rearrange,← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  rw [show 2*(v-a)+ -2*(v-b) = 2*(b-a) by ring,two_rpow_as_scale N hN]
  rw [← Real.rpow_sub hR]
  simp only [pow_succ,pow_zero,one_mul]
  have he (x y z : ℝ) : 4096*x*(y*y*y*y)*z = 4096*(x*y*y*y*y*z) := by ring
  rw [he]
  simp only [← Real.rpow_add hR]
  congr 2
  ring

end PlanarFalconer

end OAI
