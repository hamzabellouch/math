import OAI.MeasureTheory.Falconer.Measures.ScalarDensityRadius
import OAI.MeasureTheory.Falconer.Measures.ScalarSubsetMass

namespace OAI

/-! A density interval chosen with half the original Frostman exponent
 retains enough mass even below the rescaled original resolution. -/
namespace Falconer

 theorem scalar_density_relative_mass {R κ K N m : ℝ}
    (hR : 0 < R) (hκ : 0 ≤ κ) (hK : 1 ≤ K) (hN : 0 < N)
    (hmax : N/(2:ℝ)^κ ≤ m/R^κ)
    (hupper : R ≤ 1 → m ≤ K*R^(2*κ)*N) :
    N ≤ (4:ℝ)^κ*K*m := by
  have hr := scalar_density_radius_inequality hR hκ hK hN hmax hupper
  have ht : 0 < (2:ℝ)^κ := by positivity
  have hlow : N*R^κ ≤ (2:ℝ)^κ*m := by
    have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hR κ)).1 hmax
    have hh' := mul_le_mul_of_nonneg_left hh ht.le
    have he : (2:ℝ)^κ*(N/(2:ℝ)^κ*R^κ) = N*R^κ := by field_simp
    nlinarith [he]
  have h1 := mul_le_mul_of_nonneg_right hr hN.le
  have h2 := mul_le_mul_of_nonneg_left hlow
    (mul_nonneg ht.le (show 0 ≤ K by linarith))
  have he : (4:ℝ)^κ = ((2:ℝ)^κ)^2 := by
    rw [show (4:ℝ) = 2*2 by norm_num,Real.mul_rpow (by norm_num) (by norm_num),pow_two]
  rw [he]
  nlinarith

end Falconer

end OAI
