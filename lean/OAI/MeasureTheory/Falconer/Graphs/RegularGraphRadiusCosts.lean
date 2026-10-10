import OAI.MeasureTheory.Falconer.Graphs.RegularGraphCosts

namespace OAI

/-! The fixed graph loss is polynomial in the coordinate ratio radius. -/
namespace Falconer

 theorem regular_graph_radius_cost {R : ℝ} (hR : 1 ≤ R) (M : ℕ) (hM : (M:ℝ) ≤ R) :
    regularGraphCost M ≤ 1048576*R^4 := by
  have hM0 : 0 ≤ (M:ℝ) := Nat.cast_nonneg _
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hm2 : (M:ℝ)^2 ≤ R^2 := pow_le_pow_left₀ hM0 hM 2
  have hr2 : 1 ≤ R^2 := one_le_pow₀ hR
  have hr4 : 1 ≤ R^4 := one_le_pow₀ hR
  have hr24 : R^2 ≤ R^4 := pow_le_pow_right₀ hR (by omega)
  have hl : 2*(M:ℝ)+3 ≤ 5*R := by linarith
  have hlsq : (2*(M:ℝ)+3)^2 ≤ 25*R^2 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 2*(M:ℝ)+3) hl 2
    nlinarith
  have hb : (1+4*(M:ℝ))^2 ≤ 25*R^2 := by
    have hl' : 1+4*(M:ℝ) ≤ 5*R := by linarith
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1+4*(M:ℝ)) hl' 2
    nlinarith
  have ht : 2*(M:ℝ)^2+3 ≤ 5*R^2 := by nlinarith
  have hp : (2*(M:ℝ)^2+3)*(2*(M:ℝ)+3)^2 ≤ 125*R^4 := by
    have hh := mul_le_mul ht hlsq (sq_nonneg _) (by positivity : 0 ≤ 5*R^2)
    nlinarith
  unfold regularGraphCost
  nlinarith

end Falconer

end OAI
