import OAI.Probability.ContinuumTransition.LowerComparison

namespace OAI

section
open scoped Topology BigOperators
open Filter
namespace ContinuumTemperature

theorem grid_card_outer_ratio_tendsto {u : ℝ} (hu : 0 < u) (K N : ℕ) :
    Tendsto (fun m : ℕ => ((gridIndices (m+K) 1).card : ℝ)/(2*((m+N : ℕ)+1)*u)^3)
      atTop (𝓝 (1/u^3)) := by
  have hi : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hn := ((hi.const_mul (2*(K : ℝ)+1)).const_add 2).pow 3
  have hd := (((hi.const_mul ((N : ℝ)+1)).const_add 1).const_mul (2*u)).pow 3
  have hz : (2*u*(1+((N : ℝ)+1)*0))^3 ≠ 0 := by positivity
  have hh := hn.div hd hz
  have hh' : Tendsto (fun m : ℕ => (2+(2*(K : ℝ)+1)*(m : ℝ)⁻¹)^3/
      (2*u*(1+((N : ℝ)+1)*(m : ℝ)⁻¹))^3) atTop (𝓝 (1/u^3)) := by
    have he : (2 : ℝ)^3/(2*u)^3 = 1/u^3 := by
      field_simp
    simpa only [Pi.div_def, mul_zero, add_zero, mul_one, he] using hh
  apply hh'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hmn : (m : ℝ)+(N : ℝ)+1 ≠ 0 := by positivity
  rw [card_gridIndices]
  push_cast
  field_simp
  ring

end ContinuumTemperature
end

end OAI
