import OAI.Probability.ContinuumTransition.UpperComparison

namespace OAI

section
open scoped Topology BigOperators
open Filter
namespace ContinuumTemperature

theorem kacRowError_sq_tendsto (C : NNReal) :
    Tendsto (fun u : ℝ => kacRowError C (u^2) u) atTop (𝓝 0) := by
  have hi : Tendsto (fun u : ℝ => u⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hh := (hi.const_mul (48*(C : ℝ))).mul (((tendsto_const_nhds (x := (1 : ℝ))).add (hi.const_mul 6)).pow 3)
  have hh' : Tendsto (fun u : ℝ => 48*(C : ℝ)*u⁻¹*(1+6*u⁻¹)^3) atTop (𝓝 0) := by
    simpa using hh
  apply hh'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  unfold kacRowError
  field_simp
  ring

theorem grid_card_ratio_tendsto {q : ℕ} (hq : 0 < q) :
    Tendsto (fun m : ℕ => ((gridIndices m 1).card : ℝ)/((m : ℝ)*(q : ℝ)/2)^3)
      atTop (𝓝 (1/((q : ℝ)/4)^3)) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hi : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hh := (((tendsto_const_nhds (x := (2 : ℝ))).add hi).pow 3).div_const (((q : ℝ)/2)^3)
  have hh' : Tendsto (fun m : ℕ => (2+(m : ℝ)⁻¹)^3/((q : ℝ)/2)^3)
      atTop (𝓝 (1/((q : ℝ)/4)^3)) := by
    convert hh using 1
    norm_num
    field_simp
    ring
  apply hh'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [card_gridIndices]
  push_cast
  field_simp

theorem boundary_polynomial_ratio_tendsto {q : ℕ} (hq : 0 < q) (H : ℕ) :
    Tendsto (fun m : ℕ => (3*((2*(m : ℝ)+1)*(2*(H : ℝ)))*(2*(m : ℝ)*(q : ℝ)+1)^2)/
      ((m : ℝ)*(q : ℝ)/2)^3) atTop (𝓝 (384*(H : ℝ)/(q : ℝ))) := by
  have hi : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hh := ((((tendsto_const_nhds (x := (2 : ℝ))).add hi).const_mul (3*(2*(H : ℝ)))).mul
    (((tendsto_const_nhds (x := 2*(q : ℝ))).add hi).pow 2)).div_const (((q : ℝ)/2)^3)
  have hh' : Tendsto (fun m : ℕ => (3*(2*(H : ℝ))*(2+(m : ℝ)⁻¹)*(2*(q : ℝ)+(m : ℝ)⁻¹)^2)/
      ((q : ℝ)/2)^3) atTop (𝓝 (384*(H : ℝ)/(q : ℝ))) := by
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
    convert hh using 1
    norm_num
    field_simp
    ring
  apply hh'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  field_simp

end ContinuumTemperature
end

end OAI
