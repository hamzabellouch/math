import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

namespace OAI

/-! # One dyadic scale for the Euclidean affine improvement -/

open Filter
open scoped Topology

namespace RegularPointCoordinates

/-- A quadratic Taylor error is strictly smaller than the required
three-halves decay at one fixed dyadic scale, independent of the function. -/
theorem exists_dyadic_affine_contraction (C : ℝ) :
    ∃ m : ℕ, 3 ≤ m ∧
      C * ((1 / 2 : ℝ) ^ m) ^ 2 <
        (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ m * Real.sqrt ((1 / 2 : ℝ) ^ m) := by
  have ht : Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hs : Tendsto (fun m : ℕ => C * Real.sqrt ((1 / 2 : ℝ) ^ m)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.sqrt_zero, mul_zero] using
      tendsto_const_nhds.mul (Real.continuous_sqrt.tendsto 0 |>.comp ht)
  obtain ⟨m, hm, hmC⟩ := ((eventually_ge_atTop 3).and
    (hs.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)))).exists
  refine ⟨m, hm, ?_⟩
  have hp : 0 < (1 / 2 : ℝ) ^ m := pow_pos (by norm_num) _
  have hroot : 0 < Real.sqrt ((1 / 2 : ℝ) ^ m) := Real.sqrt_pos.2 hp
  have hsq := Real.sq_sqrt hp.le
  have hh := mul_lt_mul_of_pos_right hmC (mul_pos hp hroot)
  calc
    _ = C * (1 / 2 : ℝ) ^ m * (Real.sqrt ((1 / 2 : ℝ) ^ m)) ^ 2 := by
      rw [hsq]
      ring
    _ = (C * Real.sqrt ((1 / 2 : ℝ) ^ m)) *
        ((1 / 2 : ℝ) ^ m * Real.sqrt ((1 / 2 : ℝ) ^ m)) := by ring
    _ < _ := by simpa only [mul_assoc] using hh

end RegularPointCoordinates

end OAI
