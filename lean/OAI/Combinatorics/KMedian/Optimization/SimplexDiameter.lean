import Mathlib
import OAI.Combinatorics.KMedian.Optimization.ProjectedSubgradient

namespace OAI

section
section
namespace MetricKMedian.ProjectedSubgradient
open Finset
variable {n : ℕ}

theorem diameter_sq (k : ℚ) (x y : Fin n → ℚ)
    (hx : feasible k x) (hy : feasible k y) : sqdist x y ≤ 2*k^2 := by
  have hxx := sum_sq_le_sq_sum_of_nonneg (s:=(univ:Finset (Fin n))) (fun i _ => hx.1 i)
  have hyy := sum_sq_le_sq_sum_of_nonneg (s:=(univ:Finset (Fin n))) (fun i _ => hy.1 i)
  rw [hx.2] at hxx
  rw [hy.2] at hyy
  have hper : ∀ i, (x i-y i)^2 ≤ (x i)^2+(y i)^2 := by
    intro i
    nlinarith [mul_nonneg (hx.1 i) (hy.1 i)]
  have hh := sum_le_sum (fun i (_ : i ∈ (univ:Finset (Fin n))) => hper i)
  rw [sum_add_distrib] at hh
  unfold sqdist
  linarith

def initial [NeZero n] (k : ℚ) : Vector ℚ n := Vector.ofFn (fun i => if i=0 then k else 0)

theorem initial_feasible [NeZero n] (k : ℚ) (hk : 0 ≤ k) : feasible k (point (initial (n:=n) k)) := by
  simp only [initial,point_ofFn]
  constructor
  · intro i
    dsimp only
    split_ifs
    · exact hk
    · exact le_rfl
  · rw [sum_ite_eq',ite_eq_left (mem_univ _)]

end MetricKMedian.ProjectedSubgradient
end
end

end OAI
