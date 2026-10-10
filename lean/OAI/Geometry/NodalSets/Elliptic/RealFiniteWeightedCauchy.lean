import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.Real.Lemmas

namespace OAI

namespace Yau.Geometry
open Filter
open scoped Topology

theorem real_finite_weighted_cauchy {I : Type*} [Fintype I]
    (a : ℕ → I → ℝ) (f w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (ha : ∀ i, Tendsto (fun j ↦ a j i) atTop (𝓝 (f i))) :
    ∀ eps > 0, ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      (∑ k, w k*(a i k-a j k)^2) < eps := by
  classical
  let S : ℕ → ℝ := fun j ↦ ∑ k, w k*(a j k-f k)^2
  have ht : Tendsto S atTop (𝓝 0) := by
    have h : Tendsto S atTop (𝓝 (∑ k, w k*(f k-f k)^2)) :=
      tendsto_finsetSum (Finset.univ : Finset I) (fun k _ ↦
      tendsto_const_nhds.mul (((ha k).sub tendsto_const_nhds).pow 2))
    simpa only [sub_self,zero_pow (by decide : 2≠0),mul_zero,Finset.sum_const_zero] using h
  intro eps heps
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually_lt_const (show 0 < eps/4 by linarith))
  refine ⟨N,fun i hi j hj ↦ ?_⟩
  have hb : (∑ k, w k*(a i k-a j k)^2) ≤ 2*(S i+S j) := by
    dsimp [S]
    rw [← Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    have hsq : (a i k-a j k)^2 ≤ 2*((a i k-f k)^2+(a j k-f k)^2) := by
      nlinarith [sq_nonneg (a i k+a j k-2*f k)]
    calc
      _ ≤ w k*(2*((a i k-f k)^2+(a j k-f k)^2)) := mul_le_mul_of_nonneg_left hsq (hw k)
      _ = _ := by ring
  exact hb.trans_lt (by linarith [hN i hi,hN j hj])

end Yau.Geometry

end OAI
