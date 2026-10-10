import OAI.Combinatorics.Crossing.FourCycles
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI

namespace Zarankiewicz
open scoped BigOperators

theorem sum_range_cycle_succ {A : Type*} [AddCommGroup A] (f : ℕ → A) (N : ℕ)
    (hN : f N=f 0) : (∑ i ∈ Finset.range N, f (i+1))=∑ i ∈ Finset.range N, f i := by
  apply add_right_cancel (b := f 0)
  calc
    _ = ∑ i ∈ Finset.range (N+1), f i := (Finset.sum_range_succ' f N).symm
    _ = _ := by rw [Finset.sum_range_succ,hN]

theorem double_sum_cycle_shift_right {A B : Type*} (d : ℕ → A) (f : ℕ → B)
    (N K : ℕ) (hK : f K=f 0) (H : A → B → ℝ) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K, H (d i) (f (j+1)))=
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K, H (d i) (f j) := by
  apply Finset.sum_congr rfl
  intro i hi
  exact sum_range_cycle_succ (fun j => H (d i) (f j)) K (congrArg (H (d i)) hK)

theorem double_sum_cycle_shift_left {A B : Type*} (d : ℕ → A) (f : ℕ → B)
    (N K : ℕ) (hN : d N=d 0) (H : A → B → ℝ) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K, H (d (i+1)) (f j))=
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K, H (d i) (f j) :=
  sum_range_cycle_succ (fun i => ∑ j ∈ Finset.range K, H (d i) (f j)) N
    (congrArg (fun a => ∑ j ∈ Finset.range K, H a (f j)) hN)

end Zarankiewicz

end OAI
