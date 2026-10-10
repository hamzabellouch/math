import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.SeparatedNetParents

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set

def netAncestor {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k : ℕ) : ℕ → E → E
  | 0, x => x
  | t + 1, x => netAncestor N k t ((N (k + t)).parent x)

theorem netAncestor_zero {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k : ℕ) (x : E) : netAncestor N k 0 x = x := rfl

theorem netAncestor_succ {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k t : ℕ) (x : E) :
    netAncestor N k (t + 1) x = netAncestor N k t ((N (k + t)).parent x) := rfl

theorem netAncestor_add {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k u v : ℕ) (x : E) :
    netAncestor N k (u + v) x = netAncestor N k u (netAncestor N (k + u) v x) := by
  induction v generalizing x with
  | zero => rfl
  | succ v ih =>
      rw [Nat.add_succ, netAncestor_succ, netAncestor_succ, ← Nat.add_assoc, ih]

theorem netAncestor_first_parent {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k t : ℕ) (x : E) :
    netAncestor N k (t + 1) x = (N k).parent (netAncestor N (k + 1) t x) := by
  rw [show t + 1 = 1 + t by omega, netAncestor_add]
  rfl

theorem netAncestor_mem {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k t : ℕ) (x : E) :
    (netAncestor N k (t + 1) x : X) ∈ (N k).points := by
  rw [netAncestor_first_parent]
  exact (N k).parent_mem _

theorem netAncestor_self_of_mem {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (hr : ∀ k, 0 < r k)
    (hmono : Monotone (fun k => (N k).points)) (k t : ℕ) (x : E)
    (hx : (x : X) ∈ (N k).points) : netAncestor N k t x = x := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [netAncestor_succ, (N (k + t)).parent_self (hr (k + t)) x
        (hmono (Nat.le_add_right k t) hx), ih]

theorem netAncestor_dist_le_sum {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (hr : ∀ k, 0 < r k)
    (k t : ℕ) (x : E) :
    dist (x : X) (netAncestor N k t x : X) ≤ ∑ j ∈ Finset.range t, r (k + j) := by
  induction t generalizing x with
  | zero => simp only [netAncestor_zero, dist_self, Finset.range_zero, Finset.sum_empty, le_refl]
  | succ t ih =>
      rw [netAncestor_succ, Finset.sum_range_succ]
      have ht := dist_triangle (x : X) ((N (k + t)).parent x : X)
        (netAncestor N k t ((N (k + t)).parent x) : X)
      have hp := (N (k + t)).parent_dist (hr (k + t)) x
      have hi := ih ((N (k + t)).parent x)
      linarith

end

end RieszRectifiability

end OAI
