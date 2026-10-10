import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.TriangleDrift
import OAI.Combinatorics.TriangleRemoval.Process.History

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem historyLaw_path_support {α : Type*} (initial : PMF α)
    (K : ℕ → α → PMF α) (T k : ℕ) (hk : k ≤ T)
    (ω : History α T) (hω : ω ∈ (historyLaw initial K T k).support) :
    ω (historyIndex T 0) ∈ initial.support ∧
      ∀ j < k, ω (historyIndex T (j+1)) ∈ (K j (ω (historyIndex T j))).support := by
  induction k generalizing ω with
  | zero =>
    obtain ⟨a,ha,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hω
    exact ⟨ha,fun _ h => (Nat.not_lt_zero _ h).elim⟩
  | succ k ih =>
    have hkt : k < T := by omega
    obtain ⟨π,hπ,hω⟩ := (PMF.mem_support_bind_iff _ _ _).mp hω
    rw [historyKernel,ite_eq_left hkt] at hω
    obtain ⟨b,hb,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hω
    obtain ⟨hinit,hpath⟩ := ih (by omega) π hπ
    constructor
    · rw [Function.update_of_ne (historyIndex_ne_succ (Nat.zero_le k) hkt)]
      exact hinit
    · intro j hj
      by_cases he : j = k
      · subst j
        rw [Function.update_self,
          Function.update_of_ne (historyIndex_ne_succ le_rfl hkt)]
        exact hb
      · have hjk : j < k := by omega
        rw [Function.update_of_ne (historyIndex_ne_succ (by omega : j+1 ≤ k) hkt),
          Function.update_of_ne (historyIndex_ne_succ hjk.le hkt)]
        exact hpath j hjk

theorem copyCount_nonneg {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) : 0 ≤ copyCount required G := by
  apply Finset.sum_nonneg
  intro a _
  unfold intact
  split <;> norm_num

theorem historyNoise_succ_same {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : ℕ → α → ℝ)
    (T j : ℕ) (hj : j < T) (ω : History α T) :
    historyNoise K f T (j+1) ω =
      historyNoise K f T j ω + historyIncrement K f T j ω := by
  simp only [historyNoise,Nat.min_eq_left (by omega : j+1 ≤ T),
    Nat.min_eq_left hj.le,Finset.sum_range_succ]

end SharpTerminalLeave

end

end OAI
