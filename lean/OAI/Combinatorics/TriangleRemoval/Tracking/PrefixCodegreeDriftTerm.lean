import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.CenteredCodegreeNeighborSum
import OAI.Combinatorics.TriangleRemoval.Process.CommonNeighborsComplete

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

theorem complete_history_valid {n T : ℕ}
    (ω : History (Graph n) T)
    (hω : ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) T T).support) :
    ∀ j ≤ T, ω (historyIndex T j) ⊆ completeGraph n := by
  obtain ⟨hi,hp⟩ := historyLaw_path_support (PMF.pure (completeGraph n))
    (fun _ => step) T T le_rfl ω hω
  have hi' : ω (historyIndex T 0) = completeGraph n := by
    simpa only [PMF.mem_support_pure_iff] using hi
  intro j
  induction j with
  | zero =>
    intro _
    rw [hi']
  | succ j ih =>
    intro hj
    exact (step_support_subset (hp j (Nat.lt_of_succ_le hj))).trans
      (ih (Nat.le_of_succ_le hj))

noncomputable def prefixCodegreeDriftTerm {n : ℕ} (u v : Fin n)
    (k : ℕ) (G : Graph n) : ℝ :=
  (currentCodegree G u v : ℝ)*(1/earlyTemplateScale 1 2 n (k+1)-1/earlyTemplateScale 1 2 n k)-
    ((2*earlyTemplateScale 1 2 n k-if {u,v} ∈ G then 1 else 0)*
      (currentCodegree G u v : ℝ)+
      centeredCodegreeNeighborSum G u v (earlyTemplateScale 1 2 n k))/
    ((triangles G).card*earlyTemplateScale 1 2 n (k+1))

theorem codegree_predictable_error_explicit {n : ℕ} (hn : 2 ≤ n)
    (u v : Fin n) (huv : u ≠ v)
    (ω : History (Graph n) (prefixTime n))
    (hω : ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step)
      (prefixTime n) (prefixTime n)).support)
    (j : ℕ) (hj : j ≤ prefixTime n) :
    prefixCodegreePredictableError u v j ω = -1/((n : ℝ)-1)^2+
      ∑ k ∈ Finset.range j,
        prefixCodegreeDriftTerm u v k (ω (historyIndex (prefixTime n) k)) := by
  obtain ⟨hi,_⟩ := historyLaw_path_support (PMF.pure (completeGraph n))
    (fun _ => step) (prefixTime n) (prefixTime n) le_rfl ω hω
  have hi' : ω (historyIndex (prefixTime n) 0) = completeGraph n := by
    simpa only [PMF.mem_support_pure_iff] using hi
  unfold prefixCodegreePredictableError
  rw [hi']
  change ((currentCodegree (completeGraph n) u v : ℝ)/earlyTemplateScale 1 2 n 0-1)+_ = _
  rw [initial_normalized_codegree_error hn u v huv]
  congr 1
  unfold historyCompensator historyCounter
  rw [Nat.min_eq_left hj]
  apply Finset.sum_congr rfl
  intro k hk
  exact prefix_codegree_centered_drift
    (complete_history_valid ω hω k ((Finset.mem_range.mp hk).le.trans hj)) u v huv k

end SharpTerminalLeave
end

end OAI
