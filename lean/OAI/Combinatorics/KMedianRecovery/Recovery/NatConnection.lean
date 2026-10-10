import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.SmallSubsets

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [DecidableEq V]

def natConnection (δ : V → V → ℕ) (S : Finset V) (p : V) : ℕ :=
  if h : S.Nonempty then S.inf' h (δ p) else 0

def natCost (δ : V → V → ℕ) (D S : Finset V) : ℕ := ∑ p ∈ D, natConnection δ S p

variable [PseudoMetricSpace V]

omit [DecidableEq V] in
lemma natConnection_cast (δ : V → V → ℕ) (F S : Finset V) (p : V)
    (hSF : S ⊆ F) (hδ : ∀ i ∈ F, (δ p i : ℝ) = dist p i) :
    (natConnection δ S p : ℝ) = connection S p := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨i,hi,heq⟩ := Finset.exists_mem_eq_inf' hS (δ p)
    have hmin : ∀ j ∈ S, δ p i ≤ δ p j := by
      intro j hj
      rw [←heq]
      exact Finset.inf'_le _ hj
    simp only [natConnection,connection,dite_eq_left hS]
    rw [heq,hδ i (hSF hi)]
    apply le_antisymm
    · apply Finset.le_inf' hS _
      intro j hj
      have hh : (δ p i : ℝ) ≤ (δ p j : ℝ) := by exact_mod_cast hmin j hj
      simpa only [hδ i (hSF hi),hδ j (hSF hj)] using hh
    · exact Finset.inf'_le _ hi
  · simp only [natConnection,connection,dite_eq_right hS,Nat.cast_zero]

omit [DecidableEq V] in
lemma natCost_cast (δ : V → V → ℕ) (F D S : Finset V) (hSF : S ⊆ F)
    (hδ : ∀ p ∈ D, ∀ i ∈ F, (δ p i : ℝ) = dist p i) :
    (natCost δ D S : ℝ) = cost D S := by
  unfold natCost cost
  push_cast
  exact Finset.sum_congr rfl (fun p hp => natConnection_cast δ F S p hSF (hδ p hp))

omit [PseudoMetricSpace V] [DecidableEq V] in
lemma natCost_le (δ : V → V → ℕ) (F D S : Finset V) (hSF : S ⊆ F)
    (M : ℕ) (hM : ∀ p ∈ D, ∀ i ∈ F, δ p i ≤ M) : natCost δ D S ≤ D.card*M := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨i,hi⟩ := hS
    have hS : S.Nonempty := ⟨i,hi⟩
    calc
      _ ≤ ∑ _p ∈ D, M := by
        apply Finset.sum_le_sum
        intro p hp
        simp only [natConnection,dite_eq_left hS]
        exact (Finset.inf'_le _ hi).trans (hM p hp i (hSF hi))
      _ = _ := by simp
  · simp [natCost,natConnection,hS]

theorem integral_bounded_descent (δ : V → V → ℕ) (F D S : Finset V)
    (w M : ℕ) (hSF : S ⊆ F)
    (hδ : ∀ p ∈ D, ∀ i ∈ F, (δ p i : ℝ) = dist p i)
    (hM : ∀ p ∈ D, ∀ i ∈ F, δ p i ≤ M) :
    ∃ n ≤ D.card*M, ∃ path : ℕ → Finset V,
      path 0 = S ∧ (∀ j < n, path (j+1) ∈ exchangeCandidates F (path j) w) ∧
      path n ⊆ F ∧ (path n).card = S.card ∧ cost D (path n) ≤ cost D S ∧
      WidthLocalMin F D (path n) w := by
  obtain ⟨n,hn,path,hzero,hsteps,hend,hcard,hcost,hlocal⟩ :=
    bounded_descent F S (natCost δ D) w hSF
  refine ⟨n,hn.trans (natCost_le δ F D S hSF M hM),path,hzero,hsteps,hend,hcard,?_,?_⟩
  · rw [←natCost_cast δ F D (path n) hend hδ,←natCost_cast δ F D S hSF hδ]
    exact_mod_cast hcost
  · intro T hTF hTcard hrem hadd
    rw [←natCost_cast δ F D (path n) hend hδ,←natCost_cast δ F D T hTF hδ]
    exact_mod_cast hlocal T (candidate_of_exchange F (path n) T w hTF hTcard hrem hadd)

end MetricKMedianRecovery.LocalSearch

end OAI
