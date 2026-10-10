import OAI.Combinatorics.ContingencyTables.Transport.ResidualAugmentation

namespace OAI

/-!
# The bounded deterministic integral max-flow algorithm

Conditional on the augmentation-count bound, concrete residual searches,
bottlenecks and flow updates preserve feasibility and yield a stopping
certificate.
-/

namespace ContingencyTables.EdmondsKarpAlgorithm

open PublishedEdmondsKarp ResidualAugmentation

variable {n : ℕ}

def advance (c : Capacity n) (s t : Fin n) (f : Flow n) : Flow n :=
  (step c s t f).getD f

def run (c : Capacity n) (s t : Fin n) : ℕ → Flow n
  | 0 => 0
  | k+1 => advance c s t (run c s t k)

def maxFlow (c : Capacity n) (s t : Fin n) : Flow n := run c s t (n^3+1)

lemma zero_feasible (c : Capacity n) (s t : Fin n) : Feasible c s t 0 := by
  refine ⟨?_,?_,?_⟩
  · intro u v; simp
  · intro u v
    change (0:ℤ)≤(c u v:ℤ)
    exact_mod_cast Nat.zero_le (c u v)
  · intro u _ _; simp

lemma run_feasible (c : Capacity n) (s t : Fin n) (hst : s≠t) (k : ℕ) :
    Feasible c s t (run c s t k) := by
  induction k with
  | zero => exact zero_feasible c s t
  | succ k ih =>
    cases hs : step c s t (run c s t k) with
    | none => simpa only [run,advance,hs,Option.getD_none] using ih
    | some g =>
      simpa only [run,advance,hs,Option.getD_some] using
        step_feasible c s t hst (run c s t k) g ih hs

lemma run_step (c : Capacity n) (s t : Fin n) (k : ℕ) (g : Flow n)
    (h : step c s t (run c s t k)=some g) : run c s t (k+1)=g := by
  simp only [run,advance,h,Option.getD_some]

lemma run_stops (c : Capacity n) (s t : Fin n) (k : ℕ)
    (h : step c s t (run c s t k)=none) (j : ℕ) :
    run c s t (k+j)=run c s t k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.add_succ,run,ih,advance,h,Option.getD_none]

theorem termination (hEK : EdmondsKarp1972Theorem1)
    (c : Capacity n) (hc : ∀ u,c u u=0) (s t : Fin n) (hst : s≠t) :
    ∃ i≤n^3,step c s t (run c s t i)=none := by
  by_contra hn
  have hsome : ∀ i≤n^3,∃ g,step c s t (run c s t i)=some g := by
    intro i hi
    cases hs : step c s t (run c s t i) with
    | none => exact False.elim (hn ⟨i,hi,hs⟩)
    | some g => exact ⟨g,rfl⟩
  let F : Fin (n^3+2) → Flow n := fun i=>run c s t i.val
  have hF : AugmentationTrace c s t F := by
    refine ⟨rfl,?_,?_⟩
    · intro i
      exact run_feasible c s t hst i.val
    · intro i
      obtain ⟨g,hg⟩ := hsome i.val (by have hi:=i.isLt; omega)
      have he : F i.succ=g := run_step c s t i.val g hg
      rw [he]
      exact step_augmentation c s t hst (F i.castSucc) g hg
  exact no_long_trace hEK c hc s t hst F hF

theorem maxFlow_correct (hEK : EdmondsKarp1972Theorem1)
    (c : Capacity n) (hc : ∀ u,c u u=0) (s t : Fin n) (hst : s≠t) :
    IsMaximum c s t (maxFlow c s t) := by
  obtain ⟨i,hi,hs⟩ := termination hEK c hc s t hst
  have hstop := run_stops c s t i hs (n^3+1-i)
  have he : i+(n^3+1-i)=n^3+1 := by omega
  rw [he] at hstop
  unfold maxFlow
  rw [hstop]
  exact step_none_maximum c s t (run c s t i) (run_feasible c s t hst i) hs

end ContingencyTables.EdmondsKarpAlgorithm

end OAI
