import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace OAI

/-!
# Shortest-augmenting-path bound

The finite integral-network specialization of Edmonds and Karp,
*Theoretical Improvements in Algorithmic Efficiency for Network Flow
Problems*, J. ACM 19(2) (1972), 248–264, Theorem 1 (printed page 251).
The bound (n³−n)/4 implies the n³ bound for shortest residual augmentations.

Primary text:
https://web.eecs.umich.edu/~pettie/matching/Edmonds-Karp-network-flow.pdf
-/

namespace ContingencyTables.PublishedEdmondsKarp

open scoped BigOperators

abbrev Flow (n : ℕ) := Fin n → Fin n → ℤ
abbrev Capacity (n : ℕ) := Fin n → Fin n → ℕ

/-- Skew flows combine the two antiparallel directions. The upper
capacity bound and skew symmetry give both directed residual bounds. -/
def Feasible {n : ℕ} (c : Capacity n) (s t : Fin n) (f : Flow n) : Prop :=
  (∀ u v, f u v= -f v u) ∧
  (∀ u v, f u v≤c u v) ∧
  (∀ u, u≠s → u≠t → (∑ v, f u v)=0)

def value {n : ℕ} (s : Fin n) (f : Flow n) : ℤ := ∑ v, f s v

def IsMaximum {n : ℕ} (c : Capacity n) (s t : Fin n) (f : Flow n) : Prop :=
  Feasible c s t f ∧ ∀ g, Feasible c s t g → value s g≤value s f

/-- A directed residual path with k arcs and no repeated vertices. -/
def ResidualPath {n : ℕ} (c : Capacity n) (f : Flow n) (s t : Fin n)
    (k : ℕ) (p : Fin (k+1) → Fin n) : Prop :=
  p 0=s ∧ p (Fin.last k)=t ∧ Function.Injective p ∧
  ∀ i : Fin k, 0<(c (p i.castSucc) (p i.succ):ℤ)-f (p i.castSucc) (p i.succ)

/-- An actual saturating augmentation along a shortest residual path.
The bottleneck is positive, bounded by every residual capacity, and
attained by an arc. The displayed update adds it forward and subtracts
it backward on precisely the traversed arcs. -/
def ShortestAugmentation {n : ℕ} (c : Capacity n) (s t : Fin n)
    (f g : Flow n) : Prop :=
  ∃ (k : ℕ) (p : Fin (k+1) → Fin n) (a : ℤ),
    ResidualPath c f s t k p ∧
    (∀ (l : ℕ) (q : Fin (l+1) → Fin n), ResidualPath c f s t l q → k≤l) ∧
    0<a ∧
    (∀ i : Fin k, a≤(c (p i.castSucc) (p i.succ):ℤ)-f (p i.castSucc) (p i.succ)) ∧
    (∃ i : Fin k, a=(c (p i.castSucc) (p i.succ):ℤ)-f (p i.castSucc) (p i.succ)) ∧
    ∀ u v, g u v=f u v+a*((∑ i : Fin k,
      if p i.castSucc=u ∧ p i.succ=v then (1:ℤ) else 0)-
      (∑ i : Fin k, if p i.castSucc=v ∧ p i.succ=u then (1:ℤ) else 0))

/-- A finite initial segment of an actual shortest-augmentation
execution. It need not already have reached a maximum flow. -/
def AugmentationTrace {n K : ℕ} (c : Capacity n) (s t : Fin n)
    (F : Fin (K+1) → Flow n) : Prop :=
  F 0=0 ∧
  (∀ i, Feasible c s t (F i)) ∧
  ∀ i : Fin K, ShortestAugmentation c s t (F i.castSucc) (F i.succ)

/-- The shortest-augmenting-path bound for integral skew flows.
Every finite initial segment has at most n³ augmentations, independently
of the rule used to break ties between shortest paths. -/
def EdmondsKarp1972Theorem1 : Prop :=
  ∀ (n : ℕ) (c : Capacity n), (∀ u, c u u=0) →
    ∀ (s t : Fin n), s≠t →
      ∀ (K : ℕ) (F : Fin (K+1) → Flow n),
        AugmentationTrace c s t F → K≤n^3

theorem no_long_trace (hEK : EdmondsKarp1972Theorem1)
    {n : ℕ} (c : Capacity n) (hc : ∀ u, c u u=0)
    (s t : Fin n) (hst : s≠t) (F : Fin (n^3+2) → Flow n) :
    ¬AugmentationTrace c s t F := by
  intro hF
  have h := hEK n c hc s t hst (n^3+1) F hF
  exact Nat.not_succ_le_self _ h

end ContingencyTables.PublishedEdmondsKarp

end OAI
