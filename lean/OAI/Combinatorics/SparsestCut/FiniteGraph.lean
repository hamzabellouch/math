import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Positivity

namespace OAI

/-!
# Finite uniform sparsest cut

The rational-capacity objective and its unit-demand denominator follow the introduction of
*Constant-factor hardness of uniform sparsest cut* by OpenAI.
-/

open scoped BigOperators

namespace UniformSparsestCut


/-- An undirected rational-capacity graph.  Zero capacities encode absent edges.
There are no input demand weights: all distinct pairs have demand one. -/
structure Graph where
  n : ℕ
  two_le : 2 ≤ n
  capacity : Fin n → Fin n → ℚ
  nonnegative : ∀ i j, 0 ≤ capacity i j
  symmetric : ∀ i j, capacity i j = capacity j i
  diagonal : ∀ i, capacity i i = 0

/-- Demand is fixed, not chosen by the reduction. -/
def Graph.demand (G : Graph) (i j : Fin G.n) : ℕ := if i = j then 0 else 1

@[simp] theorem Graph.demand_self (G : Graph) (i : Fin G.n) : G.demand i i = 0 := by
  simp [Graph.demand]

theorem Graph.demand_of_ne (G : Graph) {i j : Fin G.n} (h : i ≠ j) :
    G.demand i j = 1 := by
  simp [Graph.demand, h]

/-- A nonempty proper subset of the vertices. -/
def IsCut {n : ℕ} (S : Finset (Fin n)) : Prop := 0 < S.card ∧ S.card < n

instance {n : ℕ} (S : Finset (Fin n)) : Decidable (IsCut S) :=
  inferInstanceAs (Decidable (0 < S.card ∧ S.card < n))

def cuts (n : ℕ) : Finset (Finset (Fin n)) := Finset.univ.filter IsCut

@[simp] theorem mem_cuts {n : ℕ} {S : Finset (Fin n)} : S ∈ cuts n ↔ IsCut S := by
  simp [cuts]

theorem cuts_nonempty (G : Graph) : (cuts G.n).Nonempty := by
  have hn : 0 < G.n := lt_of_lt_of_le (by decide : 0 < 2) G.two_le
  refine ⟨{⟨0, hn⟩}, mem_cuts.mpr ?_⟩
  simpa [IsCut] using (show 0 < 1 ∧ 1 < G.n from ⟨by decide, by have := G.two_le; omega⟩)

/-- Each unordered separated pair occurs once, with its endpoint in `S` first. -/
def Graph.cutCapacity (G : Graph) (S : Finset (Fin G.n)) : ℚ :=
  ∑ i ∈ S, ∑ j ∈ Finset.univ \ S, G.capacity i j

def Graph.cutRatio (G : Graph) (S : Finset (Fin G.n)) : ℚ :=
  G.cutCapacity S / ((S.card : ℚ) * (G.n - S.card : ℕ))

/-- The actual minimum over all nonempty proper cuts, not a relaxation. -/
def Graph.phi (G : Graph) : ℚ :=
  ((cuts G.n).image G.cutRatio).min' ((cuts_nonempty G).image _)

theorem cut_card_le (G : Graph) (S : Finset (Fin G.n)) : S.card ≤ G.n := by
  simpa using Finset.card_le_card (Finset.subset_univ S)

theorem cut_denominator_pos (G : Graph) {S : Finset (Fin G.n)} (hS : IsCut S) :
    (0 : ℚ) < (S.card : ℚ) * (G.n - S.card : ℕ) := by
  exact mul_pos (Nat.cast_pos.mpr hS.1) (Nat.cast_pos.mpr (Nat.sub_pos_of_lt hS.2))

theorem Graph.cutCapacity_nonneg (G : Graph) (S : Finset (Fin G.n)) :
    0 ≤ G.cutCapacity S := by
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => G.nonnegative i j))

theorem Graph.cutRatio_nonneg (G : Graph) (S : Finset (Fin G.n)) :
    0 ≤ G.cutRatio S := by
  exact div_nonneg (G.cutCapacity_nonneg S) (by positivity)

theorem Graph.phi_le_cutRatio (G : Graph) {S : Finset (Fin G.n)} (hS : IsCut S) :
    G.phi ≤ G.cutRatio S := by
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨S, mem_cuts.mpr hS, rfl⟩)

theorem Graph.exists_minimizing_cut (G : Graph) :
    ∃ S : Finset (Fin G.n), IsCut S ∧ G.cutRatio S = G.phi := by
  obtain ⟨S, hS, hv⟩ := Finset.mem_image.mp
    (Finset.min'_mem ((cuts G.n).image G.cutRatio) ((cuts_nonempty G).image _))
  exact ⟨S, mem_cuts.mp hS, hv⟩

theorem Graph.phi_nonneg (G : Graph) : 0 ≤ G.phi := by
  obtain ⟨S, _, hS⟩ := G.exists_minimizing_cut
  rw [← hS]
  exact G.cutRatio_nonneg S

/-- In particular, strict soundness for every cut implies strict soundness for the minimum. -/
theorem Graph.lt_phi_iff (G : Graph) (r : ℚ) :
    r < G.phi ↔ ∀ S : Finset (Fin G.n), IsCut S → r < G.cutRatio S := by
  constructor
  · intro hr S hS
    exact hr.trans_le (G.phi_le_cutRatio hS)
  · intro h
    obtain ⟨S, hS, heq⟩ := G.exists_minimizing_cut
    simpa [heq] using h S hS

/-- Summing the exactly-unit demands gives precisely the denominator in the source. -/
theorem Graph.separated_demand (G : Graph) (S : Finset (Fin G.n)) :
    (∑ i ∈ S, ∑ j ∈ Finset.univ \ S, G.demand i j) = S.card * (G.n - S.card) := by
  have hne (i : Fin G.n) (hi : i ∈ S) (j : Fin G.n) (hj : j ∈ Finset.univ \ S) :
      i ≠ j := by
    intro hij
    exact (Finset.mem_sdiff.mp hj).2 (hij ▸ hi)
  have hc : (Finset.univ \ S).card = G.n - S.card := by
    simp [Finset.card_sdiff]
  calc
    _ = ∑ _i ∈ S, ∑ _j ∈ Finset.univ \ S, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact G.demand_of_ne (hne i hi j hj)
    _ = _ := by simp [hc]

end UniformSparsestCut

end OAI
