import OAI.Combinatorics.GraphThreshold.Statement
import OAI.Combinatorics.GraphThreshold.GraphProbability
import Mathlib.Topology.Order.Monotone
import Mathlib.Tactic

namespace OAI

/-!
# Continuity and attainment of the graph thresholds

Every probability is a literal finite sum of Bernoulli products.  The
admissible parameter sets are closed subsets of `[0,1]`; endpoint feasibility
therefore makes their infima admissible.  No minimizer is postulated.
-/

noncomputable section

open scoped BigOperators

namespace LeanBlast.SecondKahnKalai

theorem continuous_bernoulliWeight {X : Type*} [Fintype X] [DecidableEq X]
    (W : Finset X) : Continuous (fun p : ℝ => bernoulliWeight p W) := by
  unfold bernoulliWeight
  apply continuous_finsetProd
  intro x _
  split_ifs <;> fun_prop

theorem continuous_bernoulliExpectation {X : Type*} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) : Continuous (fun p : ℝ => bernoulliExpectation p f) := by
  unfold bernoulliExpectation
  apply continuous_finsetSum
  intro W _
  exact (continuous_bernoulliWeight W).mul continuous_const

theorem continuous_bernoulliProbability {X : Type*} [Fintype X] [DecidableEq X]
    (P : Finset X → Prop) : Continuous (fun p : ℝ => bernoulliProbability p P) := by
  classical
  unfold bernoulliProbability
  apply continuous_finsetSum
  intro W _
  split_ifs
  · exact continuous_bernoulliWeight W
  · exact continuous_const

theorem continuous_expectedCopies {V : Type*} (n : ℕ) (H : SimpleGraph V) :
    Continuous (fun p : ℝ => expectedCopies n p H) := by
  classical
  exact continuous_bernoulliExpectation _

theorem continuous_containmentProbability {V : Type*} (n : ℕ) (H : SimpleGraph V) :
    Continuous (fun p : ℝ => containmentProbability n p H) := by
  classical
  exact continuous_bernoulliProbability _

theorem isClosed_criticalFeasible {V : Type*} (n : ℕ) (H : SimpleGraph V) :
    IsClosed {p : ℝ | p ∈ Set.Icc 0 1 ∧
      (1 / 2 : ℝ) ≤ containmentProbability n p H} :=
  isClosed_Icc.inter (isClosed_le continuous_const (continuous_containmentProbability n H))

theorem isClosed_expectationFeasible {V : Type*} (n : ℕ) (H : SimpleGraph V) :
    IsClosed {p : ℝ | p ∈ Set.Icc 0 1 ∧
      ∀ F : H.Subgraph, (1 / 2 : ℝ) ≤ expectedCopies n p F.coe} := by
  have hc : IsClosed (⋂ F : H.Subgraph,
      {p : ℝ | (1 / 2 : ℝ) ≤ expectedCopies n p F.coe}) :=
    isClosed_iInter (fun F : H.Subgraph =>
      isClosed_le continuous_const (continuous_expectedCopies n F.coe))
  convert (isClosed_Icc : IsClosed (Set.Icc (0 : ℝ) 1)).inter hc using 1
  ext p
  simp

/-- Endpoint feasibility is enough to ensure that the containment infimum
is attained; its probability need not be assumed monotone for this step. -/
theorem criticalThreshold_attained_of_one {V : Type*} (n : ℕ) (H : SimpleGraph V)
    (hone : (1 / 2 : ℝ) ≤ containmentProbability n 1 H) :
    criticalThreshold n H ∈ Set.Icc 0 1 ∧
      (1 / 2 : ℝ) ≤ containmentProbability n (criticalThreshold n H) H := by
  have hb : BddBelow {p : ℝ | p ∈ Set.Icc 0 1 ∧
      (1 / 2 : ℝ) ≤ containmentProbability n p H} := by
    refine ⟨0, ?_⟩
    intro p hp
    exact hp.1.1
  have hn : Set.Nonempty {p : ℝ | p ∈ Set.Icc 0 1 ∧
      (1 / 2 : ℝ) ≤ containmentProbability n p H} :=
    ⟨1, ⟨by norm_num, hone⟩⟩
  exact (isClosed_criticalFeasible n H).csInf_mem hn hb

/-- All subgraph constraints hold at the expectation infimum.  Arbitrary
intersections of closed constraints suffice, so no enumeration is assumed. -/
theorem expectationThreshold_attained_of_one {V : Type*} (n : ℕ) (H : SimpleGraph V)
    (hone : ∀ F : H.Subgraph, (1 / 2 : ℝ) ≤ expectedCopies n 1 F.coe) :
    expectationThreshold n H ∈ Set.Icc 0 1 ∧
      ∀ F : H.Subgraph, (1 / 2 : ℝ) ≤
        expectedCopies n (expectationThreshold n H) F.coe := by
  have hb : BddBelow {p : ℝ | p ∈ Set.Icc 0 1 ∧
      ∀ F : H.Subgraph, (1 / 2 : ℝ) ≤ expectedCopies n p F.coe} := by
    refine ⟨0, ?_⟩
    intro p hp
    exact hp.1.1
  have hn : Set.Nonempty {p : ℝ | p ∈ Set.Icc 0 1 ∧
      ∀ F : H.Subgraph, (1 / 2 : ℝ) ≤ expectedCopies n p F.coe} :=
    ⟨1, ⟨by norm_num, hone⟩⟩
  exact (isClosed_expectationFeasible n H).csInf_mem hn hb

/-- Any admissible parameter gives an upper bound on the actual critical
threshold. -/
theorem criticalThreshold_le_of_probability {V : Type*} (n : ℕ) (H : SimpleGraph V)
    {p : ℝ} (hp : p ∈ Set.Icc 0 1)
    (hprob : (1 / 2 : ℝ) ≤ containmentProbability n p H) :
    criticalThreshold n H ≤ p := by
  unfold criticalThreshold
  apply csInf_le
  · refine ⟨0, ?_⟩
    intro q hq
    exact hq.1.1
  · exact ⟨hp, hprob⟩

/-- A subgraph whose expectation vanishes at zero forces strict positivity
of the attained expectation threshold. -/
theorem expectationThreshold_pos_of_zero_constraint {V : Type*}
    (n : ℕ) (H : SimpleGraph V)
    (hone : ∀ F : H.Subgraph, (1 / 2 : ℝ) ≤ expectedCopies n 1 F.coe)
    (F : H.Subgraph) (hzero : expectedCopies n 0 F.coe = 0) :
    0 < expectationThreshold n H := by
  have hatt := expectationThreshold_attained_of_one n H hone
  have hne : expectationThreshold n H ≠ 0 := by
    intro hz
    have h := hatt.2 F
    rw [hz, hzero] at h
    norm_num at h
  exact lt_of_le_of_ne hatt.1.1 (Ne.symm hne)

theorem expectationFeasible_one {V : Type*} [Fintype V]
    (n : ℕ) (H : SimpleGraph V) (hcard : Fintype.card V ≤ n)
    (F : H.Subgraph) : (1 / 2 : ℝ) ≤ expectedCopies n 1 F.coe := by
  classical
  have hFcard : Fintype.card F.verts ≤ n :=
    (Fintype.card_le_of_injective (fun v : F.verts => (v : V)) Subtype.val_injective).trans hcard
  exact (by norm_num : (1 / 2 : ℝ) ≤ 1).trans (expectedCopies_one_ge_one n F.coe hFcard)

theorem criticalThreshold_attained {V : Type*} [Fintype V]
    (n : ℕ) (H : SimpleGraph V) (hcard : Fintype.card V ≤ n) :
    criticalThreshold n H ∈ Set.Icc 0 1 ∧
      (1 / 2 : ℝ) ≤ containmentProbability n (criticalThreshold n H) H := by
  apply criticalThreshold_attained_of_one
  rw [containmentProbability_one n H hcard]
  norm_num

/-- Every actual subgraph expectation constraint holds at `p_E`. -/
theorem expectationThreshold_attained {V : Type*} [Fintype V]
    (n : ℕ) (H : SimpleGraph V) (hcard : Fintype.card V ≤ n) :
    expectationThreshold n H ∈ Set.Icc 0 1 ∧
      ∀ F : H.Subgraph, (1 / 2 : ℝ) ≤
        expectedCopies n (expectationThreshold n H) F.coe :=
  expectationThreshold_attained_of_one n H (expectationFeasible_one n H hcard)

theorem criticalThreshold_mem_unitInterval {V : Type*} [Fintype V]
    (n : ℕ) (H : SimpleGraph V) (hcard : Fintype.card V ≤ n) :
    criticalThreshold n H ∈ Set.Icc 0 1 :=
  (criticalThreshold_attained n H hcard).1

theorem expectationThreshold_mem_unitInterval {V : Type*} [Fintype V]
    (n : ℕ) (H : SimpleGraph V) (hcard : Fintype.card V ≤ n) :
    expectationThreshold n H ∈ Set.Icc 0 1 :=
  (expectationThreshold_attained n H hcard).1

/-- Strict positivity follows from the constraint for an actual one-edge
subgraph, whose expected number of copies at parameter zero vanishes. -/
theorem expectationThreshold_pos {V : Type*} [Fintype V]
    (n : ℕ) (H : SimpleGraph V) (hcard : Fintype.card V ≤ n)
    (hedge : 1 ≤ edgeCount H) : 0 < expectationThreshold n H := by
  classical
  have hne : H ≠ ⊥ := by
    intro hz
    have hzero := (edgeCount_eq_zero_iff H).mpr hz
    omega
  obtain ⟨v, w, hvw⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
  let F : H.Subgraph := H.subgraphOfAdj hvw
  let a : F.verts := ⟨v, by simp [F]⟩
  let b : F.verts := ⟨w, by simp [F]⟩
  have hab : F.coe.Adj a b := by
    change s(v, w) = s(v, w)
    rfl
  have hFedge : 1 ≤ edgeCount F.coe := by
    let : Nonempty F.coe.edgeSet := ⟨⟨s(a, b), hab⟩⟩
    exact Nat.card_pos
  exact expectationThreshold_pos_of_zero_constraint n H
    (expectationFeasible_one n H hcard) F (expectedCopies_zero n F.coe hFedge)

theorem expectationThreshold_constraint_self {V : Type*} [Fintype V]
    (n : ℕ) (H : SimpleGraph V) (hcard : Fintype.card V ≤ n) :
    (1 / 2 : ℝ) ≤ expectedCopies n (expectationThreshold n H) H := by
  have h := (expectationThreshold_attained n H hcard).2 (⊤ : H.Subgraph)
  rwa [expectedCopies_iso n _ (SimpleGraph.Subgraph.topIso (G := H))] at h

end LeanBlast.SecondKahnKalai

end

end OAI
