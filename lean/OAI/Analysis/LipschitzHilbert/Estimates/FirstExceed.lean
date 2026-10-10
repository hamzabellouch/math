import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Nat.Find

namespace OAI

/-! Disjoint first-crossing events for a finite scalar process. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

def firstExceed {X : Type*} (U : ℕ → X → ℝ) (lambda : ℝ) (n : ℕ) : Set X :=
  {x | lambda < U n x ∧ ∀ i < n, U i x ≤ lambda}

def finiteMaxEvent {X : Type*} (U : ℕ → X → ℝ) (lambda : ℝ) (N : ℕ) : Set X :=
  {x | ∃ i ≤ N, lambda < U i x}

theorem firstExceed_disjoint {X : Type*} (U : ℕ → X → ℝ) (lambda : ℝ) :
    Pairwise (fun i j => Disjoint (firstExceed U lambda i) (firstExceed U lambda j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · exact (not_lt_of_ge (hxj.2 i h)) hxi.1
  · exact (not_lt_of_ge (hxi.2 j h)) hxj.1

theorem firstExceed_union {X : Type*} (U : ℕ → X → ℝ) (lambda : ℝ) (N : ℕ) :
    (⋃ i : Fin (N + 1), firstExceed U lambda i.val) = finiteMaxEvent U lambda N := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact ⟨i, by omega, hi.1⟩
  · rintro ⟨i, hi, hUi⟩
    have hex : ∃ n, lambda < U n x := ⟨i,hUi⟩
    let n := Nat.find hex
    have hn : n ≤ i := Nat.find_min' hex hUi
    apply mem_iUnion.mpr
    refine ⟨⟨n,by omega⟩, Nat.find_spec hex, ?_⟩
    intro j hj
    exact le_of_not_gt (Nat.find_min hex hj)

theorem measurableSet_firstExceed {X : Type*} [MeasurableSpace X]
    (U : ℕ → X → ℝ) (lambda : ℝ) (n : ℕ) (hU : ∀ i ≤ n, Measurable (U i)) :
    MeasurableSet (firstExceed U lambda n) := by
  unfold firstExceed
  simp only [ofPred_and, ofPred_forall]
  exact (measurableSet_lt measurable_const (hU n le_rfl)).inter
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun hi =>
      measurableSet_le (hU i hi.le) measurable_const)

theorem firstExceed_measure_sum {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (U : ℕ → X → ℝ) (lambda : ℝ) (N : ℕ)
    (hU : ∀ i ≤ N, Measurable (U i)) :
    (∑ i : Fin (N + 1), μ.real (firstExceed U lambda i.val)) =
      μ.real (finiteMaxEvent U lambda N) := by
  rw [← firstExceed_union]
  symm
  apply measureReal_iUnion_fintype
  · intro i j hij
    exact firstExceed_disjoint U lambda (fun h => hij (Fin.ext h))
  · intro i
    exact measurableSet_firstExceed U lambda i (fun j hj => hU j (by omega))
  · intro i
    exact measure_ne_top μ _

theorem firstExceed_norm_overshoot {X E : Type*} [NormedAddCommGroup E]
    (F : ℕ → X → E) (x : X) {lambda D : ℝ} (hlambda : 0 ≤ lambda)
    (n : ℕ) (hjump : ∀ i < n, ‖F (i + 1) x - F i x‖ ≤ D)
    (hx : x ∈ firstExceed (fun i y => ‖F i y - F 0 y‖) lambda n) :
    ‖F n x - F 0 x‖ ≤ lambda + D := by
  have hn : n ≠ 0 := by
    intro hn
    have hh := hx.1
    simp only [hn, sub_self, norm_zero] at hh
    linarith
  have hp := hx.2 (n - 1) (by omega)
  have hj := hjump (n - 1) (by omega)
  rw [show n - 1 + 1 = n by omega] at hj
  exact (norm_sub_le_norm_sub_add_norm_sub (F n x) (F (n - 1) x) (F 0 x)).trans
    (by linarith)

theorem firstExceed_large_subset {X E : Type*} [NormedAddCommGroup E]
    (F : ℕ → X → E) (N n : ℕ) (hn : n ≤ N) {lambda D δ : ℝ}
    (hlambda : 0 ≤ lambda) (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hjump : ∀ i < N, ∀ x, ‖F (i + 1) x - F i x‖ ≤ D) :
    finiteMaxEvent (fun i x => ‖F i x - F 0 x‖) (lambda + D + δ) N ∩
        firstExceed (fun i x => ‖F i x - F 0 x‖) lambda n ⊆
      {x | ∃ i ≤ N - n, δ ≤ ‖F (n + i) x - F n x‖} ∩
        firstExceed (fun i x => ‖F i x - F 0 x‖) lambda n := by
  rintro x ⟨⟨k,hk,hlarge⟩,hx⟩
  refine ⟨?_,hx⟩
  have hkn : n ≤ k := by
    by_contra h
    have hb := hx.2 k (lt_of_not_ge h)
    linarith
  have hstop := firstExceed_norm_overshoot F x hlambda n
    (fun i hi => hjump i (hi.trans_le hn) x) hx
  refine ⟨k - n, by omega, ?_⟩
  rw [show n + (k - n) = k by omega]
  have htri := norm_sub_le_norm_sub_add_norm_sub (F k x) (F n x) (F 0 x)
  linarith

end LipschitzHilbert

end

end OAI
