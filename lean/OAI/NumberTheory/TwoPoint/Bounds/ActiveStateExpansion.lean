import OAI.NumberTheory.TwoPoint.Circuits.CircuitEncoding
import OAI.NumberTheory.TwoPoint.Bounds.ScalarComparison
import Mathlib.Data.Nat.Choose.Bounds

namespace OAI

/-! Exact active-prime states give small scalar expansions after the
degree truncation. All absent prime tests remain in each conjunction. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def activeState {n : ℕ} (x : BooleanCube n) : Finset (Fin n) :=
  univ.filter (fun i => x i = true)

def boundedActiveStates (n M : ℕ) : Finset (Finset (Fin n)) :=
  univ.powerset.filter (fun S => S.card ≤ M)

lemma mem_boundedActiveStates {n M : ℕ} {S : Finset (Fin n)} :
    S ∈ boundedActiveStates n M ↔ S.card ≤ M := by
  simp only [boundedActiveStates, mem_filter, mem_powerset, subset_univ, true_and]

lemma boundedActiveStates_card (n M : ℕ) :
    (boundedActiveStates n M).card ≤ (M + 1) * (n + 1) ^ M := by
  have he : boundedActiveStates n M =
      (range (M + 1)).biUnion (fun r => univ.powersetCard r) := by
    ext S
    simp only [mem_boundedActiveStates, mem_biUnion, mem_range, mem_powersetCard,
      subset_univ, true_and]
    constructor
    · intro hS
      exact ⟨S.card, by omega, rfl⟩
    · rintro ⟨r, hr, he⟩
      omega
  rw [he]
  apply (card_biUnion_le).trans
  calc
    (∑ r ∈ range (M + 1), (univ.powersetCard r : Finset (Finset (Fin n))).card) =
        ∑ r ∈ range (M + 1), n.choose r := by
      simp only [card_powersetCard, card_univ, Fintype.card_fin]
    _ ≤ ∑ _r ∈ range (M + 1), (n + 1) ^ M := by
      apply sum_le_sum
      intro r hr
      exact (Nat.choose_le_pow n r).trans
        ((Nat.pow_le_pow_left (Nat.le_succ n) r).trans
          (Nat.pow_le_pow_right (by omega) (by simp only [mem_range] at hr; omega)))
    _ = _ := by simp

def activeStateCircuit {n : ℕ} (S : Finset (Fin n)) : AC0Circuit n :=
  .andGate (fun i : Fin n => .literal i (decide (i ∈ S)))

lemma activeStateCircuit_eval {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) :
    (activeStateCircuit S).eval x = true ↔ activeState x = S := by
  simp only [activeStateCircuit, AC0Circuit.eval, decide_eq_true_eq]
  constructor
  · intro h
    ext i
    have hi := h i
    by_cases hs : i ∈ S <;> cases hx : x i <;>
      simp_all [activeState]
  · intro h i
    have hi : x i = true ↔ i ∈ S := by
      rw [← h]
      simp only [activeState, mem_filter, mem_univ, true_and]
    by_cases hs : i ∈ S <;> cases hx : x i <;>
      simp_all [activeState]

lemma activeStateCircuit_depth {n : ℕ} (S : Finset (Fin n)) :
    (activeStateCircuit S).depth ≤ 1 := by
  simp [activeStateCircuit, AC0Circuit.depth]

lemma activeStateCircuit_size {n : ℕ} (S : Finset (Fin n)) :
    (activeStateCircuit S).size = 1 + n := by
  simp [activeStateCircuit, AC0Circuit.size]

theorem activeState_scalar_expansion {n : ℕ} (M : ℕ)
    (f : Finset (Fin n) → ℝ) (x : BooleanCube n) :
    (if (activeState x).card ≤ M then f (activeState x) else 0) =
      ∑ S ∈ boundedActiveStates n M, f S * (activeStateCircuit S).indicator x := by
  simp only [AC0Circuit.indicator]
  have hval (S : Finset (Fin n)) :
      (if (activeStateCircuit S).eval x = true then (1 : ℝ) else 0) =
        if activeState x = S then 1 else 0 := by
    simp only [activeStateCircuit_eval]
  simp only [hval, mul_ite, mul_one, mul_zero]
  by_cases hx : (activeState x).card ≤ M
  · rw [ite_eq_left hx, sum_eq_single_of_mem (activeState x) (mem_boundedActiveStates.mpr hx)]
    · simp
    · intro S _ hS
      exact ite_eq_right (Ne.symm hS)
  · rw [ite_eq_right hx]
    symm
    apply sum_eq_zero
    intro S hS
    apply ite_eq_right
    intro he
    exact hx (he.symm ▸ mem_boundedActiveStates.mp hS)

lemma activeState_coefficient_mass {n M : ℕ} (f : Finset (Fin n) → ℝ) (C : ℝ)
    (hf : ∀ S ∈ boundedActiveStates n M, |f S| ≤ C) :
    ∑ S ∈ boundedActiveStates n M, |f S| ≤ ((M + 1) * (n + 1) ^ M : ℕ) * C := by
  by_cases hC : 0 ≤ C
  · calc
      _ ≤ ∑ _S ∈ boundedActiveStates n M, C := sum_le_sum hf
      _ = ((boundedActiveStates n M).card : ℝ) * C := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast boundedActiveStates_card n M) hC
  · have hz : ∅ ∈ boundedActiveStates n M := mem_boundedActiveStates.mpr (by simp)
    exact False.elim (hC ((abs_nonneg (f ∅)).trans (hf ∅ hz)))

theorem activeState_average_comparison {n : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    (M : ℕ) (f : Finset (Fin n) → ℝ) (x : α → BooleanCube n) (y : β → BooleanCube n)
    (C ε : ℝ) (hε : 0 ≤ ε)
    (hf : ∀ S ∈ boundedActiveStates n M, |f S| ≤ C)
    (hcompare : ∀ S ∈ boundedActiveStates n M,
      |uniformAverage (fun a => (activeStateCircuit S).indicator (x a)) -
        uniformAverage (fun b => (activeStateCircuit S).indicator (y b))| ≤ ε) :
    |uniformAverage (fun a => if (activeState (x a)).card ≤ M then f (activeState (x a)) else 0) -
      uniformAverage (fun b => if (activeState (y b)).card ≤ M then f (activeState (y b)) else 0)| ≤
        (((M + 1) * (n + 1) ^ M : ℕ) : ℝ) * C * ε := by
  let S := boundedActiveStates n M
  have hrep (z : BooleanCube n) :
      (if (activeState z).card ≤ M then f (activeState z) else 0) =
        ∑ t : S, f t.val * (activeStateCircuit t.val).indicator z := by
    rw [activeState_scalar_expansion]
    exact (sum_coe_sort S (fun t => f t * (activeStateCircuit t).indicator z)).symm
  simp_rw [hrep]
  have hb := scalar_average_comparison_uniform
    (fun (t : S) a => (activeStateCircuit t.val).indicator (x a))
    (fun (t : S) b => (activeStateCircuit t.val).indicator (y b))
    (fun t : S => f t.val) ε (fun t => hcompare t.val t.property)
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ hε
  change (∑ t : boundedActiveStates n M, |f t.val|) ≤ _
  calc
    _ = ∑ t ∈ boundedActiveStates n M, |f t| :=
      sum_coe_sort (boundedActiveStates n M) (fun t => |f t|)
    _ ≤ _ := activeState_coefficient_mass f C hf

end TwoPointCorrelations

end OAI
