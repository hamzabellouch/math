import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Disjoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

universe uI uLabel

namespace QuantitativeVanDerWaerden

open scoped BigOperators

theorem outer_log_one_sub_lower {z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2) :
    -2 * z ≤ Real.log (1 - z) := by
  have hpos : 0 < 1 - z := by linarith
  have hinv : (1 - z)⁻¹ ≤ 1 + 2 * z := by
    rw [← one_div]
    apply (div_le_iff₀ hpos).2
    have hmul : 0 ≤ z * (1 - 2 * z) := mul_nonneg hz (by linarith)
    nlinarith
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  linarith

theorem outer_exp_neg_two_le_one_sub {z : ℝ} (hz : 0 ≤ z)
    (hzhalf : z ≤ 1 / 2) : Real.exp (-2 * z) ≤ 1 - z := by
  have h := Real.exp_le_exp.mpr (outer_log_one_sub_lower hz hzhalf)
  rwa [Real.exp_log (by linarith : 0 < 1 - z)] at h

theorem outer_exp_sum_le_product {I : Type uI} (s : Finset I) (z : I → ℝ)
    (hz : ∀ i ∈ s, 0 ≤ z i) (hzhalf : ∀ i ∈ s, z i ≤ 1 / 2) :
    Real.exp (-2 * ∑ i ∈ s, z i) ≤ ∏ i ∈ s, (1 - z i) := by
  classical
  revert hz hzhalf
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    intro hz hzhalf
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have has : ∀ i ∈ s, i ∈ insert a s := fun i hi => Finset.mem_insert_of_mem hi
    have hza := hz a (Finset.mem_insert_self a s)
    have hza' := hzhalf a (Finset.mem_insert_self a s)
    calc
      Real.exp (-2 * (z a + ∑ i ∈ s, z i)) =
          Real.exp (-2 * z a) * Real.exp (-2 * ∑ i ∈ s, z i) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ (1 - z a) * ∏ i ∈ s, (1 - z i) := by
        exact mul_le_mul (outer_exp_neg_two_le_one_sub hza hza')
          (ih (fun i hi => hz i (has i hi)) (fun i hi => hzhalf i (has i hi)))
          (Real.exp_pos _).le (by linarith)

/-- The numerical criterion used for each outer bad event. -/
theorem outer_local_criterion {I : Type uI} (s : Finset I) (z : I → ℝ) (l : ℝ)
    (hl : 100 ≤ l) (hz : ∀ i ∈ s, 0 ≤ z i)
    (hzhalf : ∀ i ∈ s, z i ≤ 1 / 2)
    (hsum : ∑ i ∈ s, z i ≤ l / 500) :
    2 * Real.exp (-l / 8) ≤ Real.exp (-l / 32) * ∏ i ∈ s, (1 - z i) := by
  have htwo : 2 ≤ Real.exp ((1 / 8 - (1 / 32 + 2 / 500)) * l) := by
    have h := Real.add_one_le_exp ((1 / 8 - (1 / 32 + 2 / 500)) * l)
    linarith
  have htail : 2 * Real.exp (-l / 8) ≤ Real.exp (-(1 / 32 + 2 / 500) * l) := by
    calc
      2 * Real.exp (-l / 8) ≤
          Real.exp ((1 / 8 - (1 / 32 + 2 / 500)) * l) * Real.exp (-l / 8) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = Real.exp (-(1 / 32 + 2 / 500) * l) := by
        rw [← Real.exp_add]
        congr 1
        ring
  calc
    2 * Real.exp (-l / 8) ≤ Real.exp (-(1 / 32 + 2 / 500) * l) := htail
    _ ≤ Real.exp (-l / 32) * Real.exp (-2 * ∑ i ∈ s, z i) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    _ ≤ Real.exp (-l / 32) * ∏ i ∈ s, (1 - z i) :=
      mul_le_mul_of_nonneg_left (outer_exp_sum_le_product s z hz hzhalf)
        (Real.exp_pos _).le

theorem outer_weight_pos (l : ℝ) : 0 < Real.exp (-l / 32) := Real.exp_pos _

theorem outer_weight_lt_half {l : ℝ} (hl : 100 ≤ l) :
    Real.exp (-l / 32) < 1 / 2 := by
  have hpos := Real.exp_pos (-l / 32)
  have hlarge : 2 < Real.exp (l / 32) := by
    have h := Real.add_one_le_exp (l / 32)
    linarith
  have hmul : Real.exp (-l / 32) * Real.exp (l / 32) = 1 := by
    rw [← Real.exp_add]
    rw [show -l / 32 + l / 32 = 0 by ring]
    exact Real.exp_zero
  nlinarith

/-- Distinct tests are adjacent precisely when they share a label variable. -/
noncomputable def outerNeighbors {I : Type uI} {Label : Type uLabel} [Fintype I] [DecidableEq I]
    [DecidableEq Label] (support : I → Finset Label) (i : I) : Finset I :=
  Finset.univ.filter fun j => j ≠ i ∧ ¬ Disjoint (support i) (support j)

/-- A per-label incident bound gives the required per-test neighbor bound. -/
theorem outer_neighbor_weight_bound {I : Type uI} {Label : Type uLabel} [Fintype I] [DecidableEq I]
    [DecidableEq Label] (support : I → Finset Label) (weight : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (B : ℝ)
    (hincident : ∀ b, ∑ j ∈ Finset.univ.filter (fun j => b ∈ support j), weight j ≤ B)
    (i : I) :
    ∑ j ∈ outerNeighbors support i, weight j ≤ (support i).card * B := by
  classical
  let n := outerNeighbors support i
  have hcover : ∀ j ∈ n, weight j ≤
      ∑ b ∈ support i, if b ∈ support j then weight j else 0 := by
    intro j hj
    have hnot : ¬ Disjoint (support i) (support j) :=
      (Finset.mem_filter.mp hj).2.2
    obtain ⟨b, hbi, hbj⟩ := Finset.not_disjoint_iff.mp hnot
    have hsingle := Finset.single_le_sum
      (f := fun b => if b ∈ support j then weight j else 0)
      (fun b _ => by split_ifs <;> first | exact hweight j | exact le_rfl) hbi
    simpa only [ite_eq_left hbj] using hsingle
  calc
    ∑ j ∈ n, weight j ≤ ∑ j ∈ n, ∑ b ∈ support i,
        if b ∈ support j then weight j else 0 := Finset.sum_le_sum hcover
    _ = ∑ b ∈ support i, ∑ j ∈ n,
        if b ∈ support j then weight j else 0 := Finset.sum_comm
    _ ≤ ∑ _b ∈ support i, B := by
      apply Finset.sum_le_sum
      intro b hb
      have hsub : n.filter (fun j => b ∈ support j) ⊆
          Finset.univ.filter (fun j => b ∈ support j) := by
        intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, (Finset.mem_filter.mp hj).2⟩
      calc
        (∑ j ∈ n, if b ∈ support j then weight j else 0) =
            ∑ j ∈ n.filter (fun j => b ∈ support j), weight j := by
          rw [Finset.sum_filter]
        _ ≤ ∑ j ∈ Finset.univ.filter (fun j => b ∈ support j), weight j :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hweight j)
        _ ≤ B := hincident b
    _ = (support i).card * B := by simp

end QuantitativeVanDerWaerden

end OAI
