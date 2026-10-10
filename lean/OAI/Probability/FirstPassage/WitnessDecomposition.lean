import Mathlib.Basic.Real.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Linarith

namespace OAI

namespace PlanarFPP

variable {α : Type*}

noncomputable def total (d : α → ℝ) (xs : List α) : ℝ := (xs.map d).sum
@[simp] theorem total_nil (d : α → ℝ) : total d [] = 0 := rfl
@[simp] theorem total_cons (d : α → ℝ) (x : α) (xs : List α) :
    total d (x :: xs) = d x + total d xs := by simp [total]
@[simp] theorem total_append (d : α → ℝ) (xs ys : List α) :
    total d (xs ++ ys) = total d xs + total d ys := by simp [total]

theorem first_drop (d : α → ℝ) (η : ℝ) (xs : List α)
    (hstep : ∀ x ∈ xs, -η ≤ d x) (a : ℝ) (ha : -η ≤ a)
    (hdrop : a + total d xs < -η) :
    ∃ pre rest, xs = pre ++ rest ∧ pre ≠ [] ∧
      -2 * η ≤ a + total d pre ∧ a + total d pre < -η := by
  induction xs generalizing a with
  | nil => simp at hdrop; linarith
  | cons x xs ih =>
    have hx := hstep x (by simp)
    have ht : ∀ y ∈ xs, -η ≤ d y := fun y hy => hstep y (by simp [hy])
    by_cases h : a + d x < -η
    · refine ⟨[x], xs, rfl, by simp, ?_, ?_⟩ <;> simp <;> linarith
    · obtain ⟨pre, rest, heq, hne, hlo, hhi⟩ :=
        ih ht (a + d x) (le_of_not_gt h) (by simpa [add_assoc] using hdrop)
      refine ⟨x :: pre, rest, by simp [heq], by simp, ?_, ?_⟩
      · simpa [add_assoc] using hlo
      · simpa [add_assoc] using hhi

theorem witness_decomposition (d : α → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (xs : List α) (hstep : ∀ x ∈ xs, -η ≤ d x) :
    ∃ blocks : List (List α), ∃ rest : List α,
      xs = blocks.flatten ++ rest ∧
      (∀ b ∈ blocks, b ≠ [] ∧ -2 * η ≤ total d b ∧ total d b < -η) ∧
      -η ≤ total d rest := by
  induction hn : xs.length using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    by_cases hlow : -η ≤ total d xs
    · exact ⟨[], xs, by simp, by simp, hlow⟩
    · obtain ⟨pre, rest, heq, hne, hlo, hhi⟩ :=
        first_drop d η xs hstep 0 (by linarith) (by simpa using lt_of_not_ge hlow)
      have hlen : rest.length < n := by
        rw [heq, List.length_append] at hn
        have : 0 < pre.length := List.length_pos_iff.mpr hne
        omega
      have hrest : ∀ x ∈ rest, -η ≤ d x := by
        intro x hx
        apply hstep x
        rw [heq]
        exact List.mem_append_right pre hx
      obtain ⟨bs, tail, hbs, hb, ht⟩ := ih rest.length hlen rest hrest rfl
      refine ⟨pre :: bs, tail, ?_, ?_, ht⟩
      · simp [heq, hbs, List.append_assoc]
      · intro b hb'
        rcases List.mem_cons.mp hb' with rfl | hb'
        · exact ⟨hne, by simpa using hlo, by simpa using hhi⟩
        · exact hb b hb'

theorem decomposition_lower_bound (d : α → ℝ) (η : ℝ)
    (blocks : List (List α)) (rest : List α)
    (hb : ∀ b ∈ blocks, -2 * η ≤ total d b) (hr : -η ≤ total d rest) :
    -η - 2 * η * blocks.length ≤ total d (blocks.flatten ++ rest) := by
  have hsum : -2 * η * blocks.length ≤ total d blocks.flatten := by
    induction blocks with
    | nil => simp
    | cons b bs ih =>
      have hfirst := hb b (by simp)
      have htail := ih (fun a ha => hb a (by simp [ha]))
      simp only [List.flatten_cons, total_append, List.length_cons, Nat.cast_add,
        Nat.cast_one]
      linarith
  rw [total_append]
  linarith

theorem disjoint_witness_decomposition (d : α → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (xs : List α) (hsimple : xs.Nodup) (hstep : ∀ x ∈ xs, -η ≤ d x) :
    ∃ blocks : List (List α), ∃ rest : List α,
      xs = blocks.flatten ++ rest ∧ blocks.Pairwise List.Disjoint ∧
      (∀ b ∈ blocks, b ≠ [] ∧ -2 * η ≤ total d b ∧ total d b < -η) ∧
      -η ≤ total d rest ∧
      -η - 2 * η * blocks.length ≤ total d xs := by
  obtain ⟨blocks, rest, heq, hb, hr⟩ := witness_decomposition d η hη xs hstep
  have hflat : blocks.flatten.Nodup := by
    rw [heq] at hsimple
    exact (List.nodup_append.mp hsimple).1
  refine ⟨blocks, rest, heq, (List.nodup_flatten.mp hflat).2, hb, hr, ?_⟩
  rw [heq]
  exact decomposition_lower_bound d η blocks rest (fun b h => (hb b h).2.1) hr

theorem defect_bound_from_witness_capacity (d : α → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (xs : List α) (hsimple : xs.Nodup) (hstep : ∀ x ∈ xs, -η ≤ d x)
    (M : ℕ)
    (hcapacity : ∀ blocks : List (List α),
      blocks.Pairwise List.Disjoint →
      (∀ b ∈ blocks, b ≠ [] ∧ b.Sublist xs ∧ total d b < -η) →
      blocks.length ≤ M) :
    -η - 2 * η * M ≤ total d xs := by
  obtain ⟨blocks, rest, heq, hdisj, hb, hr, hbound⟩ :=
    disjoint_witness_decomposition d η hη xs hsimple hstep
  have hM : blocks.length ≤ M := by
    apply hcapacity blocks hdisj
    intro b hmem
    refine ⟨(hb b hmem).1, ?_, (hb b hmem).2.2⟩
    rw [heq]
    exact (List.sublist_flatten_of_mem hmem).trans (List.sublist_append_left _ _)
  have hM' : (blocks.length : ℝ) ≤ M := by exact_mod_cast hM
  nlinarith [mul_le_mul_of_nonneg_left hM' hη]

theorem edge_disjoint_witness_decomposition {β : Type*} (edge : α → β)
    (d : α → ℝ) (η : ℝ) (hη : 0 ≤ η) (xs : List α)
    (hsimple : (xs.map edge).Nodup) (hstep : ∀ x ∈ xs, -η ≤ d x) :
    ∃ blocks : List (List α), ∃ rest : List α,
      xs = blocks.flatten ++ rest ∧
      blocks.Pairwise (fun b c => List.Disjoint (b.map edge) (c.map edge)) ∧
      (∀ b ∈ blocks, b ≠ [] ∧ -2 * η ≤ total d b ∧ total d b < -η) ∧
      -η ≤ total d rest ∧
      -η - 2 * η * blocks.length ≤ total d xs := by
  obtain ⟨blocks, rest, heq, hb, hr⟩ := witness_decomposition d η hη xs hstep
  have hflat : (blocks.flatten.map edge).Nodup := by
    rw [heq, List.map_append] at hsimple
    exact (List.nodup_append.mp hsimple).1
  have hdisj : blocks.Pairwise (fun b c => List.Disjoint (b.map edge) (c.map edge)) := by
    rw [List.map_flatten] at hflat
    exact List.pairwise_map.mp (List.nodup_flatten.mp hflat).2
  refine ⟨blocks, rest, heq, hdisj, hb, hr, ?_⟩
  rw [heq]
  exact decomposition_lower_bound d η blocks rest (fun b h => (hb b h).2.1) hr

theorem full_chunk_lower_bound (H η s : ℝ) (M : ℕ)
    (hηs : 0 ≤ η * s) (hbasic : -η * s - 2 * η * s * M ≤ H)
    (hzero : M = 0 → η * s ≤ H) : η * s - 4 * η * s * M ≤ H := by
  by_cases hM : M = 0
  · simpa [hM] using hzero hM
  · have hM' : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hM
    nlinarith [mul_le_mul_of_nonneg_left hM' hηs]

end PlanarFPP

end OAI
