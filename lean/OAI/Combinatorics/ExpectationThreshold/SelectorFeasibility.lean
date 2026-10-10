import OAI.Combinatorics.ExpectationThreshold.SelectorDefinitionsLemmas
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Feasible minima and the actual containment cover

Resetting an original family member to the first color proves existence of
a bounded feasible move. Minimization itself retains the unrestricted
feasibility witness from `Feasible`; the witness need not be that member.
All retained minima contribute their actual changed sets to a cover.
-/

noncomputable section

open scoped BigOperators

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {F : Family α} {s : ℕ}

/-- Reset only the specified member to zero, the first color index. -/
def reset (a : Coloring α s) (H₀ : ↥F) : Coloring α s :=
  fun x => if x ∈ H₀.val then 0 else a x

omit [Fintype α] in
theorem reset_earlier (a : Coloring α s) (H₀ : ↥F) :
    Earlier a (reset a H₀) := by
  intro x
  by_cases hx : x ∈ H₀.val
  · simp [reset, hx]
  · simp [reset, hx]

theorem changes_reset_subset (a : Coloring α s) (H₀ : ↥F) :
    changes a (reset a H₀) ⊆ H₀.val := by
  intro x hx
  by_contra hnot
  have hlt := (Finset.mem_filter.mp hx).2
  simp [reset, hnot] at hlt

/-- The reset uses this one member as a witness, with every cutoff zero. -/
theorem reset_feasibleFor (mu : MassFamily F) (a : Coloring α s) (H₀ : ↥F) :
    FeasibleFor mu a (reset a H₀) H₀ := by
  classical
  intro i
  refine ⟨0, le_rfl, zero_le_one, ?_, ?_⟩
  · intro x hpos
    have hx : x ∈ H₀.val := by
      by_contra hnot
      rw [mu.supported H₀ x hnot] at hpos
      exact (lt_irrefl (0 : ℝ)) hpos
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ x, ?_⟩
    change (if x ∈ H₀.val then (0 : Color s) else a x).val ≤ i.val
    rw [ite_eq_left hx]
    exact Nat.zero_le i.val
  · have hmin : ∀ x, min (mu.weight H₀ x) (0 : ℝ) = 0 :=
      fun x => min_eq_right (mu.nonneg H₀ x)
    simp only [truncatedExcess, hmin, zero_mul, Finset.sum_const_zero, mul_zero, le_refl]

theorem reset_boundedFeasible (mu : MassFamily F) (a : Coloring α s) (H₀ : ↥F) :
    BoundedFeasible mu a H₀ (reset a H₀) :=
  ⟨⟨reset_earlier a H₀, H₀, reset_feasibleFor mu a H₀⟩, changes_reset_subset a H₀⟩

/-- A minimum exists for every member, without restricting its witness. -/
theorem exists_isMinimalMove (mu : MassFamily F) (a : Coloring α s) (H₀ : ↥F) :
    ∃ z, IsMinimalMove mu a H₀ z := by
  classical
  let P : ℕ → Prop := fun k =>
    ∃ z : Coloring α s, BoundedFeasible mu a H₀ z ∧ movement a z = k
  have hex : ∃ k, P k :=
    ⟨movement a (reset a H₀), reset a H₀, reset_boundedFeasible mu a H₀, rfl⟩
  obtain ⟨z, hz, hcost⟩ := Nat.find_spec hex
  refine ⟨z, hz, ?_⟩
  intro w hw
  rw [hcost]
  exact Nat.find_min' hex ⟨w, hw, rfl⟩

theorem Selected.feasible {mu : MassFamily F} {a z : Coloring α s}
    (hz : Selected mu a z) : Feasible mu a z := by
  obtain ⟨H₀, hz⟩ := hz
  exact hz.1.1

theorem Selected.earlier {mu : MassFamily F} {a z : Coloring α s}
    (hz : Selected mu a z) : Earlier a z := hz.feasible.1

@[simp] theorem mem_selectedMoves {mu : MassFamily F} {a z : Coloring α s} :
    z ∈ selectedMoves mu a ↔ Selected mu a z := by
  classical
  simp [selectedMoves]

/-- Remove duplicate changed sets only when forming the containment cover. -/
def selectedChanges (mu : MassFamily F) (a : Coloring α s) : Family α := by
  classical
  exact (selectedMoves mu a).image (changes a)

theorem selectedChanges_covers (mu : MassFamily F) (a : Coloring α s) :
    Covers (selectedChanges mu a) F := by
  classical
  intro H hH
  obtain ⟨z, hz⟩ := exists_isMinimalMove mu a ⟨H, hH⟩
  refine ⟨changes a z, ?_, hz.1.2⟩
  exact Finset.mem_image.mpr
    ⟨z, mem_selectedMoves.mpr ⟨⟨H, hH⟩, hz⟩, rfl⟩

/-- The sum over selected colorings dominates the cost with duplicates removed. -/
theorem half_lt_selectedMoves_cost (mu : MassFamily F) (a : Coloring α s)
    {p : ℝ} (hp : 0 ≤ p) (hF : ¬ Small p F) :
    (1 / 2 : ℝ) < ∑ z ∈ selectedMoves mu a, p ^ (changes a z).card := by
  classical
  exact (cost_gt_of_not_small hF (selectedChanges_covers mu a)).trans_le
    (cost_image_le hp (selectedMoves mu a) (changes a))

omit [DecidableEq α] in
/-- An earlier move with no changed vertex is the unchanged coloring. -/
theorem eq_of_changes_eq_empty {a z : Coloring α s} (hz : Earlier a z)
    (hempty : changes a z = ∅) : z = a := by
  funext x
  apply le_antisymm (hz x)
  apply le_of_not_gt
  intro hlt
  have hx : x ∈ changes a z := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hlt⟩
  rw [hempty] at hx
  exact Finset.notMem_empty x hx

/-- Restoring weights increases the excess: only heavy points change, and
their coefficient is the nonnegative value `d`. -/
theorem truncatedExcess_le_original (w : α → ℝ) (A : Finset α) (d u : ℝ)
    (hd : 0 ≤ d) (hheavy : ∀ x, u < w x → x ∈ A) :
    truncatedExcess w A d u ≤
      ∑ x, w x * ((if x ∈ A then 1 else 0) - (1 - d)) := by
  classical
  unfold truncatedExcess
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : x ∈ A
  · have hcoef : ((if x ∈ A then (1 : ℝ) else 0) - (1 - d)) = d := by
      rw [ite_eq_left hx]
      ring
    rw [hcoef]
    exact mul_le_mul_of_nonneg_right (min_le_left (w x) u) hd
  · have hxu : w x ≤ u := le_of_not_gt (fun h => hx (hheavy x h))
    rw [min_eq_left hxu]

theorem originalExcess_eq_mass_sub (w : α → ℝ) (A : Finset α) (d : ℝ)
    (htotal : ∑ x, w x = 1) :
    (∑ x, w x * ((if x ∈ A then 1 else 0) - (1 - d))) =
      (∑ x ∈ A, w x) - (1 - d) := by
  classical
  calc
    (∑ x, w x * ((if x ∈ A then 1 else 0) - (1 - d))) =
        (∑ x, if x ∈ A then w x else 0) - (∑ x, w x) * (1 - d) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> ring
    _ = (∑ x ∈ A, w x) - (1 - d) := by
      rw [Finset.sum_ite_mem_eq, htotal, one_mul]

/-- The actual feasibility witness is chosen once, before the scale index. -/
theorem captured_of_feasible_self {mu : MassFamily F} {a : Coloring α s}
    (h : Feasible mu a a) : Captured mu a := by
  classical
  obtain ⟨H, hH⟩ := h.2
  refine ⟨H, ?_⟩
  intro i
  obtain ⟨u, hu⟩ := hH i
  have htest : 0 ≤ truncatedExcess (mu.weight H) (prefixSet a i) (dscale i) u := by
    simpa [crossings] using hu.2.2.2
  have hfull : 0 ≤ (∑ x ∈ prefixSet a i, mu.weight H x) - (1 - dscale i) := by
    calc
      0 ≤ truncatedExcess (mu.weight H) (prefixSet a i) (dscale i) u := htest
      _ ≤ ∑ x, mu.weight H x *
          ((if x ∈ prefixSet a i then 1 else 0) - (1 - dscale i)) :=
        truncatedExcess_le_original (mu.weight H) (prefixSet a i) (dscale i) u
          (dscale_nonneg i) hu.2.2.1
      _ = (∑ x ∈ prefixSet a i, mu.weight H x) - (1 - dscale i) :=
        originalExcess_eq_mass_sub (mu.weight H) (prefixSet a i) (dscale i) (mu.total H)
  exact sub_nonneg.mp hfull

theorem Selected.changes_nonempty {mu : MassFamily F} {a z : Coloring α s}
    (hz : Selected mu a z) (ha : Bad mu a) : (changes a z).Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro hempty
  have hza : z = a := eq_of_changes_eq_empty hz.earlier hempty
  have hself : Feasible mu a a := by simpa only [hza] using hz.feasible
  exact ha (captured_of_feasible_self hself)

end TalagrandThreshold.Selector

end

end OAI
