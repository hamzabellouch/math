import OAI.Combinatorics.EditApproximation.Geometry.Geometry

namespace OAI

/-!
# Splitting an optimal edit script at a source cut

An arbitrary unrestricted edit script transports a cut through its
intermediate strings. Each edit belongs to one side of that cut. Applied
to a shortest script, this gives an exact optimal target split, including
empty source or target pieces.
-/

namespace EditApproximation

open EditDistortion

universe u

theorem step_split {α : Type u} {x y : List α} (step : Step true x y)
    (left right : List α) (hx : x = left ++ right) :
    ∃ left' right', y = left' ++ right' ∧
      ((Step true left left' ∧ right = right') ∨
        (left = left' ∧ Step true right right')) := by
  cases step with
  | insert p q a =>
    rcases List.append_eq_append_iff.mp hx.symm with ⟨mid, hp, hr⟩ | ⟨mid, hl, hq⟩
    · refine ⟨left, mid ++ a :: q, ?_, Or.inr ⟨rfl, ?_⟩⟩
      · simp only [hp, List.append_assoc]
      · rw [hr]
        exact Step.insert mid q a
    · refine ⟨p ++ a :: mid, right, ?_, Or.inl ⟨?_, rfl⟩⟩
      · simp only [hq, List.append_assoc, List.cons_append]
      · rw [hl]
        exact Step.insert p mid a
  | delete p q a =>
    rcases List.append_eq_append_iff.mp hx.symm with ⟨mid, hp, hr⟩ | ⟨mid, hl, hq⟩
    · refine ⟨left, mid ++ q, ?_, Or.inr ⟨rfl, ?_⟩⟩
      · simp only [hp, List.append_assoc]
      · rw [hr]
        exact Step.delete mid q a
    · cases mid with
      | nil =>
        simp only [List.append_nil] at hl
        simp only [List.nil_append] at hq
        refine ⟨left, q, ?_, Or.inr ⟨rfl, ?_⟩⟩
        · rw [hl]
        · rw [← hq]
          exact Step.delete [] q a
      | cons b mid =>
        simp only [List.cons_append, List.cons.injEq] at hq
        rcases hq with ⟨rfl, hq⟩
        refine ⟨p ++ mid, right, ?_, Or.inl ⟨?_, rfl⟩⟩
        · simp only [hq, List.append_assoc]
        · rw [hl]
          exact Step.delete p mid a
  | substitute _ p q a b =>
    rcases List.append_eq_append_iff.mp hx.symm with ⟨mid, hp, hr⟩ | ⟨mid, hl, hq⟩
    · refine ⟨left, mid ++ b :: q, ?_, Or.inr ⟨rfl, ?_⟩⟩
      · simp only [hp, List.append_assoc]
      · rw [hr]
        exact Step.substitute rfl mid q a b
    · cases mid with
      | nil =>
        simp only [List.append_nil] at hl
        simp only [List.nil_append] at hq
        refine ⟨left, b :: q, ?_, Or.inr ⟨rfl, ?_⟩⟩
        · rw [hl]
        · rw [← hq]
          exact Step.substitute rfl [] q a b
      | cons c mid =>
        simp only [List.cons_append, List.cons.injEq] at hq
        rcases hq with ⟨rfl, hq⟩
        refine ⟨p ++ b :: mid, right, ?_, Or.inl ⟨?_, rfl⟩⟩
        · simp only [hq, List.append_assoc, List.cons_append]
        · rw [hl]
          exact Step.substitute rfl p mid a b

theorem script_split {α : Type u} {x y : List α} {n : ℕ}
    (script : Script true n x y) (left right : List α) (hx : x = left ++ right) :
    ∃ left' right' nleft nright,
      y = left' ++ right' ∧ nleft + nright = n ∧
        Script true nleft left left' ∧ Script true nright right right' := by
  induction script generalizing left right with
  | nil x => exact ⟨left, right, 0, 0, hx, rfl, .nil _, .nil _⟩
  | @cons n x y z step rest ih =>
    obtain ⟨midleft, midright, hy, hs⟩ := step_split step left right hx
    obtain ⟨lastleft, lastright, nl, nr, hz, hn, hleft, hright⟩ :=
      ih midleft midright hy
    rcases hs with ⟨hstep, rfl⟩ | ⟨rfl, hstep⟩
    · exact ⟨lastleft, lastright, nl + 1, nr, hz, by omega,
        .cons hstep hleft, hright⟩
    · exact ⟨lastleft, lastright, nl, nr + 1, hz, by omega,
        hleft, .cons hstep hright⟩

/-- A shortest unrestricted edit script admits an exactly optimal split
at every source cut. -/
theorem edit_append_split {α : Type u} (left right target : List α) :
    ∃ targetLeft targetRight, target = targetLeft ++ targetRight ∧
      edit (left ++ right) target = edit left targetLeft + edit right targetRight := by
  obtain ⟨tl, tr, nl, nr, ht, hn, hl, hr⟩ :=
    script_split (cost_spec (s := true) (left ++ right) target) left right rfl
  refine ⟨tl, tr, ht, Nat.le_antisymm ?_ ?_⟩
  · rw [ht]
    exact cost_append_le (s := true) left tl right tr
  · have hleft := cost_le hl
    have hright := cost_le hr
    change edit left tl ≤ nl at hleft
    change edit right tr ≤ nr at hright
    change nl + nr = edit (left ++ right) target at hn
    omega

/-- Repeated source cuts have a common ordered target partition whose
piecewise edit costs sum exactly to the parent optimum. Source pieces
may be empty. A nonempty list of pieces is needed to assign insertions. -/
theorem edit_partition_split {α : Type u} (parts : List (List α))
    (hne : parts ≠ []) (target : List α) :
    ∃ targetParts : List (List α), targetParts.length = parts.length ∧
      targetParts.flatten = target ∧
      (List.zipWith edit parts targetParts).sum = edit parts.flatten target := by
  induction parts generalizing target with
  | nil => exact False.elim (hne rfl)
  | cons first rest ih =>
    cases rest with
    | nil =>
      refine ⟨[target], rfl, ?_, ?_⟩
      · simp
      · simp
    | cons second rest =>
      obtain ⟨tl, tr, ht, hc⟩ := edit_append_split first (second :: rest).flatten target
      obtain ⟨targets, hlen, hflatten, hcost⟩ := ih (by simp) tr
      refine ⟨tl :: targets, by simp only [List.length_cons, hlen], ?_, ?_⟩
      · simp only [List.flatten_cons, hflatten]
        exact ht.symm
      · simp only [List.flatten_cons, List.zipWith_cons_cons, List.sum_cons, hcost]
        exact hc.symm

/-- Prefixes of an ordered source/target partition use at most the
partition's total edit cost. This bounds every alignment anchor shift. -/
theorem edit_partition_prefix_le {α : Type u}
    (parts targets : List (List α)) (hlen : parts.length = targets.length) (k : ℕ) :
    edit (parts.take k).flatten (targets.take k).flatten ≤
      (List.zipWith edit parts targets).sum := by
  induction parts generalizing targets k with
  | nil =>
    have ht : targets = [] := List.length_eq_zero_iff.mp hlen.symm
    subst targets
    simp only [List.take_nil, List.flatten_nil, List.zipWith_nil_left, List.sum_nil]
    exact (cost_refl ([] : List α)).le
  | cons first rest ih =>
    cases targets with
    | nil => simp at hlen
    | cons targetFirst targetRest =>
      have hrest : rest.length = targetRest.length := by simpa using hlen
      cases k with
      | zero =>
        simp only [List.take_zero, List.flatten_nil]
        exact (cost_refl ([] : List α)).le.trans (Nat.zero_le _)
      | succ k =>
        simp only [List.take_succ_cons, List.flatten_cons, List.zipWith_cons_cons, List.sum_cons]
        exact (cost_append_le (s := true) first targetFirst
          (rest.take k).flatten (targetRest.take k).flatten).trans
            (Nat.add_le_add_left (ih targetRest hrest k) _)

theorem optimal_partition_anchor_shift_bound {α : Type u}
    (parts targets : List (List α)) (target : List α)
    (hlen : parts.length = targets.length)
    (hcost : (List.zipWith edit parts targets).sum = edit parts.flatten target) (k : ℕ) :
    |((targets.take k).flatten.length : ℝ) - (parts.take k).flatten.length| ≤
      (edit parts.flatten target : ℝ) := by
  apply (abs_length_gap_le_edit (parts.take k).flatten (targets.take k).flatten).trans
  exact_mod_cast (edit_partition_prefix_le parts targets hlen k).trans_eq hcost

end EditApproximation

end OAI
