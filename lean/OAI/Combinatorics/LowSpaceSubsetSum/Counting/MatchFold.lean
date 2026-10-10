import OAI.Combinatorics.LowSpaceSubsetSum.Counting.MatchPotential

namespace OAI

/-! Exact callback semantics for matching Cartesian occurrences. -/

namespace LowSpaceSubsetSum
namespace MatchFold

universe u v w
variable {α : Type u} {β : Type v} {τ : Type w}

def run (key₁ : α → ℤ) (key₂ : β → ℤ) (report : α → β → τ → τ × Bool) :
    List α → List β → τ → τ
  | [], _, a => a
  | x :: xs, ys, a => run key₁ key₂ report xs ys
      ((ys.filter (fun y => decide (key₁ x = key₂ y))).foldl (fun a y => (report x y a).1) a)

theorem nil_right (key₁ : α → ℤ) (key₂ : β → ℤ) (report : α → β → τ → τ × Bool)
    (xs : List α) (a : τ) : run key₁ key₂ report xs [] a = a := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [run, List.filter_nil, List.foldl_nil] using ih

theorem append_left (key₁ : α → ℤ) (key₂ : β → ℤ) (report : α → β → τ → τ × Bool)
    (xs rest : List α) (ys : List β) (a : τ) :
    run key₁ key₂ report (xs ++ rest) ys a =
      run key₁ key₂ report rest ys (run key₁ key₂ report xs ys a) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, run, ih]

theorem filter_congr (key₁ : α → ℤ) (key₂ : β → ℤ) (report : α → β → τ → τ × Bool)
    (xs : List α) (ys zs : List β) (a : τ)
    (h : ∀ x ∈ xs, ys.filter (fun y => decide (key₁ x = key₂ y)) =
      zs.filter (fun y => decide (key₁ x = key₂ y))) :
    run key₁ key₂ report xs ys a = run key₁ key₂ report xs zs a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    rw [run, h x (by simp), run]
    exact ih _ (fun z hz => h z (by simp [hz]))

theorem group_eq (key₁ : α → ℤ) (key₂ : β → ℤ) (report : α → β → τ → τ × Bool)
    (K : ℤ) (xs : List α) (ys : List β) (a : τ)
    (hx : ∀ x ∈ xs, key₁ x = K) (hy : ∀ y ∈ ys, key₂ y = K) :
    run key₁ key₂ report xs ys a =
      xs.foldl (fun a x => ys.foldl (fun a y => (report x y a).1) a) a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    have hfilter : ys.filter (fun y => decide (key₁ x = key₂ y)) = ys := by
      apply List.filter_eq_self.mpr
      intro y hym
      simp only [hx x (by simp), hy y hym, decide_true]
    rw [run, hfilter, List.foldl_cons]
    exact ih _ (fun z hz => hx z (by simp [hz]))

theorem split_groups (key₁ : α → ℤ) (key₂ : β → ℤ) (report : α → β → τ → τ × Bool)
    (K : ℤ) (xs rest₁ : List α) (ys rest₂ : List β) (a : τ)
    (hx : ∀ x ∈ xs, key₁ x = K) (hy : ∀ y ∈ ys, key₂ y = K)
    (hr₁ : ∀ x ∈ rest₁, key₁ x ≠ K) (hr₂ : ∀ y ∈ rest₂, key₂ y ≠ K) :
    run key₁ key₂ report (xs ++ rest₁) (ys ++ rest₂) a =
      run key₁ key₂ report rest₁ rest₂
        (xs.foldl (fun a x => ys.foldl (fun a y => (report x y a).1) a) a) := by
  have hleft : ∀ a, run key₁ key₂ report xs (ys ++ rest₂) a = run key₁ key₂ report xs ys a := by
    intro a
    apply filter_congr
    intro x hxm
    have hz : rest₂.filter (fun y => decide (key₁ x = key₂ y)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro y hym
      simpa only [decide_eq_true_eq, hx x hxm] using (hr₂ y hym).symm
    simp only [List.filter_append, hz, List.append_nil]
  have hright : ∀ a, run key₁ key₂ report rest₁ (ys ++ rest₂) a =
      run key₁ key₂ report rest₁ rest₂ a := by
    intro a
    apply filter_congr
    intro x hxm
    have hz : ys.filter (fun y => decide (key₁ x = key₂ y)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro y hym
      simpa only [decide_eq_true_eq, hy y hym] using hr₁ x hxm
    simp only [List.filter_append, hz, List.nil_append]
  rw [append_left, hleft, hright, group_eq key₁ key₂ report K xs ys a hx hy]

theorem skip_left (key₁ : α → ℤ) (key₂ : β → ℤ) (report : α → β → τ → τ × Bool)
    (x : α) (xs : List α) (ys : List β) (a : τ)
    (h : ∀ y ∈ ys, key₁ x < key₂ y) :
    run key₁ key₂ report (x :: xs) ys a = run key₁ key₂ report xs ys a := by
  have he : ys.filter (fun y => decide (key₁ x = key₂ y)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro y hy
    simpa only [decide_eq_true_eq] using (h y hy).ne
  simp only [run, he, List.foldl_nil]

theorem skip_right (key₁ : α → ℤ) (key₂ : β → ℤ) (report : α → β → τ → τ × Bool)
    (xs : List α) (y : β) (ys : List β) (a : τ)
    (h : ∀ x ∈ xs, key₂ y < key₁ x) :
    run key₁ key₂ report xs (y :: ys) a = run key₁ key₂ report xs ys a := by
  apply filter_congr
  intro x hx
  have he : key₁ x ≠ key₂ y := (h x hx).ne.symm
  simp only [List.filter_cons, he, decide_false, Bool.false_eq_true, ite_false]

end MatchFold
end LowSpaceSubsetSum

end OAI
