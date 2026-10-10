import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

namespace OAI
/-!
The alternating sum of finite chains cancels when an admissibility condition is stable under
joining with a fixed nonbottom element. The involution inserts or removes the join of that
element with the largest chain element that does not lie above it. Bottom is implicit, so
an empty set represents the chain consisting of bottom alone and has sign `+1`.
-/
namespace FiniteChain
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α] [SemilatticeSup α] [OrderBot α]

/-- Every pair of members of a finite set is comparable. -/
def Ordered (s : Finset α) : Prop := ∀ a ∈ s, ∀ b ∈ s, a ≤ b ∨ b ≤ a

omit [Fintype α] in
theorem sup_bot_or_mem (s : Finset α) (h : Ordered s) :
    s.sup id = ⊥ ∨ s.sup id ∈ s := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have ht : Ordered s := fun x hx y hy => h x (mem_insert_of_mem hx) y (mem_insert_of_mem hy)
    rcases ih ht with hb | hm
    · rw [sup_insert, id_eq, hb, sup_bot_eq]
      exact Or.inr (mem_insert_self _ _)
    · rcases h a (mem_insert_self _ _) (s.sup id) (mem_insert_of_mem hm) with hab | hba
      · rw [sup_insert, id_eq, sup_eq_right.mpr hab]
        exact Or.inr (mem_insert_of_mem hm)
      · rw [sup_insert, id_eq, sup_eq_left.mpr hba]
        exact Or.inr (mem_insert_self _ _)

/-- The chain elements which do not lie above the fixed element. -/
noncomputable def bad (P : α) (s : Finset α) : Finset α := by
  classical
  exact s.filter (fun q => ¬ P ≤ q)
/-- The largest element of `bad P s`, or bottom if there are none. -/
noncomputable def pivot (P : α) (s : Finset α) : α := (bad P s).sup id
/-- The element whose presence in the chain is toggled. -/
noncomputable def inserted (P : α) (s : Finset α) : α := pivot P s ⊔ P
/-- Insert or remove the join of the pivot with the fixed element. -/
noncomputable def toggle (P : α) (s : Finset α) : Finset α := by
  classical
  exact if inserted P s ∈ s then s.erase (inserted P s) else insert (inserted P s) s

omit [Fintype α] in
theorem pivot_description {P : α} (hP : P ≠ ⊥) {s : Finset α} (hs : Ordered s) :
    ¬ P ≤ pivot P s ∧ (pivot P s = ⊥ ∨ pivot P s ∈ s) := by
  classical
  have hb : Ordered (bad P s) := fun a ha b hb => hs a (mem_filter.mp ha).1 b (mem_filter.mp hb).1
  rcases sup_bot_or_mem (bad P s) hb with he | hm
  · change (¬ P ≤ (bad P s).sup id) ∧
      ((bad P s).sup id = ⊥ ∨ (bad P s).sup id ∈ s)
    rw [he]
    exact ⟨fun h => hP (le_bot_iff.mp h), Or.inl rfl⟩
  · exact ⟨(mem_filter.mp hm).2, Or.inr (mem_filter.mp hm).1⟩

omit [Fintype α] [DecidableEq α] in
theorem comparable_inserted {P : α} {s : Finset α} (hs : Ordered s)
    {x : α} (hx : x ∈ s) : x ≤ inserted P s ∨ inserted P s ≤ x := by
  classical
  by_cases hp : P ≤ x
  · right
    apply sup_le _ hp
    apply Finset.sup_le_iff.mpr
    intro a ha
    rcases mem_filter.mp ha with ⟨has, hpa⟩
    rcases hs a has x hx with hax | hxa
    · exact hax
    · exact False.elim (hpa (hp.trans hxa))
  · left
    exact (Finset.le_sup (f := id) (show x ∈ bad P s from mem_filter.mpr ⟨hx, hp⟩)).trans le_sup_left

omit [Fintype α] in
theorem bad_toggle (P : α) (s : Finset α) : bad P (toggle P s) = bad P s := by
  classical
  have hr : P ≤ inserted P s := le_sup_right
  ext x
  by_cases hx : x = inserted P s
  · subst x
    simp [bad, hr]
  · by_cases ht : inserted P s ∈ s
    · simp [bad, toggle, ht, hx]
    · simp [bad, toggle, ht, hx]

omit [Fintype α] in
theorem toggle_twice (P : α) (s : Finset α) : toggle P (toggle P s) = s := by
  classical
  have hr : inserted P (toggle P s) = inserted P s := by
    unfold inserted pivot
    rw [bad_toggle]
  rw [toggle, hr]
  by_cases h : inserted P s ∈ s <;> simp [toggle, h]

/-- A chain of nonbottom elements satisfying the admissibility condition. -/
def Admissible (allowed : α → Prop) (s : Finset α) : Prop :=
  Ordered s ∧ ∀ x ∈ s, x ≠ ⊥ ∧ allowed x
/-- The finite set of admissible chains. -/
noncomputable def chains (allowed : α → Prop) : Finset (Finset α) := by
  classical
  exact univ.powerset.filter (Admissible allowed)

omit [Fintype α] in
theorem toggle_admissible {allowed : α → Prop} {P : α} (hP : P ≠ ⊥)
    (hbot : allowed ⊥) (hjoin : ∀ q, allowed q → allowed (q ⊔ P))
    {s : Finset α} (hs : Admissible allowed s) : Admissible allowed (toggle P s) := by
  classical
  have hpiv := pivot_description hP hs.1
  have hr : inserted P s ≠ ⊥ := fun he => hP (le_bot_iff.mp (he ▸ (le_sup_right : P ≤ inserted P s)))
  have har : allowed (inserted P s) := by
    apply hjoin
    rcases hpiv.2 with h | h
    · rw [h]; exact hbot
    · exact (hs.2 _ h).2
  have hi : Admissible allowed (insert (inserted P s) s) := by
    constructor
    · intro a ha b hb
      rcases mem_insert.mp ha with rfl | ha
      · rcases mem_insert.mp hb with rfl | hb
        · exact Or.inl le_rfl
        · exact (comparable_inserted hs.1 hb).symm
      · rcases mem_insert.mp hb with rfl | hb
        · exact comparable_inserted hs.1 ha
        · exact hs.1 a ha b hb
    · intro a ha
      rcases mem_insert.mp ha with rfl | ha
      · exact ⟨hr, har⟩
      · exact hs.2 a ha
  unfold toggle
  split_ifs
  · exact ⟨fun a ha b hb => hs.1 a (mem_of_mem_erase ha) b (mem_of_mem_erase hb),
      fun a ha => hs.2 a (mem_of_mem_erase ha)⟩
  · exact hi

/-- A join-stable class of chains has vanishing alternating sum. -/
theorem alternating_chain_sum_zero {allowed : α → Prop} {P : α} (hP : P ≠ ⊥)
    (hbot : allowed ⊥) (hjoin : ∀ q, allowed q → allowed (q ⊔ P)) :
    ∑ s ∈ chains allowed, (-1 : ℤ) ^ s.card = 0 := by
  classical
  apply Finset.sum_involution (fun s _ => toggle P s)
  · intro s hs
    unfold toggle
    split_ifs with hr
    · have hc := Finset.card_erase_add_one hr
      rw [← hc, pow_succ]
      ring
    · rw [Finset.card_insert_of_notMem hr, pow_succ]
      ring
  · intro s hs hn he
    have hm := congrArg (fun t : Finset α => inserted P s ∈ t) he
    by_cases hr : inserted P s ∈ s <;> simp [toggle, hr] at hm
  · intro s hs
    have ha : Admissible allowed s := (mem_filter.mp hs).2
    exact mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), toggle_admissible hP hbot hjoin ha⟩
  · intro s hs
    exact toggle_twice P s
end FiniteChain

end OAI
