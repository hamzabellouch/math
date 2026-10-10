import OAI.MeasureTheory.Falconer.Estimates.DyadicTree
import Mathlib.Data.Nat.Log

namespace OAI

/-!
# Upward regularization labels in arbitrary dimension

The label-preservation argument applies to all-dimensional dyadic paths.
Each extension retains or removes a whole previous child group.
-/

namespace Falconer.Regularization

abbrev CellPath (d : ℕ) := List (Fin d → Bool)
variable {d : ℕ}

noncomputable def labeledChildren (L : Finset (CellPath d)) (f : CellPath d → List ℕ)
    (a b : ℕ) (p : CellPath d) : Finset (CellPath d) := by
  classical
  exact (L.filter fun q => q.take a = p.take a ∧ f q = f p).image (List.take b)

noncomputable def extendLabel (L : Finset (CellPath d)) (a b : ℕ)
    (f : CellPath d → List ℕ) (p : CellPath d) : List ℕ :=
  Nat.log 2 (labeledChildren L f a b p).card :: f p

noncomputable def upwardLabels (L : Finset (CellPath d)) :
    List (ℕ × ℕ) → (CellPath d → List ℕ) → CellPath d → List ℕ
  | [], f => f
  | (a,b) :: steps, f => upwardLabels L steps (extendLabel L a b f)

theorem take_eq_of_take_eq {p q : CellPath d} {a c : ℕ}
    (hc : c ≤ a) (h : p.take a = q.take a) : p.take c = q.take c := by
  have := congrArg (List.take c) h
  simpa only [List.take_take, Nat.min_eq_left hc] using this

theorem labeledChildren_eq {L : Finset (CellPath d)} {f : CellPath d → List ℕ}
    {a b : ℕ} {p q : CellPath d} (ha : p.take a = q.take a) (hf : f p = f q) :
    labeledChildren L f a b p = labeledChildren L f a b q := by
  classical
  simp only [labeledChildren, ha, hf]

theorem labeledChildren_nonempty {L : Finset (CellPath d)} (f : CellPath d → List ℕ)
    (a b : ℕ) {p : CellPath d} (hp : p ∈ L) :
    (labeledChildren L f a b p).Nonempty := by
  classical
  exact Finset.image_nonempty.mpr ⟨p, by simp [hp]⟩

theorem extendLabel_old {L : Finset (CellPath d)} {f : CellPath d → List ℕ}
    {a b : ℕ} {p q : CellPath d} (h : extendLabel L a b f p = extendLabel L a b f q) :
    f p = f q := (List.cons.inj h).2

theorem extendLabel_local {L : Finset (CellPath d)} {f : CellPath d → List ℕ}
    {a b : ℕ} {p q : CellPath d} (ha : p.take a = q.take a) :
    extendLabel L a b f p = extendLabel L a b f q ↔ f p = f q := by
  constructor
  · exact extendLabel_old
  · intro hf
    simp only [extendLabel, labeledChildren_eq ha hf, hf]

theorem upwardLabels_old (L : Finset (CellPath d)) (steps : List (ℕ × ℕ))
    (f : CellPath d → List ℕ) {p q : CellPath d}
    (h : upwardLabels L steps f p = upwardLabels L steps f q) : f p = f q := by
  induction steps generalizing f with
  | nil => exact h
  | cons s steps ih => exact extendLabel_old (ih _ h)

theorem upwardLabels_local (L : Finset (CellPath d)) (steps : List (ℕ × ℕ))
    (f : CellPath d → List ℕ) {a : ℕ} (hsteps : ∀ s ∈ steps, s.1 ≤ a)
    {p q : CellPath d} (ha : p.take a = q.take a) :
    upwardLabels L steps f p = upwardLabels L steps f q ↔ f p = f q := by
  induction steps generalizing f with
  | nil => rfl
  | cons s steps ih =>
    rw [upwardLabels, ih _ (fun t ht => hsteps t (by simp [ht]))]
    exact extendLabel_local (take_eq_of_take_eq (hsteps s (by simp)) ha)

theorem final_labeledChildren_eq (L : Finset (CellPath d)) (f : CellPath d → List ℕ)
    (a b : ℕ) (steps : List (ℕ × ℕ)) (hsteps : ∀ s ∈ steps, s.1 ≤ a)
    (p : CellPath d) :
    labeledChildren L (upwardLabels L steps (extendLabel L a b f)) a b p =
      labeledChildren L f a b p := by
  classical
  apply congrArg (Finset.image (List.take b))
  apply Finset.filter_congr
  intro q _
  constructor
  · rintro ⟨ha,hf⟩
    exact ⟨ha, extendLabel_old (upwardLabels_old L steps _ hf)⟩
  · rintro ⟨ha,hf⟩
    exact ⟨ha,(upwardLabels_local L steps _ hsteps ha).mpr
      ((extendLabel_local ha).mpr hf)⟩

theorem final_child_count_bin (L : Finset (CellPath d)) (f : CellPath d → List ℕ)
    (a b : ℕ) (steps : List (ℕ × ℕ)) (hsteps : ∀ s ∈ steps, s.1 ≤ a)
    {p q : CellPath d}
    (hclass : upwardLabels L steps (extendLabel L a b f) p =
      upwardLabels L steps (extendLabel L a b f) q) :
    Nat.log 2 (labeledChildren L (upwardLabels L steps (extendLabel L a b f)) a b p).card =
      Nat.log 2 (labeledChildren L (upwardLabels L steps (extendLabel L a b f)) a b q).card := by
  rw [final_labeledChildren_eq L f a b steps hsteps,
    final_labeledChildren_eq L f a b steps hsteps]
  exact (List.cons.inj (upwardLabels_old L steps _ hclass)).1

theorem final_child_count_bounds (L : Finset (CellPath d)) (f : CellPath d → List ℕ)
    (a b : ℕ) (steps : List (ℕ × ℕ)) (hsteps : ∀ s ∈ steps, s.1 ≤ a)
    {p q : CellPath d} (hq : q ∈ L)
    (hclass : upwardLabels L steps (extendLabel L a b f) p =
      upwardLabels L steps (extendLabel L a b f) q) :
    let F := upwardLabels L steps (extendLabel L a b f)
    let B := 2 ^ Nat.log 2 (labeledChildren L F a b p).card
    0 < B ∧ B ≤ (labeledChildren L F a b q).card ∧
      (labeledChildren L F a b q).card < 2 * B := by
  dsimp only
  rw [final_child_count_bin L f a b steps hsteps hclass]
  have hp := Finset.card_pos.mpr (labeledChildren_nonempty
    (upwardLabels L steps (extendLabel L a b f)) a b hq)
  refine ⟨by positivity, Nat.pow_log_le_self 2 (by omega), ?_⟩
  simpa only [pow_succ, Nat.mul_comm] using Nat.lt_pow_succ_log_self (by omega : 1 < 2)
    (labeledChildren L (upwardLabels L steps (extendLabel L a b f)) a b q).card

end Falconer.Regularization

end OAI
