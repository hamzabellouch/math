import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseSelect

namespace OAI

section Inline_PCPLinearity

namespace MetricKMedian.PCP
open Finset

section Linearity
variable {G H : Type} [AddCommGroup G] [Fintype G] [AddCommGroup H] [DecidableEq H]

def derivative (f : G → H) (x y : G) : H := f (x + y) - f y

noncomputable def linearityRejects (f : G → H) : ℕ := by
  classical
  exact (univ.filter (fun p : G × G => f (p.1 + p.2) ≠ f p.1 + f p.2)).card

noncomputable def correctionErrors (f : G → H) (x : G) (a : H) : ℕ := by
  classical
  exact (univ.filter (fun y : G => derivative f x y ≠ a)).card

private theorem exists_best_anchor (f : G → H) (x : G) :
    ∃ y : G, ∀ z : G, correctionErrors f x (derivative f x y) ≤
      correctionErrors f x (derivative f x z) := by
  classical
  obtain ⟨y, _, hy⟩ := univ.exists_min_image
    (fun z : G => correctionErrors f x (derivative f x z))
    (show (univ : Finset G).Nonempty from ⟨0, mem_univ 0⟩)
  exact ⟨y, fun z => hy z (mem_univ z)⟩

noncomputable def corrected (f : G → H) (x : G) : H :=
  derivative f x (Classical.choose (exists_best_anchor f x))

theorem corrected_min (f : G → H) (x y : G) :
    correctionErrors f x (corrected f x) ≤
      correctionErrors f x (derivative f x y) :=
  (Classical.choose_spec (exists_best_anchor f x)) y

def derivativePairEquiv (x : G) : (G × G) ≃ (G × G) where
  toFun p := (x + p.1, p.2 - p.1)
  invFun q := (q.1 - x, q.2 + q.1 - x)
  left_inv p := by ext <;> dsimp <;> abel
  right_inv q := by ext <;> dsimp <;> abel

private theorem shifted_reject_count (f : G → H) (x : G) :
    (univ.filter (fun p : G × G =>
      f (x + p.2) ≠ f (x + p.1) + f (p.2 - p.1))).card =
      linearityRejects f := by
  classical
  apply card_equiv (derivativePairEquiv x)
  intro p
  simp only [mem_filter, mem_univ, true_and, derivativePairEquiv,
    Equiv.coe_fn_mk]
  abel_nf

private theorem different_derivatives_bound (f : G → H) (x : G) :
    (univ.filter (fun p : G × G => derivative f x p.1 ≠ derivative f x p.2)).card ≤
      2 * linearityRejects f := by
  classical
  let A := univ.filter (fun p : G × G =>
    f (x + p.2) ≠ f (x + p.1) + f (p.2 - p.1))
  let B := univ.filter (fun p : G × G => f p.2 ≠ f p.1 + f (p.2 - p.1))
  have hsub : (univ.filter (fun p : G × G =>
      derivative f x p.1 ≠ derivative f x p.2)) ⊆ A ∪ B := by
    intro p hp
    simp only [mem_filter, mem_univ, true_and, mem_union, A, B] at hp ⊢
    by_contra h
    push Not at h
    apply hp
    simp only [derivative, h.1, h.2]
    abel
  have hA : A.card = linearityRejects f := shifted_reject_count f x
  have hB : B.card = linearityRejects f := by
    simpa only [zero_add] using shifted_reject_count f (0 : G)
  calc
    _ ≤ (A ∪ B).card := card_le_card hsub
    _ ≤ A.card + B.card := card_union_le _ _
    _ = _ := by rw [hA, hB]; omega

theorem correction_error_bound (f : G → H) (x : G) :
    Fintype.card G * correctionErrors f x (corrected f x) ≤
      2 * linearityRejects f := by
  classical
  have hsum : (∑ y : G, correctionErrors f x (derivative f x y)) =
      (univ.filter (fun p : G × G => derivative f x p.1 ≠ derivative f x p.2)).card := by
    simp only [correctionErrors, card_filter, Fintype.sum_prod_type]
    apply sum_congr rfl
    intro y _
    apply sum_congr rfl
    intro z _
    simp only [ne_comm]
  calc
    _ = ∑ _y : G, correctionErrors f x (corrected f x) := by simp
    _ ≤ ∑ y : G, correctionErrors f x (derivative f x y) := by
      exact sum_le_sum (fun y _ => corrected_min f x y)
    _ ≤ _ := by rw [hsum]; exact different_derivatives_bound f x

private theorem count_translate (p : G → Prop) [DecidablePred p] (y : G) :
    (univ.filter (fun z => p (y + z))).card = (univ.filter p).card := by
  classical
  exact card_equiv (Equiv.addLeft y) (by simp)

omit [AddCommGroup G] in
private theorem card_le_of_three_cover (p q r : G → Prop)
    [DecidablePred p] [DecidablePred q] [DecidablePred r]
    (h : ∀ z, p z ∨ q z ∨ r z) :
    Fintype.card G ≤ (univ.filter p).card + (univ.filter q).card +
      (univ.filter r).card := by
  classical
  have hs : (univ : Finset G) ⊆ (univ.filter p ∪ univ.filter q) ∪ univ.filter r := by
    intro z _
    simpa only [mem_union, mem_filter, mem_univ, true_and, or_assoc] using h z
  have h₁ := card_union_le (univ.filter p ∪ univ.filter q) (univ.filter r)
  have h₂ := card_union_le (univ.filter p) (univ.filter q)
  have h₃ := card_le_card hs
  simp only [card_univ] at h₃
  omega

theorem corrected_add (f : G → H)
    (hsmall : 6 * linearityRejects f < Fintype.card G * Fintype.card G)
    (x y : G) : corrected f (x + y) = corrected f x + corrected f y := by
  classical
  by_contra hbad
  have hc : ∀ z : G,
      derivative f (x+y) z ≠ corrected f (x+y) ∨
      derivative f x (y+z) ≠ corrected f x ∨
      derivative f y z ≠ corrected f y := by
    intro z
    by_contra hz
    push Not at hz
    apply hbad
    rw [← hz.1, ← hz.2.1, ← hz.2.2]
    dsimp [derivative]
    rw [add_assoc]
    abel
  have hh := card_le_of_three_cover _ _ _ hc
  rw [count_translate (fun z => derivative f x z ≠ corrected f x) y] at hh
  change Fintype.card G ≤ correctionErrors f (x+y) (corrected f (x+y)) +
    correctionErrors f x (corrected f x) + correctionErrors f y (corrected f y) at hh
  have hm := Nat.mul_le_mul_left (Fintype.card G) hh
  have hxy := correction_error_bound f (x+y)
  have hx := correction_error_bound f x
  have hy := correction_error_bound f y
  nlinarith

noncomputable def correctedHom (f : G → H)
    (hsmall : 6 * linearityRejects f < Fintype.card G * Fintype.card G) : G →+ H where
  toFun := corrected f
  map_zero' := by
    have h := corrected_add f hsmall 0 0
    simp only [zero_add] at h
    exact (add_left_cancel (a := corrected f 0) (by simpa using h.symm))
  map_add' := corrected_add f hsmall

noncomputable def tableErrors (f g : G → H) : ℕ := by
  classical
  exact (univ.filter (fun x => f x ≠ g x)).card

private theorem sum_point_rejects (f : G → H) :
    (∑ x : G, correctionErrors f x (f x)) = linearityRejects f := by
  classical
  unfold linearityRejects
  rw [card_filter, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro x _
  unfold correctionErrors
  rw [card_filter]
  apply sum_congr rfl
  intro y _
  simp only [derivative, ne_eq, sub_eq_iff_eq_add]

theorem corrected_close (f : G → H)
    (hsmall : 6 * linearityRejects f < Fintype.card G * Fintype.card G) :
    Fintype.card G * tableErrors f (corrected f) ≤ 2 * linearityRejects f := by
  classical
  have hN : 0 < Fintype.card G := Fintype.card_pos
  have half (x : G) : 2 * correctionErrors f x (corrected f x) ≤ Fintype.card G := by
    have hb := correction_error_bound f x
    nlinarith
  have bad (x : G) (hx : f x ≠ corrected f x) :
      Fintype.card G ≤ 2 * correctionErrors f x (f x) := by
    have hc : ∀ y : G, (derivative f x y ≠ f x) ∨
        (derivative f x y ≠ corrected f x) ∨ False := by
      intro y
      by_contra h
      push Not at h
      exact hx (h.1.symm.trans h.2.1)
    have hh := card_le_of_three_cover _ _ _ hc
    simp only [filter_false, card_empty, add_zero] at hh
    change Fintype.card G ≤ correctionErrors f x (f x) +
      correctionErrors f x (corrected f x) at hh
    have hh' := half x
    omega
  let B := univ.filter (fun x => f x ≠ corrected f x)
  calc
    _ = ∑ _x ∈ B, Fintype.card G := by simp [tableErrors, B, mul_comm]
    _ ≤ ∑ x ∈ B, 2 * correctionErrors f x (f x) := by
      apply sum_le_sum
      intro x hx
      exact bad x (mem_filter.mp hx).2
    _ ≤ ∑ x : G, 2 * correctionErrors f x (f x) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; omega)
    _ = _ := by rw [← mul_sum, sum_point_rejects]

theorem linearity_test_sound (f : G → H)
    (hsmall : 6 * linearityRejects f < Fintype.card G * Fintype.card G) :
    ∃ g : G →+ H, Fintype.card G * tableErrors f g ≤ 2 * linearityRejects f :=
  ⟨correctedHom f hsmall, corrected_close f hsmall⟩

theorem linearity_test_complete (f : G →+ H) : linearityRejects f = 0 := by
  classical
  simp [linearityRejects]

end Linearity
end MetricKMedian.PCP

end Inline_PCPLinearity

end OAI
