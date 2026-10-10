import Mathlib

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
attribute [local instance] Classical.propDecidable

/-- Identifying two classes, without making any other identifications. -/
def glue {D : Type*} (s : Setoid D) (a b : D) : Setoid D := by
  classical
  exact Setoid.ker (fun x => if (Quotient.mk s x : Quotient s) = Quotient.mk s b
    then Quotient.mk s a else Quotient.mk s x)

variable {D : Type*} (s : Setoid D) (a b : D)

lemma glue_iff (x y : D) : glue s a b x y ↔
    (if s x b then (Quotient.mk s a : Quotient s) else Quotient.mk s x) =
    (if s y b then (Quotient.mk s a : Quotient s) else Quotient.mk s y) := by
  classical
  change ((if (Quotient.mk s x : Quotient s) = Quotient.mk s b then Quotient.mk s a else Quotient.mk s x) =
    (if (Quotient.mk s y : Quotient s) = Quotient.mk s b then Quotient.mk s a else Quotient.mk s y)) ↔ _
  simp only [Quotient.eq]

lemma le_glue : s ≤ glue s a b := by
  classical
  intro x y h
  rw [glue_iff]
  have ee : (Quotient.mk s x : Quotient s) = Quotient.mk s y := Quotient.sound h
  have hh : s x b ↔ s y b := ⟨fun hx => s.trans' (s.symm' h) hx,fun hy => s.trans' h hy⟩
  simp only [hh,ee]

lemma glue_pair : glue s a b a b := by
  classical
  rw [glue_iff]
  simp

lemma glue_le {t : Setoid D} (hs : s ≤ t) (hab : t a b) : glue s a b ≤ t := by
  classical
  intro x y h
  rw [glue_iff] at h
  split_ifs at h with hx hy hy
  · exact t.trans' (hs hx) (t.symm' (hs hy))
  · exact t.trans' (t.trans' (hs hx) (t.symm' hab)) (hs (Quotient.exact h))
  · exact t.trans' (t.trans' (hs (Quotient.exact h)) hab) (t.symm' (hs hy))
  · exact hs (Quotient.exact h)

lemma glue_eq_of_rel (h : s a b) : glue s a b = s :=
  le_antisymm (glue_le s a b le_rfl h) (le_glue s a b)

lemma glue_monotone {t : Setoid D} (h : s ≤ t) : glue s a b ≤ glue t a b :=
  glue_le s a b (h.trans (le_glue t a b)) (glue_pair t a b)

section Finite
variable [Finite D]

/-- Exactly one component is lost when previously distinct classes are glued. -/
theorem card_glue_of_not_rel (h : ¬ s a b) :
    Nat.card (Quotient (glue s a b)) + 1 = Nat.card (Quotient s) := by
  classical
  let qa : Quotient s := Quotient.mk s a
  let qb : Quotient s := Quotient.mk s b
  have hn : qa ≠ qb := fun he => h (Quotient.exact he)
  let f : D → {q : Quotient s // q ≠ qb} := fun x =>
    ⟨if (Quotient.mk s x : Quotient s) = qb then qa else Quotient.mk s x,
      by split_ifs with hx <;> assumption⟩
  have hf : Function.Surjective f := by
    rintro ⟨q,hq⟩
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective q
    refine ⟨x,Subtype.ext ?_⟩
    exact ite_eq_right hq
  have hk : Setoid.ker f = glue s a b := by
    ext x y
    change (f x = f y) ↔ ((if (Quotient.mk s x : Quotient s) = qb then qa else Quotient.mk s x) =
      (if (Quotient.mk s y : Quotient s) = qb then qa else Quotient.mk s y))
    simp only [f,Subtype.mk.injEq]
  have hc := Nat.card_congr (Setoid.quotientKerEquivOfSurjective f hf)
  rw [hk] at hc
  rw [hc]
  let := Fintype.ofFinite (Quotient s)
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  have hpos : 0 < Fintype.card (Quotient s) := Fintype.card_pos_iff.mpr ⟨qa⟩
  simp only [Fintype.card_unique]
  omega

/-- A uniformly phrased count, including the already-related case. -/
theorem card_glue : (Nat.card (Quotient (glue s a b)) : ℤ) =
    Nat.card (Quotient s) - if s a b then 0 else 1 := by
  classical
  by_cases h : s a b
  · rw [glue_eq_of_rel s a b h,ite_eq_left h,sub_zero]
  · rw [ite_eq_right h]
    have hc := card_glue_of_not_rel s a b h
    omega

end Finite
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
