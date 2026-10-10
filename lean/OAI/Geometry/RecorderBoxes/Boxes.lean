import Mathlib
import OAI.Analysis.RecorderRadix.Tape

namespace OAI

/-! Filled prefix rectangles and normalized separation gaps. -/

namespace Solenoidal
namespace Bridge
@[ext] structure Rectangle where
  lower : ℝ × ℝ
  upper : ℝ × ℝ

def Rectangle.carrier (P : Rectangle) : Set (ℝ × ℝ) :=
  Set.Icc P.lower.1 P.upper.1 ×ˢ Set.Icc P.lower.2 P.upper.2

 
def Rectangle.SeparatedBy (δ : ℝ) (P Q : Rectangle) : Prop :=
  (P.upper.1 + δ ≤ Q.lower.1 ∨ Q.upper.1 + δ ≤ P.lower.1) ∨
  (P.upper.2 + δ ≤ Q.lower.2 ∨ Q.upper.2 + δ ≤ P.lower.2)

def Rectangle.InUnit (P : Rectangle) : Prop :=
  0 ≤ P.lower.1 ∧ P.lower.1 ≤ P.upper.1 ∧ P.upper.1 ≤ 1 ∧
  0 ≤ P.lower.2 ∧ P.lower.2 ≤ P.upper.2 ∧ P.upper.2 ≤ 1

theorem Rectangle.gap_mono {δ ε : ℝ} {P Q : Rectangle} (h : P.SeparatedBy ε Q)
    (hδε : δ ≤ ε) : P.SeparatedBy δ Q := by
  rcases h with (h | h) | (h | h)
  · exact .inl (.inl (le_trans (by linarith) h))
  · exact .inl (.inr (le_trans (by linarith) h))
  · exact .inr (.inl (le_trans (by linarith) h))
  · exact .inr (.inr (le_trans (by linarith) h))

 

theorem Rectangle.disjoint_of_gap {δ : ℝ} {P Q : Rectangle} (hδ : 0 < δ)
    (h : P.SeparatedBy δ Q) : Disjoint P.carrier Q.carrier := by
  apply Set.disjoint_left.mpr
  intro p hp hq
  change (P.lower.1 ≤ p.1 ∧ p.1 ≤ P.upper.1) ∧
    (P.lower.2 ≤ p.2 ∧ p.2 ≤ P.upper.2) at hp
  change (Q.lower.1 ≤ p.1 ∧ p.1 ≤ Q.upper.1) ∧
    (Q.lower.2 ≤ p.2 ∧ p.2 ≤ Q.upper.2) at hq
  rcases h with (h | h) | (h | h) <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2,
    hq.1.1, hq.1.2, hq.2.1, hq.2.2]

noncomputable def sourceBox {m : ℕ} (a l : Fin (m + 1)) : Rectangle :=
  ⟨(Radix.pushDigit l 0, Radix.pushDigit a 0),
    (Radix.pushDigit l 1, Radix.pushDigit a 1)⟩

noncomputable def targetBox {m : ℕ} (b l : Fin (m + 1)) : Move → Rectangle
  | .right => ⟨(Radix.pushDigit b (Radix.pushDigit l 0), 0),
      (Radix.pushDigit b (Radix.pushDigit l 1), 1)⟩
  | .stay => sourceBox b l
  | .left => ⟨(0, Radix.pushDigit l (Radix.pushDigit b 0)),
      (1, Radix.pushDigit l (Radix.pushDigit b 1))⟩

@[simp] theorem sourceBox_carrier {m : ℕ} (a l : Fin (m + 1)) :
    (sourceBox a l).carrier = Radix.source a l := rfl

@[simp] theorem targetBox_carrier {m : ℕ} (b l : Fin (m + 1)) (d : Move) :
    (targetBox b l d).carrier = Radix.target b l d := by
  cases d <;> rfl

theorem first_bounds {m : ℕ} (a : Fin (m + 1)) :
    0 ≤ Radix.pushDigit a 0 ∧ Radix.pushDigit a 0 ≤ Radix.pushDigit a 1 ∧
      Radix.pushDigit a 1 ≤ 1 :=
  ⟨Radix.lower_nonneg a, (Radix.prefix_le_prefix_iff a).mpr (by norm_num),
    Radix.upper_le_one a⟩

theorem two_bounds {m : ℕ} (a b : Fin (m + 1)) :
    0 ≤ Radix.pushDigit a (Radix.pushDigit b 0) ∧
      Radix.pushDigit a (Radix.pushDigit b 0) ≤ Radix.pushDigit a (Radix.pushDigit b 1) ∧
      Radix.pushDigit a (Radix.pushDigit b 1) ≤ 1 := by
  have ha := first_bounds a
  have hb := first_bounds b
  exact ⟨ha.1.trans ((Radix.prefix_le_prefix_iff a).mpr hb.1),
    (Radix.prefix_le_prefix_iff a).mpr hb.2.1,
    ((Radix.prefix_le_prefix_iff a).mpr hb.2.2).trans ha.2.2⟩

theorem source_in_unit {m : ℕ} (a l : Fin (m + 1)) : (sourceBox a l).InUnit :=
  ⟨(first_bounds l).1, (first_bounds l).2.1, (first_bounds l).2.2,
    (first_bounds a).1, (first_bounds a).2.1, (first_bounds a).2.2⟩

theorem target_in_unit {m : ℕ} (b l : Fin (m + 1)) (d : Move) :
    (targetBox b l d).InUnit := by
  cases d with
  | stay => exact source_in_unit b l
  | left => exact ⟨le_refl _, by norm_num [targetBox], le_refl _,
      (two_bounds l b).1, (two_bounds l b).2.1, (two_bounds l b).2.2⟩
  | right => exact ⟨(two_bounds b l).1, (two_bounds b l).2.1, (two_bounds b l).2.2,
      le_refl _, by norm_num [targetBox], le_refl _⟩

theorem inverse_square_le_inverse (m : ℕ) : 1 / Radix.base m ^ 2 ≤ 1 / Radix.base m := by
  apply one_div_le_one_div_of_le (Radix.base_pos m)
  have := Radix.base_three_le m
  nlinarith

 
theorem normalized_source_gap {m : ℕ} {a l a' l' : Fin (m + 1)}
    (hne : (a, l) ≠ (a', l')) :
    (sourceBox a l).SeparatedBy (1 / Radix.base m) (sourceBox a' l') := by
  by_cases hl : l = l'
  · have ha : a ≠ a' := fun he => hne (Prod.ext he hl)
    exact .inr (Radix.first_separated ha)
  · exact .inl (Radix.first_separated hl)

 

theorem normalized_target_gap {m : ℕ} {b l b' l' : Fin (m + 1)}
    (hne : (b, l) ≠ (b', l')) (d : Move) :
    (targetBox b l d).SeparatedBy (1 / Radix.base m ^ 2) (targetBox b' l' d) := by
  cases d with
  | right => exact .inl (Radix.two_separated hne)
  | left =>
    exact .inr (Radix.two_separated (by
      intro he
      exact hne (Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he))))
  | stay => exact Rectangle.gap_mono (normalized_source_gap hne) (inverse_square_le_inverse m)
end Bridge
end Solenoidal

end OAI
