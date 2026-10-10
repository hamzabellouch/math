import Mathlib
import OAI.Geometry.RecorderBoxes.Branches

namespace OAI

/-! Separated state-square placement of recorder controls. -/

namespace Solenoidal
namespace Bridge
variable {M : Machine}
def terminalControl : Recorder.Control M → Bool
  | .S q => M.halt q
  | _ => false

abbrev controlCount (M : Machine) : ℕ := Fintype.card (Recorder.Control M)

 

noncomputable def controlIndex (M : Machine) : Recorder.Control M ≃ Fin (controlCount M) :=
  Fintype.equivFin _

theorem controlCount_pos (M : Machine) : 0 < controlCount M :=
  Fintype.card_pos_iff.mpr ⟨.S M.initial⟩

noncomputable def kappa (M : Machine) : ℝ := 1 / (32 * (controlCount M : ℝ))

theorem kappa_pos (M : Machine) : 0 < kappa M :=
  one_div_pos.mpr (mul_pos (by norm_num) (by exact_mod_cast controlCount_pos M))

theorem kappa_le (M : Machine) : kappa M ≤ 1 / 32 := by
  apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 32)
  have hN : (1 : ℝ) ≤ controlCount M := by exact_mod_cast controlCount_pos M
  nlinarith

noncomputable def origin (s : Recorder.Control M) : ℝ :=
  (if terminalControl s then 3 / 4 else 1 / 8) +
    2 * ((controlIndex M s).val : ℝ) * kappa M

 
theorem state_extent (s : Recorder.Control M) :
    (if terminalControl s then (3 / 4 : ℝ) else 1 / 8) ≤ origin s ∧
    origin s + kappa M < (if terminalControl s then (13 / 16 : ℝ) else 3 / 16) := by
  have hk := kappa_pos M
  have h₀ : (0 : ℝ) ≤ (controlIndex M s).val := Nat.cast_nonneg _
  have hN : (↑(controlIndex M s).val : ℝ) + 1 ≤ controlCount M := by
    exact_mod_cast (controlIndex M s).isLt
  have hprod : 2 * (controlCount M : ℝ) * kappa M = 1 / 16 := by
    dsimp only [kappa]
    have hn : (controlCount M : ℝ) ≠ 0 := by
      exact_mod_cast (controlCount_pos M).ne'
    field_simp
    norm_num
  have hscaled := mul_le_mul_of_nonneg_right hN hk.le
  have hnonneg := mul_nonneg h₀ hk.le
  dsimp only [origin]
  cases terminalControl s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    constructor <;> nlinarith

 
theorem state_gap {s t : Recorder.Control M} (hne : s ≠ t) :
    (origin s + kappa M) + kappa M ≤ origin t ∨
    (origin t + kappa M) + kappa M ≤ origin s := by
  have hk := kappa_pos M
  by_cases he : terminalControl s = terminalControl t
  · have hidx : (controlIndex M s).val ≠ (controlIndex M t).val := by
      intro hi
      exact hne ((controlIndex M).injective (Fin.ext hi))
    rcases lt_or_gt_of_ne hidx with hi | hi
    · left
      have hi' : (↑(controlIndex M s).val : ℝ) + 1 ≤ (controlIndex M t).val := by
        exact_mod_cast hi
      have hm := mul_le_mul_of_nonneg_right hi' hk.le
      dsimp only [origin]
      rw [he]
      nlinarith
    · right
      have hi' : (↑(controlIndex M t).val : ℝ) + 1 ≤ (controlIndex M s).val := by
        exact_mod_cast hi
      have hm := mul_le_mul_of_nonneg_right hi' hk.le
      dsimp only [origin]
      rw [he]
      nlinarith
  · have hs := state_extent s
    have ht := state_extent t
    have hκ := kappa_le M
    cases es : terminalControl s <;> cases et : terminalControl t
    · exact False.elim (he (es.trans et.symm))
    · simp only [es, Bool.false_eq_true, ↓reduceIte] at hs
      simp only [et, ↓reduceIte] at ht
      left; linarith
    · simp only [es, ↓reduceIte] at hs
      simp only [et, Bool.false_eq_true, ↓reduceIte] at ht
      right; linarith
    · exact False.elim (he (es.trans et.symm))

 
noncomputable def place (s : Recorder.Control M) (p : ℝ × ℝ) : ℝ × ℝ :=
  (origin s + kappa M * p.1, 3 / 8 + kappa M * p.2)

noncomputable def unplace (s : Recorder.Control M) (p : ℝ × ℝ) : ℝ × ℝ :=
  ((p.1 - origin s) / kappa M, (p.2 - 3 / 8) / kappa M)

@[simp] theorem unplace_place (s : Recorder.Control M) (p : ℝ × ℝ) :
    unplace s (place s p) = p := by
  apply Prod.ext <;> dsimp [unplace, place] <;> field_simp [(kappa_pos M).ne'] <;> ring

@[simp] theorem place_unplace (s : Recorder.Control M) (p : ℝ × ℝ) :
    place s (unplace s p) = p := by
  apply Prod.ext <;> dsimp [unplace, place] <;> field_simp [(kappa_pos M).ne'] <;> ring

noncomputable def physicalBox (s : Recorder.Control M) (P : Rectangle) : Rectangle :=
  ⟨place s P.lower, place s P.upper⟩

 
theorem physicalBox_carrier (s : Recorder.Control M) (P : Rectangle) :
    (physicalBox s P).carrier = place s '' P.carrier := by
  ext q
  constructor
  · intro hq
    refine ⟨unplace s q, ?_, place_unplace s q⟩
    change (P.lower.1 ≤ (q.1 - origin s) / kappa M ∧
      (q.1 - origin s) / kappa M ≤ P.upper.1) ∧
      (P.lower.2 ≤ (q.2 - 3 / 8) / kappa M ∧
      (q.2 - 3 / 8) / kappa M ≤ P.upper.2)
    change (origin s + kappa M * P.lower.1 ≤ q.1 ∧
      q.1 ≤ origin s + kappa M * P.upper.1) ∧
      (3 / 8 + kappa M * P.lower.2 ≤ q.2 ∧
      q.2 ≤ 3 / 8 + kappa M * P.upper.2) at hq
    simp only [le_div_iff₀ (kappa_pos M), div_le_iff₀ (kappa_pos M)]
    constructor <;> constructor <;> nlinarith [hq.1.1, hq.1.2, hq.2.1, hq.2.2]
  · rintro ⟨p, hp, rfl⟩
    change (origin s + kappa M * P.lower.1 ≤ origin s + kappa M * p.1 ∧
      origin s + kappa M * p.1 ≤ origin s + kappa M * P.upper.1) ∧
      (3 / 8 + kappa M * P.lower.2 ≤ 3 / 8 + kappa M * p.2 ∧
      3 / 8 + kappa M * p.2 ≤ 3 / 8 + kappa M * P.upper.2)
    have h₁ := mul_le_mul_of_nonneg_left hp.1.1 (kappa_pos M).le
    have h₂ := mul_le_mul_of_nonneg_left hp.1.2 (kappa_pos M).le
    have h₃ := mul_le_mul_of_nonneg_left hp.2.1 (kappa_pos M).le
    have h₄ := mul_le_mul_of_nonneg_left hp.2.2 (kappa_pos M).le
    constructor <;> constructor <;> linarith

theorem physical_gap_same (s : Recorder.Control M) {P Q : Rectangle} {δ : ℝ}
    (h : P.SeparatedBy δ Q) :
    (physicalBox s P).SeparatedBy (kappa M * δ) (physicalBox s Q) := by
  rcases h with (h | h) | (h | h)
  all_goals have hm := mul_le_mul_of_nonneg_left h (kappa_pos M).le
  · exact .inl (.inl (by dsimp [physicalBox, place]; nlinarith))
  · exact .inl (.inr (by dsimp [physicalBox, place]; nlinarith))
  · exact .inr (.inl (by dsimp [physicalBox, place]; nlinarith))
  · exact .inr (.inr (by dsimp [physicalBox, place]; nlinarith))

theorem physical_gap_different {s t : Recorder.Control M} {P Q : Rectangle}
    (hs : s ≠ t) (hP : P.InUnit) (hQ : Q.InUnit) :
    (physicalBox s P).SeparatedBy (kappa M) (physicalBox t Q) := by
  have hk := kappa_pos M
  have hpU := mul_le_mul_of_nonneg_left hP.2.2.1 hk.le
  have hpL := mul_nonneg hk.le hP.1
  have hqU := mul_le_mul_of_nonneg_left hQ.2.2.1 hk.le
  have hqL := mul_nonneg hk.le hQ.1
  rcases state_gap hs with hst | hst
  · exact .inl (.inl (by dsimp [physicalBox, place]; nlinarith))
  · exact .inl (.inr (by dsimp [physicalBox, place]; nlinarith))
end Bridge
end Solenoidal

end OAI
