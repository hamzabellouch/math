import OAI.Combinatorics.EditDistance.RecursiveWords

namespace OAI

/-!
# Length, alphabet, and distortion recurrences for word families
-/

namespace EditFamily
open scoped BigOperators

def familyLength (b P s : ℕ) : ℕ := (2 * (2 * b - 1) * P ^ (b / 2)) ^ s

def familyAlphabet (b P : ℕ) : ℕ → ℕ
  | 0 => 2 * P
  | s+1 => 1 + (2 * b - 1) * familyAlphabet b P s

noncomputable def familyAlpha (s : ℕ) : ℝ := (24 : ℝ)⁻¹ ^ s

noncomputable def familyBudget (b P h : ℕ) : ℕ → ℝ
  | 0 => 2
  | s+1 => 2 * (2 * (P : ℝ)) ^ (2 * h) / (P ^ (b / 2) : ℕ) + familyBudget b P h s / h

lemma familyLength_pos {b P : ℕ} (hb : 0 < b) (hP : 0 < P) (s : ℕ) :
    0 < familyLength b P s := by
  unfold familyLength
  exact pow_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (pow_pos hP _)) _

lemma familyAlpha_pos (s : ℕ) : 0 < familyAlpha s := by
  unfold familyAlpha
  positivity

lemma familyAlpha_le_one (s : ℕ) : familyAlpha s ≤ 1 := by
  unfold familyAlpha
  exact pow_le_one₀ (by norm_num) (by norm_num)

lemma familyBudget_nonneg (b P h s : ℕ) : 0 ≤ familyBudget b P h s := by
  induction s with
  | zero => norm_num [familyBudget]
  | succ s ih =>
      exact add_nonneg (by positivity) (div_nonneg ih (Nat.cast_nonneg _))

noncomputable def recursive {J : Type} [Fintype J] [DecidableEq J]
    (p : J → ℕ) (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    (P : ℕ) (hP : 1 ≤ P) (hpLow : ∀ j, P ≤ p j) (hpHigh : ∀ j, p j ≤ 2 * P)
    (h : ℕ) (hh : 0 < h) : (s : ℕ) → (j : J) →
    Family (p j) (familyLength (Fintype.card J) P s) (familyAlphabet (Fintype.card J) P s)
      (familyAlpha s) (familyBudget (Fintype.card J) P h s)
  | 0, j => base (hp j) (hpHigh j)
  | s+1, j => by
      let F := recursive p hp hinj P hP hpLow hpHigh h hh s
      have hn : familyLength (Fintype.card J) P (s+1) =
          2 * ((2 * Fintype.card J - 1) * familyLength (Fintype.card J) P s) *
            P ^ (Fintype.card J / 2) := by
        simp only [familyLength, pow_succ]
        ring
      have ha : familyAlpha (s+1) = familyAlpha s / 24 := by
        simp only [familyAlpha, pow_succ, div_eq_mul_inv]
      rw [hn, familyAlphabet, ha, familyBudget]
      exact successor j F hp hinj P hP hpLow hpHigh
        (familyLength_pos (Fintype.card_pos_iff.mpr ⟨j⟩) (by omega) s)
        (familyAlpha_pos s).le (familyAlpha_le_one s)
        (familyBudget_nonneg _ _ _ _) h hh

lemma familyAlphabet_pos {b P : ℕ} (hP : 0 < P) (s : ℕ) : 0 < familyAlphabet b P s := by
  cases s <;> simp only [familyAlphabet] <;> omega

lemma familyAlphabet_le {b P : ℕ} (hb : 0 < b) (hP : 0 < P) (s : ℕ) :
    familyAlphabet b P s ≤ (2 * P + 1) * (2 * b) ^ s := by
  induction s with
  | zero => simp [familyAlphabet]
  | succ s ih =>
      have hap := familyAlphabet_pos (b := b) hP s
      have hb' : 2 * b - 1 + 1 = 2 * b := by omega
      calc
        familyAlphabet b P (s+1) = 1 + (2 * b - 1) * familyAlphabet b P s := rfl
        _ ≤ 2 * b * familyAlphabet b P s := by
          nlinarith [Nat.mul_add (2 * b - 1) 1 (familyAlphabet b P s)]
        _ ≤ 2 * b * ((2 * P + 1) * (2 * b) ^ s) := Nat.mul_le_mul_left _ ih
        _ = (2 * P + 1) * (2 * b) ^ (s+1) := by rw [pow_succ]; ring

end EditFamily

end OAI
