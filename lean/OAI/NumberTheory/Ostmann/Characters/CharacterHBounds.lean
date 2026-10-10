import OAI.NumberTheory.Ostmann.Characters.CharacterHCoordinates
import OAI.NumberTheory.Ostmann.Construction.RoundedScheduleRanges

namespace OAI

/-! # Product bounds retain the complete selected word bins -/
namespace Ostmann
open scoped Classical BigOperators
open Filter

theorem character_H_card_le {k n : ℕ} (hn : n < k) :
    Fintype.card (CopyScheduleH (characterRole k) n) ≤ 2 ^ n + k + 2 := by
  rw [← Fintype.card_congr (characterHEquiv hn)]
  change Fintype.card ((Fin n → Bool) ⊕ ({j : Fin k // n < j.val} ⊕ Bool)) ≤ _
  simp only [Fintype.card_sum, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have h := Fintype.card_subtype_le (fun j : Fin k => n < j.val)
  simp only [Fintype.card_fin] at h
  omega

theorem character_H_sum {k n : ℕ} (hn : n < k) (w : CharacterRole k → ℝ) :
    (∑ h : CopyScheduleH (characterRole k) n, w (copyScheduleOrigin n h.val)) =
      (2 : ℝ) ^ n * w (true, none) +
        ((∑ j : {j : Fin k // n < j.val}, w (characterPivotAtom j.val)) +
          ∑ b : Bool, w (characterAnchorAtom ⟨n, hn⟩ b)) := by
  rw [← (characterHEquiv hn).sum_comp]
  change (∑ x : CharacterHIndex k n,
    w (copyScheduleOrigin n (characterHCoordinate hn x).val)) = _
  simp only [characterHCoordinate_origin, Fintype.sum_sum_type, Finset.sum_const,
    Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- A bounded error per selected atom costs only a constant depending on the
fixed depth, not on the number of primes in the word. -/
theorem character_H_product_bounds {k n : ℕ} (hn : n < k)
    (w : CharacterRole k → ℝ) (lo hi : CharacterRole k → ℕ)
    (c : ℝ) (hc : 0 ≤ c)
    (hlo : ∀ i, Real.exp (w i - c) ≤ lo i)
    (hhi : ∀ i, (hi i : ℝ) ≤ Real.exp (w i + c)) :
    let T := (2 : ℝ) ^ n * w (true, none) +
      ((∑ j : {j : Fin k // n < j.val}, w (characterPivotAtom j.val)) +
        ∑ b : Bool, w (characterAnchorAtom ⟨n, hn⟩ b))
    let C := ((2 : ℝ) ^ k + k + 2) * c
    Real.exp (T - C) ≤
      (∏ h : CopyScheduleH (characterRole k) n, lo (copyScheduleOrigin n h.val) : ℕ) ∧
    (∏ h : CopyScheduleH (characterRole k) n, hi (copyScheduleOrigin n h.val) : ℕ) ≤
      Real.exp (T + C) := by
  intro T C
  have hcard : (Fintype.card (CopyScheduleH (characterRole k) n) : ℝ) ≤
      (2 : ℝ) ^ k + k + 2 := by
    have h : (Fintype.card (CopyScheduleH (characterRole k) n) : ℝ) ≤
        (2 : ℝ) ^ n + k + 2 := by exact_mod_cast character_H_card_le hn
    have hp : (2 : ℝ) ^ n ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hn.le
    linarith
  have hcost := mul_le_mul_of_nonneg_right hcard hc
  have hsum : (∑ h : CopyScheduleH (characterRole k) n,
      w (copyScheduleOrigin n h.val)) = T := character_H_sum hn w
  constructor
  · calc
      Real.exp (T - C) ≤ Real.exp (T - Fintype.card (CopyScheduleH (characterRole k) n) * c) :=
        Real.exp_le_exp.mpr (by dsimp [C] at hcost ⊢; linarith)
      _ = ∏ h : CopyScheduleH (characterRole k) n, Real.exp (w (copyScheduleOrigin n h.val) - c) := by
        rw [← Real.exp_sum, Finset.sum_sub_distrib, hsum]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ _ := by
        rw [Nat.cast_prod]
        exact Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le) (fun i _ => hlo _)
  · calc
      _ ≤ ∏ h : CopyScheduleH (characterRole k) n, Real.exp (w (copyScheduleOrigin n h.val) + c) := by
        rw [Nat.cast_prod]
        exact Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => hhi _)
      _ = Real.exp (T + Fintype.card (CopyScheduleH (characterRole k) n) * c) := by
        rw [← Real.exp_sum, Finset.sum_add_distrib, hsum]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ Real.exp (T + C) := Real.exp_le_exp.mpr (by dsimp [C] at hcost ⊢; linarith)

end Ostmann

end OAI
