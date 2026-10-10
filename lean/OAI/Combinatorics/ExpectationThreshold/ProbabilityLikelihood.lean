import OAI.Combinatorics.ExpectationThreshold.SelectorDefinitions
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Basic.Real.Basic

namespace OAI

/-!
# Likelihood of an actual move of colors

The full guarded profile records every changed coordinate exactly once.
Grouping the coordinate likelihood factors by that profile gives the precise
ratio used by the selector estimate.
-/

noncomputable section

open scoped BigOperators

namespace TalagrandThreshold

open Selector

variable {α : Type*} [Fintype α] [DecidableEq α] {s : ℕ}

omit [DecidableEq α] in
/-- Group a product over changed vertices by the actual full profile. -/
theorem prod_profile_eq_prod_changes (a z : Coloring α s)
    (F : Color s → Color s → ℝ) :
    (∏ i : Fin s, ∏ h : Color s, F i.castSucc h ^ profile a z i h) =
      ∏ x ∈ changes a z, F (z x) (a x) := by
  classical
  let n (c h : Color s) : ℕ :=
    (Finset.univ.filter
      (fun x : α => z x = c ∧ a x = h ∧ c.val < h.val)).card
  have hfiber (c h : Color s) :
      (changes a z).filter (fun x => (z x, a x) = (c, h)) =
        Finset.univ.filter
          (fun x : α => z x = c ∧ a x = h ∧ c.val < h.val) := by
    ext x
    simp only [changes, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq,
      Fin.lt_def]
    constructor
    · rintro ⟨hx, hz, ha⟩
      exact ⟨hz, ha, by simpa only [hz, ha] using hx⟩
    · rintro ⟨hz, ha, hch⟩
      exact ⟨by simpa only [hz, ha] using hch, hz, ha⟩
  have hgroup :
      (∏ c : Color s, ∏ h : Color s, F c h ^ n c h) =
        ∏ x ∈ changes a z, F (z x) (a x) := by
    calc
      _ = ∏ ch : Color s × Color s,
          F ch.1 ch.2 ^
            ((changes a z).filter (fun x => (z x, a x) = ch)).card := by
        rw [Fintype.prod_prod_type]
        apply Finset.prod_congr rfl
        intro c _
        apply Finset.prod_congr rfl
        intro h _
        rw [hfiber c h]
      _ = ∏ x ∈ changes a z, F (z x) (a x) := by
        simpa only [Finset.prod_const] using
          (Finset.prod_fiberwise' (changes a z)
            (fun x => (z x, a x))
            (fun ch : Color s × Color s => F ch.1 ch.2))
  have hlast : (∏ h : Color s, F (Fin.last s) h ^ n (Fin.last s) h) = 1 := by
    apply Finset.prod_eq_one
    intro h _
    have hnot : ¬ (Fin.last s).val < h.val :=
      Nat.not_lt_of_ge (Nat.le_of_lt_succ h.isLt)
    simp only [n, hnot, and_false, Finset.filter_false, Finset.card_empty, pow_zero]
  have hcount (i : Fin s) (h : Color s) : n i.castSucc h = profile a z i h := by
    simp only [n, profile, Fin.ext_iff, Fin.val_castSucc]
  rw [Fin.prod_univ_castSucc, hlast, mul_one] at hgroup
  simpa only [hcount] using hgroup

omit [DecidableEq α] in
/-- The profile exponent is the product of one p-factor per actual changed vertex. -/
theorem pow_profileSize_eq_prod_changes (p : ℝ) (a z : Coloring α s) :
    p ^ profileSize (profile a z) = ∏ _x ∈ changes a z, p := by
  calc
    _ = ∏ i : Fin s, ∏ h : Color s, p ^ profile a z i h := by
      simp only [Finset.prod_pow_eq_pow_sum, profileSize, rowCount]
    _ = ∏ _x ∈ changes a z, p :=
      prod_profile_eq_prod_changes a z (fun _ _ => p)

omit [DecidableEq α] in
/-- Exact likelihood regrouping for the original independent color law and an
actual move to earlier colors. Each source row retains all original-color counts. -/
theorem colorMass_profile_likelihood (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (a z : Coloring α s) (haz : Selector.Earlier a z) :
    p ^ Selector.profileSize (Selector.profile a z) * colorMass p s a =
      colorMass p s z * ∏ i : Fin s,
        ((p / colorProb p s i.castSucc) ^ Selector.rowCount (Selector.profile a z) i *
          ∏ h : Color s, (colorProb p s h) ^ Selector.profile a z i h) := by
  classical
  have hpowers : p ^ profileSize (profile a z) =
      ∏ x : α, if z x < a x then p else 1 := by
    calc
      _ = ∏ _x ∈ changes a z, p := pow_profileSize_eq_prod_changes p a z
      _ = ∏ x : α, if z x < a x then p else 1 :=
        Finset.prod_filter (fun x => z x < a x) (fun _ => p)
  have hratios :
      (∏ x ∈ changes a z, (p / colorProb p s (z x)) * colorProb p s (a x)) =
        ∏ x : α, if z x < a x then
          (p / colorProb p s (z x)) * colorProb p s (a x) else 1 :=
    Finset.prod_filter (fun x => z x < a x)
      (fun x => (p / colorProb p s (z x)) * colorProb p s (a x))
  have hpoint (x : α) :
      (if z x < a x then p else 1) * colorProb p s (a x) =
        colorProb p s (z x) * (if z x < a x then
          (p / colorProb p s (z x)) * colorProb p s (a x) else 1) := by
    by_cases h : z x < a x
    · rw [ite_eq_left h, ite_eq_left h, ← mul_assoc,
        mul_div_cancel₀ p (ne_of_gt (colorProb_pos p s hp hs (z x)))]
    · have heq : z x = a x := le_antisymm (haz x) (le_of_not_gt h)
      simp only [heq, lt_self_iff_false, ite_false, one_mul, mul_one]
  calc
    _ = ∏ x : α, (if z x < a x then p else 1) * colorProb p s (a x) := by
      rw [hpowers, colorMass, Finset.prod_mul_distrib]
    _ = ∏ x : α, colorProb p s (z x) * (if z x < a x then
        (p / colorProb p s (z x)) * colorProb p s (a x) else 1) := by
      apply Finset.prod_congr rfl
      intro x _
      exact hpoint x
    _ = colorMass p s z *
        ∏ x ∈ changes a z, (p / colorProb p s (z x)) * colorProb p s (a x) := by
      rw [Finset.prod_mul_distrib, ← hratios, colorMass]
    _ = colorMass p s z *
        ∏ i : Fin s, ∏ h : Color s,
          ((p / colorProb p s i.castSucc) * colorProb p s h) ^ profile a z i h := by
      rw [prod_profile_eq_prod_changes a z
        (fun c h => (p / colorProb p s c) * colorProb p s h)]
    _ = colorMass p s z * ∏ i : Fin s,
        ((p / colorProb p s i.castSucc) ^ rowCount (profile a z) i *
          ∏ h : Color s, (colorProb p s h) ^ profile a z i h) := by
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, rowCount]

end TalagrandThreshold

end

end OAI
