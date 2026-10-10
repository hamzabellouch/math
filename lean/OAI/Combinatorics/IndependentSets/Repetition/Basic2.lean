import Mathlib

namespace OAI

namespace IndependentSetsGames.Foundations.CorrelatedSampling

def firstAccepted {σ : Type*} (accept : σ → Bool) : List σ → Option σ
  | [] => none
  | proposal :: rest =>
      if accept proposal then some proposal else firstAccepted accept rest

theorem first_union_common {σ : Type*} (left right : σ → Bool)
    (proposals : List σ) (proposal : σ)
    (hfirst : firstAccepted (fun s => left s || right s) proposals = some proposal)
    (hleft : left proposal = true) (hright : right proposal = true) :
    firstAccepted left proposals = some proposal ∧
      firstAccepted right proposals = some proposal := by
  induction proposals with
  | nil => simp [firstAccepted] at hfirst
  | cons head tail ih =>
      by_cases hl : left head = true
      · have heq : head = proposal := by
          simpa [firstAccepted, hl] using hfirst
        subst head
        simp [firstAccepted, hleft, hright]
      · by_cases hr : right head = true
        · have heq : head = proposal := by
            simpa [firstAccepted, hl, hr] using hfirst
          subst head
          exact False.elim (hl hleft)
        · have htail : firstAccepted (fun s => left s || right s) tail = some proposal := by
            simpa [firstAccepted, hl, hr] using hfirst
          simpa [firstAccepted, hl, hr] using ih htail

def thresholdSample {α : Type*} (mass : α → Nat) (proposals : List (α × Nat)) :
    Option α :=
  (firstAccepted (fun s => decide (s.2 < mass s.1)) proposals).map Prod.fst

theorem thresholdSample_agreement {α : Type*} (left right : α → Nat)
    (proposals : List (α × Nat)) (a : α) (height : Nat)
    (hfirst : firstAccepted
      (fun s => decide (s.2 < left s.1) || decide (s.2 < right s.1)) proposals =
      some (a, height))
    (hcommon : height < min (left a) (right a)) :
    thresholdSample left proposals = some a ∧
      thresholdSample right proposals = some a := by
  have h := first_union_common
    (fun s : α × Nat => decide (s.2 < left s.1))
    (fun s : α × Nat => decide (s.2 < right s.1)) proposals (a, height) hfirst
    (by simpa using (lt_min_iff.mp hcommon).1)
    (by simpa using (lt_min_iff.mp hcommon).2)
  simp [thresholdSample, h.1, h.2]

noncomputable section FiniteWeights

variable {α : Type*} [Fintype α]

def totalVariation (p q : α → ℝ) : ℝ := (∑ a, |p a - q a|) / 2

def overlapMass (p q : α → ℝ) : ℝ := ∑ a, min (p a) (q a)

def unionMass (p q : α → ℝ) : ℝ := ∑ a, max (p a) (q a)

theorem totalVariation_nonneg (p q : α → ℝ) : 0 ≤ totalVariation p q := by
  unfold totalVariation
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by norm_num)

theorem overlapMass_nonneg (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hq : ∀ a, 0 ≤ q a) : 0 ≤ overlapMass p q := by
  exact Finset.sum_nonneg (fun a _ => le_min (hp a) (hq a))

private theorem min_abs_identity (x y : ℝ) : 2 * min x y + |x - y| = x + y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

private theorem max_abs_identity (x y : ℝ) : 2 * max x y - |x - y| = x + y := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem overlapMass_eq (p q : α → ℝ) (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    overlapMass p q = 1 - totalVariation p q := by
  have h := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun a _ => min_abs_identity (p a) (q a))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hp, hq] at h
  unfold overlapMass totalVariation
  linarith

theorem unionMass_eq (p q : α → ℝ) (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    unionMass p q = 1 + totalVariation p q := by
  have h := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun a _ => max_abs_identity (p a) (q a))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hp, hq] at h
  unfold unionMass totalVariation
  linarith

theorem totalVariation_le_one (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hq : ∀ a, 0 ≤ q a) (hpsum : ∑ a, p a = 1) (hqsum : ∑ a, q a = 1) :
    totalVariation p q ≤ 1 := by
  have h := overlapMass_nonneg p q hp hq
  rw [overlapMass_eq p q hpsum hqsum] at h
  linarith

theorem overlap_union_ratio (p q : α → ℝ)
    (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    overlapMass p q / unionMass p q =
      (1 - totalVariation p q) / (1 + totalVariation p q) := by
  rw [overlapMass_eq p q hp hq, unionMass_eq p q hp hq]

theorem overlap_union_ratio_lower_bound (p q : α → ℝ)
    (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    1 - 2 * totalVariation p q ≤ overlapMass p q / unionMass p q := by
  rw [overlap_union_ratio p q hp hq]
  have htv := totalVariation_nonneg p q
  have hden : 0 < 1 + totalVariation p q := by linarith
  apply (le_div_iff₀ hden).2
  nlinarith [sq_nonneg (totalVariation p q)]

theorem first_union_disagreement_upper_bound (p q : α → ℝ)
    (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    1 - overlapMass p q / unionMass p q ≤ 2 * totalVariation p q := by
  linarith [overlap_union_ratio_lower_bound p q hp hq]

end FiniteWeights

end IndependentSetsGames.Foundations.CorrelatedSampling

end OAI
