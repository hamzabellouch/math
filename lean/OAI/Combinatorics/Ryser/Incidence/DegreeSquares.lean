import OAI.Combinatorics.Ryser.Incidence.PruningCore
import OAI.Combinatorics.Ryser.Geometry.ProjectiveJoins

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Incidence

variable {Pt Ln : Type*} [DecidableEq Pt] [DecidableEq Ln]

private theorem rightDegree_sq_eq_sum (R : Pt → Ln → Prop) (P : Finset Pt) (l : Ln) :
    rightDegree R P l ^ 2 =
      ∑ p ∈ P, ∑ q ∈ P, if R p l ∧ R q l then 1 else 0 := by
  classical
  rw [rightDegree, leftDegree_eq_sum, pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hpl : R p l <;> by_cases hql : R q l <;> simp [hpl, hql]

theorem sum_rightDegree_sq_eq_commonCount (R : Pt → Ln → Prop)
    (P : Finset Pt) (L : Finset Ln) :
    (∑ l ∈ L, rightDegree R P l ^ 2) =
      ∑ p ∈ P, ∑ q ∈ P, (L.filter fun l => R p l ∧ R q l).card := by
  classical
  simp_rw [rightDegree_sq_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  exact Finset.sum_boole (R := ℕ) (fun l => R p l ∧ R q l) L

theorem sum_rightDegree_sq_le_nat (R : Pt → Ln → Prop)
    (P : Finset Pt) (L : Finset Ln)
    (huniq : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → ∀ l ∈ L, ∀ m ∈ L,
      R p l → R q l → R p m → R q m → l = m) :
    (∑ l ∈ L, rightDegree R P l ^ 2) ≤ incidenceCount R P L + P.card ^ 2 := by
  classical
  have hpair (p : Pt) (hp : p ∈ P) (q : Pt) (hq : q ∈ P) :
      (L.filter fun l => R p l ∧ R q l).card ≤
        (if p = q then leftDegree R L p else 0) + 1 := by
    by_cases hpq : p = q
    · subst q
      simp only [and_self]
      change leftDegree R L p ≤ leftDegree R L p + 1
      exact Nat.le_succ _
    · rw [ite_eq_right hpq, zero_add]
      apply Finset.card_le_one.mpr
      intro l hl m hm
      obtain ⟨hlL, hpl, hql⟩ := Finset.mem_filter.mp hl
      obtain ⟨hmL, hpm, hqm⟩ := Finset.mem_filter.mp hm
      exact huniq p hp q hq hpq l hlL m hmL hpl hql hpm hqm
  have hrow (p : Pt) (hp : p ∈ P) :
      (∑ q ∈ P, (L.filter fun l => R p l ∧ R q l).card) ≤
        leftDegree R L p + P.card := by
    calc
      (∑ q ∈ P, (L.filter fun l => R p l ∧ R q l).card) ≤
          ∑ q ∈ P, ((if p = q then leftDegree R L p else 0) + 1) :=
        Finset.sum_le_sum fun q hq => hpair p hp q hq
      _ = leftDegree R L p + P.card := by
        simp [Finset.sum_add_distrib, hp]
  calc
    (∑ l ∈ L, rightDegree R P l ^ 2) =
        ∑ p ∈ P, ∑ q ∈ P, (L.filter fun l => R p l ∧ R q l).card :=
      sum_rightDegree_sq_eq_commonCount R P L
    _ ≤ ∑ p ∈ P, (leftDegree R L p + P.card) :=
      Finset.sum_le_sum fun p hp => hrow p hp
    _ = incidenceCount R P L + P.card ^ 2 := by
      simp [incidenceCount, Finset.sum_add_distrib, pow_two]

theorem sum_rightDegree_sq_le (R : Pt → Ln → Prop)
    (P : Finset Pt) (L : Finset Ln)
    (huniq : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → ∀ l ∈ L, ∀ m ∈ L,
      R p l → R q l → R p m → R q m → l = m) :
    (∑ l ∈ L, (rightDegree R P l : ℝ) ^ 2) ≤
      (incidenceCount R P L : ℝ) + (P.card : ℝ) ^ 2 := by
  exact_mod_cast sum_rightDegree_sq_le_nat R P L huniq

theorem sum_leftDegree_sq_le (R : Pt → Ln → Prop)
    (P : Finset Pt) (L : Finset Ln)
    (huniq : ∀ l ∈ L, ∀ m ∈ L, l ≠ m → ∀ p ∈ P, ∀ q ∈ P,
      R p l → R p m → R q l → R q m → p = q) :
    (∑ p ∈ P, (leftDegree R L p : ℝ) ^ 2) ≤
      (incidenceCount R P L : ℝ) + (L.card : ℝ) ^ 2 := by
  have h := sum_rightDegree_sq_le (fun l p => R p l) L P huniq
  rw [← incidenceCount_swap R P L] at h
  exact h

variable {F : Type*} [Field F] [DecidableEq F]

theorem sum_projective_rightDegree_sq_le
    (P : Finset (ProjectivePoint F)) (L : Finset (ProjectiveLine F)) :
    (∑ l ∈ L, (rightDegree ProjectiveIncidence P l : ℝ) ^ 2) ≤
      (incidenceCount ProjectiveIncidence P L : ℝ) + (P.card : ℝ) ^ 2 := by
  apply sum_rightDegree_sq_le
  intro p hp q hq hpq l hl m hm hpl hql hpm hqm
  exact eq_projectiveLine_of_common_incidence hpq hpl hql hpm hqm

theorem sum_projective_leftDegree_sq_le
    (P : Finset (ProjectivePoint F)) (L : Finset (ProjectiveLine F)) :
    (∑ p ∈ P, (leftDegree ProjectiveIncidence L p : ℝ) ^ 2) ≤
      (incidenceCount ProjectiveIncidence P L : ℝ) + (L.card : ℝ) ^ 2 := by
  apply sum_leftDegree_sq_le
  intro l hl m hm hlm p hp q hq hpl hpm hql hqm
  exact eq_projectivePoint_of_common_incidence hlm hpl hpm hql hqm

end RyserCoveringCounterexample.Incidence

end

end OAI
