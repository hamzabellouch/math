import OAI.LinearAlgebra.MatrixMultiplication.Recovery.PermutationIndicatorMoments
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-! Finite orbit symmetries, masks and exact recovery operations. -/

noncomputable section

namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators

variable {P : Type*} [Fintype P] [DecidableEq P]

def matchingCount (A B : Finset P) (p : Equiv.Perm P) : ℝ :=
  ∑ i ∈ A, membership B p i

theorem average_matchingCount [Nonempty P] (A B : Finset P) :
    average (matchingCount A B) =
      (A.card : ℝ) * (B.card : ℝ) / (Fintype.card P : ℝ) := by
  unfold matchingCount
  rw [average_finset_sum]
  simp only [average_membership, Finset.sum_const, nsmul_eq_mul]
  ring

theorem average_matchingCount_sq [Nonempty P] (A B : Finset P) :
    average (fun p => matchingCount A B p ^ 2) =
      (A.card : ℝ) * (B.card : ℝ) / (Fintype.card P : ℝ) +
      (A.card : ℝ) * ((A.card : ℝ) - 1) * (B.card : ℝ) *
        ((B.card : ℝ) - 1) /
        ((Fintype.card P : ℝ) * ((Fintype.card P : ℝ) - 1)) := by
  let u : ℝ := (B.card : ℝ) / (Fintype.card P : ℝ)
  let v : ℝ := (B.card : ℝ) * ((B.card : ℝ) - 1) /
    ((Fintype.card P : ℝ) * ((Fintype.card P : ℝ) - 1))
  have hpair (i j : P) :
      average (fun p => membership B p i * membership B p j) =
        v + if i = j then u - v else 0 := by
    by_cases hij : i = j
    · subst j
      simp only [membership_sq]
      rw [average_membership]
      dsimp [u]
      ring
    · rw [average_membership_mul_of_ne B hij]
      simp [hij, v]
  have hsq (p : Equiv.Perm P) : matchingCount A B p ^ 2 =
      ∑ i ∈ A, ∑ j ∈ A, membership B p i * membership B p j := by
    unfold matchingCount
    rw [pow_two, Finset.sum_mul_sum]
  simp_rw [hsq]
  rw [average_finset_sum]
  simp_rw [average_finset_sum, hpair]
  have hinner (i : P) (hi : i ∈ A) :
      (∑ j ∈ A, (v + (if i = j then u - v else 0))) =
        (A.card : ℝ) * v + (u - v) := by
    rw [Finset.sum_add_distrib]
    simp [hi]
  rw [Finset.sum_congr rfl hinner]
  simp only [Finset.sum_const, nsmul_eq_mul]
  dsimp [u, v]
  ring

theorem matchingCount_variance [Nonempty P] (A B : Finset P)
    (hn : 2 ≤ Fintype.card P) :
    average (fun p => (matchingCount A B p - average (matchingCount A B)) ^ 2) =
      (A.card : ℝ) * ((Fintype.card P : ℝ) - (A.card : ℝ)) *
        (B.card : ℝ) * ((Fintype.card P : ℝ) - (B.card : ℝ)) /
        ((Fintype.card P : ℝ) ^ 2 * ((Fintype.card P : ℝ) - 1)) := by
  rw [average_centered_sq, average_matchingCount_sq, average_matchingCount]
  have hn' : (2 : ℝ) ≤ Fintype.card P := by exact_mod_cast hn
  have hn0 : (Fintype.card P : ℝ) ≠ 0 := by linarith
  have hn1 : (Fintype.card P : ℝ) - 1 ≠ 0 := by linarith
  field_simp [hn0, hn1]
  ring

theorem matchingCount_variance_le (A B : Finset P)
    (hn : 2 ≤ Fintype.card P) :
    average (fun p => (matchingCount A B p - average (matchingCount A B)) ^ 2) ≤
      (Fintype.card P : ℝ) / 8 := by
  have : Nonempty P := Fintype.card_pos_iff.mp (lt_of_lt_of_le (by decide : 0 < 2) hn)
  rw [matchingCount_variance A B hn]
  have hn' : (2 : ℝ) ≤ Fintype.card P := by exact_mod_cast hn
  have ha : (A.card : ℝ) ≤ (Fintype.card P : ℝ) := by
    exact_mod_cast Finset.card_le_univ A
  have hb : (B.card : ℝ) ≤ (Fintype.card P : ℝ) := by
    exact_mod_cast Finset.card_le_univ B
  have ha0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
  have hna : 0 ≤ (A.card : ℝ) * ((Fintype.card P : ℝ) - A.card) :=
    mul_nonneg ha0 (sub_nonneg.mpr ha)
  have hnb : 0 ≤ (B.card : ℝ) * ((Fintype.card P : ℝ) - B.card) :=
    mul_nonneg hb0 (sub_nonneg.mpr hb)
  have hqa : (A.card : ℝ) * ((Fintype.card P : ℝ) - A.card) ≤
      (Fintype.card P : ℝ) ^ 2 / 4 := by
    nlinarith [sq_nonneg ((A.card : ℝ) - (Fintype.card P : ℝ) / 2)]
  have hqb : (B.card : ℝ) * ((Fintype.card P : ℝ) - B.card) ≤
      (Fintype.card P : ℝ) ^ 2 / 4 := by
    nlinarith [sq_nonneg ((B.card : ℝ) - (Fintype.card P : ℝ) / 2)]
  have hprod := mul_le_mul hqa hqb hnb (by positivity :
    (0 : ℝ) ≤ (Fintype.card P : ℝ) ^ 2 / 4)
  have hn3 : 0 ≤ (Fintype.card P : ℝ) ^ 3 * ((Fintype.card P : ℝ) - 2) :=
    mul_nonneg (by positivity) (by linarith)
  have hn1pos : (0 : ℝ) < (Fintype.card P : ℝ) - 1 := by linarith
  have hnpos : (0 : ℝ) < Fintype.card P := by linarith
  apply (div_le_iff₀ (show (0 : ℝ) <
    (Fintype.card P : ℝ) ^ 2 * ((Fintype.card P : ℝ) - 1) by positivity)).mpr
  nlinarith

noncomputable def statisticPositions {A B : Type*} (w : P → A)
    (statistic : A → B) (b : B) : Finset P := by
  classical
  exact Finset.univ.filter fun i => statistic (w i) = b

noncomputable def statisticMatchingCount {A B S T : Type*}
    (left : P → A) (right : P → B) (sl : A → S) (sr : B → T)
    (s : S) (t : T) : Equiv.Perm P → ℝ :=
  matchingCount (statisticPositions left sl s) (statisticPositions right sr t)

theorem statisticMatchingCount_variance_le {A B S T : Type*}
    (left : P → A) (right : P → B) (sl : A → S) (sr : B → T)
    (s : S) (t : T) (hn : 2 ≤ Fintype.card P) :
    average (fun p =>
      (statisticMatchingCount left right sl sr s t p -
        average (statisticMatchingCount left right sl sr s t)) ^ 2) ≤
      (Fintype.card P : ℝ) / 8 :=
  matchingCount_variance_le _ _ hn

end MatrixMultiplication.PermutationMatching

end

end OAI
