import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import OAI.NumberTheory.Ostmann.Preliminaries.Collision

namespace OAI

/-!
# Extracting one common center

The finite incidence argument in Section 3: large matching-prime sets
with small pairwise intersections have total size at most twice the
ambient set. A large moment therefore forces one large matching set.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def centerIncidence {I P : Type*} [Fintype I] [DecidableEq P]
    (S : I → Finset P) (p : P) : ℝ := ∑ i : I, if p ∈ S i then 1 else 0

theorem sum_centerIncidence {I P : Type*} [Fintype I] [Fintype P] [DecidableEq P]
    (S : I → Finset P) :
    (∑ p : P, centerIncidence S p) = ∑ i : I, ((S i).card : ℝ) := by
  unfold centerIncidence
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem sum_centerIncidence_sq {I P : Type*} [Fintype I] [Fintype P] [DecidableEq P]
    (S : I → Finset P) :
    (∑ p : P, centerIncidence S p ^ 2) =
      ∑ i : I, ∑ j : I, ((S i ∩ S j).card : ℝ) := by
  have hind (i j : I) :
      (∑ p : P, (if p ∈ S i then (1 : ℝ) else 0) * (if p ∈ S j then 1 else 0)) =
        (S i ∩ S j).card := by
    calc
      _ = ∑ p : P, if p ∈ S i ∩ S j then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro p _
        by_cases hi : p ∈ S i <;> by_cases hj : p ∈ S j <;> simp [hi, hj]
      _ = _ := by
        simp
        congr 1
        ext p
        simp
  simp only [centerIncidence, pow_two, Fintype.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => hind i j)

/-- Incidence Cauchy--Schwarz, with the diagonal separated before estimating intersections. -/
theorem commonCenter_incidence_bound {I P : Type*} [Fintype I] [Fintype P]
    [DecidableEq P] (S : I → Finset P) (K : ℝ) (hK : 0 ≤ K)
    (hinter : ∀ i j, i ≠ j → ((S i ∩ S j).card : ℝ) ≤ K) :
    (∑ i : I, ((S i).card : ℝ)) ^ 2 ≤
      (Fintype.card P : ℝ) *
        ((∑ i : I, ((S i).card : ℝ)) + K * (Fintype.card I : ℝ) ^ 2) := by
  classical
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset P))
    (f := centerIncidence S)
  rw [sum_centerIncidence, sum_centerIncidence_sq] at hcs
  simp only [Finset.card_univ] at hcs
  apply hcs.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ i : I, ∑ j : I, ((if i = j then ((S i).card : ℝ) else 0) + K) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i = j
      · subst j
        simpa using hK
      · simpa only [hij, ite_false, zero_add] using hinter i j hij
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
        ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- The quantitative absorption used for the high matching sets. -/
theorem commonCenter_total_le_twice {R J b A K : ℝ}
    (hJ : 0 ≤ J) (hb : 0 ≤ b) (hA : 0 < A)
    (hinc : R ^ 2 ≤ J * (R + K * b ^ 2))
    (hlarge : b * A ≤ R) (hsmall : 2 * K * J ≤ A ^ 2) : R ≤ 2 * J := by
  have hsq : (b * A) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (mul_nonneg hb hA.le) hlarge 2
  have hprod := mul_le_mul_of_nonneg_right hsmall (sq_nonneg b)
  have hquad : R ^ 2 ≤ 2 * J * R := by nlinarith
  nlinarith

theorem commonCenter_family_total_le_twice {I P : Type*} [Fintype I] [Fintype P]
    [DecidableEq P] (S : I → Finset P) (A K : ℝ) (hA : 0 < A) (hK : 0 ≤ K)
    (hlarge : ∀ i, A ≤ ((S i).card : ℝ))
    (hinter : ∀ i j, i ≠ j → ((S i ∩ S j).card : ℝ) ≤ K)
    (hsmall : 2 * K * (Fintype.card P : ℝ) ≤ A ^ 2) :
    (∑ i : I, ((S i).card : ℝ)) ≤ 2 * (Fintype.card P : ℝ) := by
  apply commonCenter_total_le_twice
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hA
    (commonCenter_incidence_bound S K hK hinter) _ hsmall
  calc
    (Fintype.card I : ℝ) * A = ∑ _i : I, A := by simp
    _ ≤ _ := Finset.sum_le_sum fun i _ => hlarge i

/-- A lower moment and the total incidence budget force a single large center. -/
theorem exists_commonCenter_of_moment {I P : Type*} [Fintype I] [Fintype P]
    [DecidableEq P] [Nonempty I] (S : I → Finset P) (A K L : ℝ) (k : ℕ)
    (hA : 0 < A) (hK : 0 ≤ K)
    (hlarge : ∀ i, A ≤ ((S i).card : ℝ))
    (hinter : ∀ i j, i ≠ j → ((S i ∩ S j).card : ℝ) ≤ K)
    (hsmall : 2 * K * (Fintype.card P : ℝ) ≤ A ^ 2)
    (hmoment : L ≤ ∑ i : I, ((S i).card : ℝ) ^ (k + 1)) :
    ∃ i : I, L ≤ 2 * (Fintype.card P : ℝ) * ((S i).card : ℝ) ^ k := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i => ((S i).card : ℝ)) Finset.univ_nonempty
  refine ⟨i, hmoment.trans ?_⟩
  calc
    _ ≤ ∑ j : I, ((S i).card : ℝ) ^ k * (S j).card := by
      apply Finset.sum_le_sum
      intro j _
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) (hi j (Finset.mem_univ _)) k) (Nat.cast_nonneg _)
    _ = ((S i).card : ℝ) ^ k * (∑ j : I, ((S j).card : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ ((S i).card : ℝ) ^ k * (2 * (Fintype.card P : ℝ)) :=
      mul_le_mul_of_nonneg_left (commonCenter_family_total_le_twice S A K hA hK
        hlarge hinter hsmall) (pow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := by ring

end Ostmann

end OAI
