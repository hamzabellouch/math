import OAI.NumberTheory.TwoPoint.Bounds.FiniteRoughSieve
import Mathlib.Data.Nat.Prime.Basic

namespace OAI

/-! The finite sieve applied to the actual one- and four-form rough events.
Only the classical reciprocal-prime estimates remain in the quantitative
bounds; all finite local and intersection calculations are proved. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def avoidsPrimeSet (P : Finset ℕ) (n : ℕ) : Prop := ∀ p ∈ P, ¬p ∣ n

def fourFormsAvoidPrimeSet (P : Finset ℕ) (x : ℕ × ℕ × ℕ) : Prop :=
  avoidsPrimeSet P x.1 ∧ avoidsPrimeSet P x.2.1 ∧ avoidsPrimeSet P x.2.2 ∧
    ∀ p ∈ P, ¬(p : ℤ) ∣ (x.1 : ℤ) + x.2.1 - x.2.2

lemma primeSet_pairwise_coprime (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    Pairwise (fun p q : P => (p : ℕ).Coprime (q : ℕ)) := by
  intro p q hpq
  exact (Nat.coprime_primes (hP p p.property) (hP q q.property)).mpr
    (fun h => hpq (Subtype.ext h))

lemma avoidsPrimeSet_iff_residues (P : Finset ℕ) (n : ℕ) :
    avoidsPrimeSet P n ↔ ∀ p : P, (n : ZMod (p : ℕ)) ≠ 0 := by
  simp only [avoidsPrimeSet, Subtype.forall, ne_eq, ZMod.natCast_eq_zero_iff]

lemma fourFormsAvoidPrimeSet_iff_residues (P : Finset ℕ)
    [∀ p : P, NeZero (p : ℕ)] (x : ℕ × ℕ × ℕ) :
    fourFormsAvoidPrimeSet P x ↔ ∀ p : P,
      ¬fourFormBad ((x.1 : ZMod (p : ℕ)), (x.2.1 : ZMod (p : ℕ)),
        (x.2.2 : ZMod (p : ℕ))) := by
  have hlast (p : P) :
      ((x.1 : ZMod (p : ℕ)) + (x.2.1 : ZMod (p : ℕ)) - (x.2.2 : ZMod (p : ℕ)) = 0) ↔
      (p : ℤ) ∣ (x.1 : ℤ) + x.2.1 - x.2.2 := by
    simpa only [Int.cast_sub, Int.cast_add, Int.cast_natCast] using
      ZMod.intCast_zmod_eq_zero_iff_dvd ((x.1 : ℤ) + x.2.1 - x.2.2) (p : ℕ)
  simp only [fourFormsAvoidPrimeSet, avoidsPrimeSet_iff_residues,
    fourFormBad, not_or, hlast, forall_and, Subtype.forall]

theorem rough_interval_probability (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (A N : ℕ) [NeZero N] (r : ℕ) (L C Y : ℝ) (hL : 1 ≤ L) (hY : 0 ≤ Y)
    (hmax : ∀ p ∈ P, (p : ℝ) ≤ Y)
    (hlower : (99 / 100 : ℝ) * Real.log L - C ≤ ∑ p ∈ P, 1 / (p : ℝ))
    (hupper : (∑ p ∈ P, 1 / (p : ℝ)) ≤ 5 * Real.log L)
    (hr : 220 * Real.log L ≤ (2 * r + 1 : ℕ)) :
    (uniformFiniteLaw (Fin N)).probability (fun j => avoidsPrimeSet P (A + j.val)) ≤
      Real.exp C * L ^ (-99 / 100 : ℝ) + L ^ (-100 : ℝ) +
        1 / (N : ℝ) * (2 * r + 1 : ℕ) * ((P.card : ℝ) * Y + 1) ^ (2 * r) := by
  let (p : P) : NeZero (p : ℕ) := ⟨(hP p p.property).ne_zero⟩
  have hh := finite_interval_sieve (fun p : P => (p : ℕ)) (primeSet_pairwise_coprime P hP)
    A N (fun _ x => x = 0) r Y hY (fun p => hmax p p.property)
  have he : avoidsEvents univ (fun p : P => fun j : Fin N =>
      ((A + j.val : ℕ) : ZMod (p : ℕ)) = 0) =
      (fun j => avoidsPrimeSet P (A + j.val)) := by
    funext j
    simp only [avoidsEvents, mem_univ, forall_true_left, avoidsPrimeSet_iff_residues]
  simp only [he, oneFormBadDensity, Fintype.card_coe] at hh
  have hsum : (∑ p : P, 1 / (p : ℝ)) ≤ 5 * Real.log L := by
    rw [← sum_subtype (p := fun p : ℕ => p ∈ P) P (fun _ => Iff.rfl)
      (fun p => 1 / (p : ℝ))]
    exact hupper
  have ht := elementarySymmetric_log_tail (univ : Finset P)
    (fun p => 1 / (p : ℝ)) (fun p _ => by positivity) (2 * r + 1) L hL hsum hr
  have hp := oneForm_product_scale P (fun p hp => (hP p hp).two_le)
    L C (zero_lt_one.trans_le hL) hlower
  rw [prod_subtype (p := fun p : ℕ => p ∈ P) P (fun _ => Iff.rfl)] at hp
  exact hh.trans (by gcongr)

theorem rough_cube_probability (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (A : ℕ × ℕ × ℕ) (N : ℕ) [NeZero N] (r : ℕ) (L C Y : ℝ)
    (hL : 1 ≤ L) (hY : 0 ≤ Y) (hmax : ∀ p ∈ P, (p : ℝ) ≤ Y)
    (hlower : (99 / 100 : ℝ) * Real.log L - C ≤ ∑ p ∈ P, 1 / (p : ℝ))
    (hupper : (∑ p ∈ P, 1 / (p : ℝ)) ≤ (5 / 4 : ℝ) * Real.log L)
    (hr : 220 * Real.log L ≤ (2 * r + 1 : ℕ)) :
    (uniformFiniteLaw (Fin N × Fin N × Fin N)).probability (fun j =>
      fourFormsAvoidPrimeSet P (A.1 + j.1.val, A.2.1 + j.2.1.val, A.2.2 + j.2.2.val)) ≤
      Real.exp (4 * C + 6) * L ^ (-99 / 25 : ℝ) + L ^ (-100 : ℝ) +
        3 / (N : ℝ) * (2 * r + 1 : ℕ) * ((P.card : ℝ) * Y + 1) ^ (2 * r) := by
  let (p : P) : NeZero (p : ℕ) := ⟨(hP p p.property).ne_zero⟩
  have hh := finite_cube_sieve (fun p : P => (p : ℕ)) (primeSet_pairwise_coprime P hP)
    A N (fun _ => fourFormBad) r Y hY (fun p => hmax p p.property)
  have he : avoidsEvents univ (fun p : P => fun j : Fin N × Fin N × Fin N =>
      fourFormBad (((A.1 + j.1.val : ℕ) : ZMod (p : ℕ)),
        ((A.2.1 + j.2.1.val : ℕ) : ZMod (p : ℕ)),
        ((A.2.2 + j.2.2.val : ℕ) : ZMod (p : ℕ)))) =
      (fun j => fourFormsAvoidPrimeSet P
        (A.1 + j.1.val, A.2.1 + j.2.1.val, A.2.2 + j.2.2.val)) := by
    funext j
    simp only [avoidsEvents, mem_univ, forall_true_left, fourFormsAvoidPrimeSet_iff_residues]
  change _ ≤ (∏ p : P, (1 - fourFormBadDensity (p : ℕ))) +
    elementarySymmetric univ (fun p : P => fourFormBadDensity (p : ℕ)) (2 * r + 1) + _ at hh
  rw [he] at hh
  simp only [Fintype.card_coe] at hh
  have hsum : (∑ p : P, fourFormBadDensity (p : ℕ)) ≤ 5 * Real.log L := by
    calc
      _ ≤ ∑ p : P, 4 / (p : ℝ) :=
        sum_le_sum (fun p _ => (fourFormBadDensity_bounds (p : ℕ)).2)
      _ = 4 * ∑ p ∈ P, 1 / (p : ℝ) := by
        rw [← sum_subtype (p := fun p : ℕ => p ∈ P) P (fun _ => Iff.rfl)
          (fun p => 4 / (p : ℝ))]
        simp only [div_eq_mul_inv, one_mul, ← mul_sum]
      _ ≤ _ := by linarith
  have ht := elementarySymmetric_log_tail (univ : Finset P)
    (fun p => fourFormBadDensity (p : ℕ)) (fun p _ => fourFormBadDensity_nonneg _)
    (2 * r + 1) L hL hsum hr
  have hp := fourForm_product_scale P (fun p hp => (hP p hp).two_le)
    L C (zero_lt_one.trans_le hL) hlower
  exact hh.trans (by gcongr)

end TwoPointCorrelations

end OAI
