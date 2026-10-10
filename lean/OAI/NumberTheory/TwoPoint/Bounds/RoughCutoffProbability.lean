import OAI.NumberTheory.TwoPoint.Bounds.RoughSieveProbability

namespace OAI

/-! The finite rough sieve with its cutoff left explicit, for both one
linear form and the additive four-form system. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem rough_interval_probability_cutoff (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (A N : ℕ) [NeZero N] (r : ℕ) (B C X Y : ℝ) (hB : 1 ≤ B) (hX : 0 < X)
    (hY : 0 ≤ Y) (hmax : ∀ p ∈ P, (p : ℝ) ≤ Y)
    (hlower : Real.log X - C ≤ ∑ p ∈ P, 1 / (p : ℝ))
    (hupper : (∑ p ∈ P, 1 / (p : ℝ)) ≤ 5 * Real.log B)
    (hr : 220 * Real.log B ≤ (2 * r + 1 : ℕ)) :
    (uniformFiniteLaw (Fin N)).probability (fun j => avoidsPrimeSet P (A + j.val)) ≤
      Real.exp C / X + B ^ (-100 : ℝ) +
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
  have hsum : (∑ p : P, 1 / (p : ℝ)) ≤ 5 * Real.log B := by
    rw [← sum_subtype (p := fun p : ℕ => p ∈ P) P (fun _ => Iff.rfl)
      (fun p => 1 / (p : ℝ))]
    exact hupper
  have ht := elementarySymmetric_log_tail (univ : Finset P)
    (fun p => 1 / (p : ℝ)) (fun p _ => by positivity) (2 * r + 1) B hB hsum hr
  have hp : (∏ p ∈ P, (1 - 1 / (p : ℝ))) ≤ Real.exp C / X := by
    apply (oneForm_product_bound P (fun p hp => (hP p hp).two_le)).trans
    calc
      _ ≤ Real.exp (C - Real.log X) := Real.exp_le_exp.mpr (by linarith only [hlower])
      _ = _ := by rw [Real.exp_sub, Real.exp_log hX]
  rw [prod_subtype (p := fun p : ℕ => p ∈ P) P (fun _ => Iff.rfl)] at hp
  exact hh.trans (by gcongr)

theorem rough_cube_probability_cutoff (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (A : ℕ × ℕ × ℕ) (N : ℕ) [NeZero N] (r : ℕ) (B C X Y : ℝ)
    (hB : 1 ≤ B) (hX : 0 < X) (hY : 0 ≤ Y) (hmax : ∀ p ∈ P, (p : ℝ) ≤ Y)
    (hlower : Real.log X - C ≤ ∑ p ∈ P, 1 / (p : ℝ))
    (hupper : (∑ p ∈ P, 1 / (p : ℝ)) ≤ (5 / 4 : ℝ) * Real.log B)
    (hr : 220 * Real.log B ≤ (2 * r + 1 : ℕ)) :
    (uniformFiniteLaw (Fin N × Fin N × Fin N)).probability (fun j =>
      fourFormsAvoidPrimeSet P (A.1 + j.1.val, A.2.1 + j.2.1.val, A.2.2 + j.2.2.val)) ≤
      Real.exp (4 * C + 6) / X ^ 4 + B ^ (-100 : ℝ) +
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
  have hsum : (∑ p : P, fourFormBadDensity (p : ℕ)) ≤ 5 * Real.log B := by
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
    (2 * r + 1) B hB hsum hr
  have hp : (∏ p : P, (1 - fourFormBadDensity (p : ℕ))) ≤
      Real.exp (4 * C + 6) / X ^ 4 := by
    apply (fourForm_product_bound P (fun p hp => (hP p hp).two_le)).trans
    calc
      _ = Real.exp (6 - 4 * ∑ p ∈ P, 1 / (p : ℝ)) := by
        rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (4 * C + 6 - 4 * Real.log X) :=
        Real.exp_le_exp.mpr (by linarith only [hlower])
      _ = _ := by
        rw [Real.exp_sub]
        have he : Real.exp (4 * Real.log X) = X ^ 4 := by
          calc
            _ = (Real.exp (Real.log X)) ^ (4 : ℕ) := Real.exp_nat_mul (Real.log X) 4
            _ = _ := by rw [Real.exp_log hX]
        rw [he]
  exact hh.trans (by gcongr)

end TwoPointCorrelations

end OAI
