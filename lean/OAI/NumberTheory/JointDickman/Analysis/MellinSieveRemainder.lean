import OAI.NumberTheory.JointDickman.Analysis.MellinSieveQuadratic
import OAI.NumberTheory.JointDickman.Analysis.MellinPrimeSieve
import Mathlib.Data.Nat.GCD.BigOperators

namespace OAI

/-! # Literal divisor-sum remainders for the Mellin sieve -/
namespace JointDickman
open Finset
open scoped Classical ComplexConjugate

lemma primeProduct_dvd_iff (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (n : ℕ) :
    (∏ p ∈ D, p) ∣ n ↔ ∀ p ∈ D, p ∣ n := by
  induction D using Finset.induction_on with
  | empty => simp
  | @insert p D hp ih =>
    have hprime : p.Prime := hD p (mem_insert_self _ _)
    have hD' : ∀ q ∈ D, q.Prime := fun q hq => hD q (mem_insert_of_mem hq)
    have hcop : p.Coprime (∏ q ∈ D, q) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      apply (Nat.coprime_primes hprime (hD' q hq)).mpr
      intro he
      exact hp (he ▸ hq)
    rw [prod_insert hp]
    constructor
    · intro h q hq
      rcases mem_insert.mp hq with rfl | hq
      · exact dvd_trans (dvd_mul_right _ _) h
      · exact ((ih hD').mp (dvd_trans (dvd_mul_left _ _) h)) q hq
    · intro h
      apply hcop.mul_dvd_of_dvd_of_dvd (h p (mem_insert_self _ _))
      exact (ih hD').mpr (fun q hq => h q (mem_insert_of_mem hq))

lemma primeDivisorEvents_subset_iff {P D : Finset ℕ}
    (hD : D ⊆ P) (hprime : ∀ p ∈ D, p.Prime) (n : ℕ) :
    D ⊆ primeDivisorEvents P n ↔ (∏ p ∈ D, p) ∣ n := by
  rw [primeProduct_dvd_iff D hprime]
  constructor
  · intro h p hp
    exact (mem_filter.mp (h hp)).2
  · intro h p hp
    exact mem_filter.mpr ⟨hD hp, h p hp⟩

noncomputable def mellinSieveDiscreteKernel (K d : ℕ) (N t : ℝ) : ℂ :=
  mellinSampleKernel ((Icc 1 K).filter (fun n => d ∣ n)) (fun n => mellinSieveWeight N n) t

noncomputable def mellinSieveSquareWeight (N : ℝ) (S : Finset ℝ) (b : ℝ → ℂ) (n : ℕ) : ℝ :=
  mellinSieveWeight N n * ‖∑ t ∈ S, b t *
    Complex.exp (((-Real.log (n : ℝ)*t : ℝ) : ℂ)*Complex.I)‖^2

lemma mellinSieveSquareWeight_nonneg {N : ℝ} (hN : 0 ≤ N)
    (S : Finset ℝ) (b : ℝ → ℂ) (n : ℕ) : 0 ≤ mellinSieveSquareWeight N S b n := by
  exact mul_nonneg (mellinSieveWeight_nonneg hN (Nat.cast_nonneg n)) (sq_nonneg _)

lemma mellinSieveMain_div (N : ℝ) (S : Finset ℝ) (b : ℝ → ℂ) (d : ℕ) :
    mellinSieveMain N S b / d = ∑ t ∈ S, ∑ u ∈ S,
      ((b t*conj (b u))*(mellinSieveMainKernel N (t-u)/(d : ℂ))).re := by
  rw [mellinSieveMain_eq, sum_div]
  apply sum_congr rfl
  intro t _
  rw [sum_div]
  apply sum_congr rfl
  intro u _
  rw [← mul_div_assoc]
  simp only [div_eq_mul_inv, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- Only the concrete scalar divisor-sum kernel discrepancy is needed
for the weighted sieve remainder. No short-average premise is used. -/
theorem mellin_sieve_remainder_bound {P D : Finset ℕ}
    (hD : D ⊆ P) (hprime : ∀ p ∈ D, p.Prime)
    (K : ℕ) (N : ℝ) (S : Finset ℝ) (b : ℝ → ℂ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hkernel : ∀ t ∈ S, ∀ u ∈ S,
      ‖mellinSieveDiscreteKernel K (∏ p ∈ D, p) N (t-u) -
        mellinSieveMainKernel N (t-u)/((∏ p ∈ D, p : ℕ) : ℂ)‖ ≤ δ) :
    |sieveRemainder (fun n : Icc 1 K => primeDivisorEvents P n)
      (fun n => mellinSieveSquareWeight N S b n) (mellinSieveMain N S b)
      (fun p => 1/(p : ℝ)) D| ≤ δ*S.card*∑ t ∈ S, ‖b t‖^2 := by
  have hcond (n : Icc 1 K) := primeDivisorEvents_subset_iff hD hprime n
  have hi : sieveIntersection (fun n : Icc 1 K => primeDivisorEvents P n)
      (fun n => mellinSieveSquareWeight N S b n) D =
      ∑ n ∈ (Icc 1 K).filter (fun n => (∏ p ∈ D, p) ∣ n), mellinSieveSquareWeight N S b n := by
    unfold sieveIntersection
    simp_rw [hcond]
    rw [(Icc 1 K).sum_coe_sort (fun n : ℕ => if (∏ p ∈ D, p) ∣ n then
      mellinSieveSquareWeight N S b n else 0), sum_filter]
  have hp : (∏ p ∈ D, 1/(p : ℝ)) = 1/((∏ p ∈ D, p : ℕ) : ℝ) := by
    rw [prod_div_distrib]
    simp
  unfold sieveRemainder
  rw [hi, hp, mul_one_div, mellinSieveMain_div]
  rw [show (∑ n ∈ (Icc 1 K).filter (fun n => (∏ p ∈ D, p) ∣ n),
      mellinSieveSquareWeight N S b n) = ∑ t ∈ S, ∑ u ∈ S,
      ((b t*conj (b u))*mellinSieveDiscreteKernel K (∏ p ∈ D, p) N (t-u)).re from
    mellin_weighted_dual_identity _ S (fun n => mellinSieveWeight N n) b]
  exact mellin_quadratic_kernel_error S b _ _ hδ hkernel

end JointDickman

end OAI
