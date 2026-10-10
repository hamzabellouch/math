import OAI.NumberTheory.JointDickman.Amplification.CRTMean
import OAI.NumberTheory.JointDickman.Arithmetic.ConsecutivePrimeHits

namespace OAI

/-! # Exact CRT law of the prime hits of two consecutive integers -/

namespace JointDickman
open Finset

theorem consecutive_crt_mean (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (F : (P → Bool × Bool) → ℝ) :
    (∑ n ∈ range (∏ p ∈ P, p), F (fun p => consecutivePrimeHit (n : ZMod p.val))) /
        (∏ p ∈ P, (p : ℝ)) =
      ∑ x, finiteProductMass (fun (p : P) => consecutiveHitMass (1 / (p.val : ℝ))) x * F x := by
  classical
  let : ∀ p : P, NeZero p.val := fun p => ⟨(hP p.val p.property).ne_zero⟩
  have hcop : Pairwise (fun p q : P => p.val.Coprime q.val) := by
    intro p q hpq
    exact (Nat.coprime_primes (hP p p.property) (hP q q.property)).mpr
      (fun h => hpq (Subtype.ext h))
  have hc := crt_uniform_mean (fun p : P => p.val) hcop
    (fun x => F (fun p => consecutivePrimeHit (x p)))
  have hl (p : P) : finitePushMass (fun (_ : ZMod p.val) => 1 / (p.val : ℝ))
      consecutivePrimeHit = consecutiveHitMass (1 / (p.val : ℝ)) := by
    funext v
    simpa only [finitePushMass] using consecutivePrimeHit_fiber (hP p.val p.property) v
  have hp := finiteProductMass_pushforward_test (fun (p : P) (_ : ZMod p.val) => 1 / (p.val : ℝ))
    (fun (_p : P) => consecutivePrimeHit) (fun x => (F x : ℂ))
  simp only [hl] at hp
  have hp' : (∑ x, finiteProductMass (fun (p : P) => consecutiveHitMass (1 / (p.val : ℝ))) x * F x) =
      ∑ x, finiteProductMass (fun (p : P) (_ : ZMod p.val) => 1 / (p.val : ℝ)) x *
        F (fun p => consecutivePrimeHit (x p)) := by exact_mod_cast hp
  rw [P.prod_coe_sort (fun p : ℕ => p), P.prod_coe_sort (fun p : ℕ => (p : ℝ))] at hc
  exact hc.trans hp'.symm

theorem consecutive_prime_product_l1 (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ x, |finiteProductMass (fun (p : P) => consecutiveHitMass (1 / (p.val : ℝ))) x -
      finiteProductMass (fun (p : P) => independentHitMass (1 / (p.val : ℝ))) x|) ≤
      4 * ∑ p ∈ P, 1 / (p : ℝ)^2 := by
  classical
  have hq (p : P) : 0 ≤ 1 / (p.val : ℝ) ∧ 1 / (p.val : ℝ) ≤ 1 := by
    have h1 : (1 : ℝ) ≤ p.val := by exact_mod_cast (hP p.val p.property).one_le
    exact ⟨by positivity, by simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) h1⟩
  have htwo (p : P) : 2 * (1 / (p.val : ℝ)) ≤ 1 := by
    have h2 : (2 : ℝ) ≤ p.val := by exact_mod_cast (hP p.val p.property).two_le
    have hp : (0 : ℝ) < p.val := by linarith
    calc
      2 * (1 / (p.val : ℝ)) = 2 / (p.val : ℝ) := by ring
      _ ≤ 1 := (div_le_one hp).mpr h2
  have h := finiteProductMass_l1_le
    (fun (p : P) => consecutiveHitMass (1 / (p.val : ℝ)))
    (fun (p : P) => independentHitMass (1 / (p.val : ℝ)))
    (fun p v => consecutiveHitMass_nonneg (hq p).1 (htwo p) v)
    (fun p v => mul_nonneg (bernoulliBitMass_nonneg (hq p) v.1)
      (bernoulliBitMass_nonneg (hq p) v.2))
    (fun p => consecutiveHitMass_sum _) (fun p => independentHitMass_sum _)
  simp only [consecutiveHitMass_l1, one_div_pow, ← mul_sum] at h
  rw [P.sum_coe_sort (fun p : ℕ => 1 / (p : ℝ)^2)] at h
  exact h

end JointDickman

end OAI
