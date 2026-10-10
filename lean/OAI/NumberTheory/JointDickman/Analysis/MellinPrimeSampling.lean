import OAI.NumberTheory.JointDickman.Analysis.MellinSieveRemainder

namespace OAI

/-! # Sparse prime sampling from concrete divisor-sum discrepancies

The constant is unconditional: it comes from the proved upper sieve.
Only the explicitly displayed finite logarithmic kernels remain to be
estimated in applications.
-/
namespace JointDickman
open Finset TwoPointCorrelations
open scoped Classical

/-- A separated sample set gains the prime density, provided its actual
smooth divisor sums have the stated error. -/
theorem mellin_prime_sampling : ∃ C : ℝ, 0 < C ∧
    ∀ (K Z : ℕ) (P Q : Finset ℕ) (N : ℝ) (S : Finset ℝ) (δ : ℝ),
      2 ≤ Z → 0 < N → 0 ≤ δ →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z) →
      Q ⊆ Icc 1 K → (∀ q ∈ Q, q.Prime ∧ Z < q) →
      (∀ q ∈ Q, N ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2*N) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|) →
      (∀ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p) ≤ Z),
        ∀ t ∈ S, ∀ u ∈ S,
          ‖mellinSieveDiscreteKernel K (∏ p ∈ D, p) N (t-u) -
            mellinSieveMainKernel N (t-u)/((∏ p ∈ D, p : ℕ) : ℂ)‖ ≤ δ) →
      ∀ a : ℕ → ℂ,
      (∑ t ∈ S, ‖mrtExponentialPolynomial Q a (fun n => -Real.log (n : ℝ)) t‖^2) ≤
        8*(32*C*N*(∏ p ∈ P, (1-1/(p : ℝ))) + (Z+1:ℕ)*δ*S.card)*
          ∑ q ∈ Q, ‖a q‖^2 := by
  obtain ⟨C, hC, hsieve⟩ := prime_weighted_sieve
  refine ⟨C, hC, ?_⟩
  intro K Z P Q N S δ hZ hN hδ hP hQ hQprime hQN hsep hkernel a
  have hprod : 0 ≤ ∏ p ∈ P, (1-1/(p : ℝ)) := by
    apply prod_nonneg
    intro p hp
    have hp1 : (1:ℝ) ≤ p := by exact_mod_cast (hP p hp).1.one_lt.le
    exact sub_nonneg.mpr ((div_le_one (by linarith : (0:ℝ) < p)).mpr hp1)
  have hcost : 0 ≤ 8*(32*C*N*(∏ p ∈ P, (1-1/(p : ℝ))) +
      (Z+1:ℕ)*δ*S.card) := by positivity
  apply mellin_samples_of_dual Q S a hcost
  intro b
  let B : ℝ := ∑ t ∈ S, ‖b t‖^2
  have hB : 0 ≤ B := sum_nonneg (fun _ _ => sq_nonneg _)
  have hR : 0 ≤ δ*S.card*B := by positivity
  have hrem (D : Finset ℕ)
      (hD : D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p) ≤ Z)) :
      |sieveRemainder (fun n : Icc 1 K => primeDivisorEvents P n)
        (fun n => mellinSieveSquareWeight N S b n) (mellinSieveMain N S b)
        (fun p => 1/(p : ℝ)) D| ≤ δ*S.card*B := by
    have hDP := mem_powerset.mp (mem_filter.mp hD).1
    exact mellin_sieve_remainder_bound hDP (fun p hp => (hP p (hDP hp)).1)
      K N S b hδ (hkernel D hD)
  have hs := hsieve K Z P Q (mellinSieveSquareWeight N S b)
    (mellinSieveMain N S b) (δ*S.card*B) hZ
    (mellinSieveMain_nonneg hN.le S b) hR hP hQ hQprime
    (fun n _ => mellinSieveSquareWeight_nonneg hN.le S b n) hrem
  have hmain := mellinSieveMain_bound hN.le S hsep b
  have hupper : (∑ q ∈ Q, mellinSieveSquareWeight N S b q) ≤
      (32*C*N*(∏ p ∈ P, (1-1/(p : ℝ))) + (Z+1:ℕ)*δ*S.card)*B := by
    apply hs.trans
    calc
      _ ≤ C*(32*N*B)*(∏ p ∈ P, (1-1/(p : ℝ))) + (Z+1:ℕ)*(δ*S.card*B) := by
        apply add_le_add _ le_rfl
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmain hC.le) hprod
      _ = _ := by ring
  have hlower : (1/8:ℝ)*(∑ q ∈ Q, ‖∑ t ∈ S, b t *
      Complex.exp (((-Real.log (q : ℝ)*t : ℝ) : ℂ)*Complex.I)‖^2) ≤
        ∑ q ∈ Q, mellinSieveSquareWeight N S b q := by
    rw [mul_sum]
    apply sum_le_sum
    intro q hq
    exact mul_le_mul_of_nonneg_right
      (mellinSieveWeight_interval hN (hQN q hq).1 (hQN q hq).2) (sq_nonneg _)
  have hh := hlower.trans hupper
  change _ ≤ _*B
  nlinarith

end JointDickman

end OAI
