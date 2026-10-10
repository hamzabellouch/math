import OAI.NumberTheory.JointDickman.Arithmetic.SieveInterval
import OAI.NumberTheory.JointDickman.Amplification.ProductComparison

namespace OAI

/-! # Independently randomized root sets

Averaging the uniform deterministic bound preserves its remainder and
factors its main term. The root sets at a prime may contain coincident
roots of several forms; only their union and its cardinality matter.
-/

namespace JointDickman

open Finset

/-- Exact expectation of a product under the finite product law. -/
theorem finiteProductMass_product_expectation {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (μ F : ∀ i, Ω i → ℝ) :
    (∑ ω, finiteProductMass μ ω * ∏ i, F i (ω i)) =
      ∏ i, ∑ x, μ i x * F i x := by
  simp_rw [finiteProductMass, ← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => μ i x * F i x)).symm

/-- Arbitrary independent choices of at most `k` roots per prime satisfy
the interval upper bound, with one uniform polynomial remainder. -/
theorem randomized_root_interval_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (Ω : P → Type) [∀ p, Fintype (Ω p)]
      (μ : ∀ p, Ω p → ℝ) (A : ∀ p : P, Ω p → Finset (ZMod p.val))
      (a b Z : ℕ), a ≤ b → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 2 * k ≤ p) →
      (∀ p x, 0 ≤ μ p x) → (∀ p, ∑ x, μ p x = 1) →
      (∀ p x, (A p x).card ≤ k) →
      (∑ n ∈ Ico a b, ∏ p : P, ∑ x, μ p x *
        (if (n : ZMod p.val) ∈ A p x then 0 else 1)) ≤
      C * ((b : ℝ) - a) * (∏ p : P, ∑ x, μ p x *
        (1 - ((A p x).card : ℝ) / p.val)) +
      2 * (Z + 1 : ℝ) * (Z : ℝ) ^ k := by
  classical
  obtain ⟨C, hC, hbound⟩ := weighted_interval_sieve_polynomial hFord hM hk
  refine ⟨C, hC, ?_⟩
  intro P Ω _ μ A a b Z hab hZ hP hμ hμ1 hA
  let roots (ω : ∀ p, Ω p) (q : ℕ) : Finset (ZMod q) :=
    if hq : q ∈ P then A ⟨q, hq⟩ (ω ⟨q, hq⟩) else ∅
  have hroot (ω : ∀ p, Ω p) (p : P) : roots ω p.val = A p (ω p) := by
    simp [roots, p.property]
  have hprod (ω : ∀ p, Ω p) (n : ℕ) :
      (∏ p ∈ rootEvents P (roots ω) n, (0 : ℝ)) =
        ∏ p : P, if (n : ZMod p.val) ∈ A p (ω p) then 0 else 1 := by
    calc
      _ = ∏ p ∈ P, if (n : ZMod p) ∈ roots ω p then (0 : ℝ) else 1 := by
        simp only [rootEvents, prod_filter]
      _ = ∏ p : P, if (n : ZMod p.val) ∈ roots ω p.val then (0 : ℝ) else 1 :=
        (P.prod_coe_sort (fun p : ℕ => if (n : ZMod p) ∈ roots ω p then (0 : ℝ) else 1)).symm
      _ = _ := by simp_rw [hroot]
  have hpoint (ω : ∀ p, Ω p) :
      (∑ n ∈ Ico a b, ∏ p : P,
        if (n : ZMod p.val) ∈ A p (ω p) then (0 : ℝ) else 1) ≤
        C * ((b : ℝ) - a) *
          (∏ p : P, (1 - ((A p (ω p)).card : ℝ) / p.val)) +
        2 * (Z + 1 : ℝ) * (Z : ℝ) ^ k := by
    have h := hbound P (roots ω) (fun _ => 0) a b Z hab hZ hP
      (fun p hp => by simpa [roots, hp] using hA ⟨p, hp⟩ (ω ⟨p, hp⟩))
      (by intros; norm_num)
    simp_rw [hprod] at h
    simpa only [mul_zero, add_zero,
      ← P.prod_coe_sort (fun p : ℕ => 1 - ((roots ω p).card : ℝ) / p), hroot] using h
  calc
    _ = ∑ ω, finiteProductMass μ ω * (∑ n ∈ Ico a b, ∏ p : P,
        if (n : ZMod p.val) ∈ A p (ω p) then (0 : ℝ) else 1) := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro n _
      exact (finiteProductMass_product_expectation μ
        (fun p x => if (n : ZMod p.val) ∈ A p x then 0 else 1)).symm
    _ ≤ ∑ ω, finiteProductMass μ ω *
        (C * ((b : ℝ) - a) * (∏ p : P, (1 - ((A p (ω p)).card : ℝ) / p.val)) +
          2 * (Z + 1 : ℝ) * (Z : ℝ) ^ k) := by
      apply sum_le_sum
      intro ω _
      exact mul_le_mul_of_nonneg_left (hpoint ω) (finiteProductMass_nonneg μ hμ ω)
    _ = _ := by
      simp_rw [mul_add, sum_add_distrib]
      have hfirst : (∑ ω, finiteProductMass μ ω *
          (C * ((b : ℝ) - a) * ∏ p : P, (1 - ((A p (ω p)).card : ℝ) / p.val))) =
          C * ((b : ℝ) - a) * ∏ p : P, ∑ x, μ p x *
            (1 - ((A p x).card : ℝ) / p.val) := by
        rw [← finiteProductMass_product_expectation, mul_sum]
        apply sum_congr rfl
        intro ω _
        ring
      rw [hfirst, ← sum_mul, finiteProductMass_sum μ hμ1, one_mul]

end JointDickman

end OAI
