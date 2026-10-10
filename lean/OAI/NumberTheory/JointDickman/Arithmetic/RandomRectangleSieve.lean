import OAI.NumberTheory.JointDickman.Arithmetic.SieveRectangle
import OAI.NumberTheory.JointDickman.Arithmetic.RandomRootSieve

namespace OAI

/-! # Independent random forbidden sets in residue planes -/

namespace JointDickman

open Finset

theorem randomized_pair_rectangle_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (Ω : P → Type) [∀ p, Fintype (Ω p)]
      (μ : ∀ p, Ω p → ℝ) (A : ∀ p : P, Ω p → Finset (ZMod p.val × ZMod p.val))
      (a b c d Z : ℕ), a ≤ b → c ≤ d → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 2 * k ≤ p) →
      (∀ p x, 0 ≤ μ p x) → (∀ p, ∑ x, μ p x = 1) →
      (∀ p x, (A p x).card ≤ k * p.val) →
      (∑ r ∈ Ico a b, ∑ s ∈ Ico c d, ∏ p : P, ∑ x, μ p x *
        (if ((r : ZMod p.val), (s : ZMod p.val)) ∈ A p x then 0 else 1)) ≤
      C * ((b : ℝ) - a) * ((d : ℝ) - c) * (∏ p : P, ∑ x, μ p x *
        (1 - ((A p x).card : ℝ) / (p.val : ℝ) ^ 2)) +
      2 * (((b : ℝ) - a) + ((d : ℝ) - c) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ k := by
  classical
  obtain ⟨C, hC, hbound⟩ := weighted_rectangle_sieve hFord hM hk
  refine ⟨C, hC, ?_⟩
  intro P Ω _ μ A a b c d Z hab hcd hZ hP hμ hμ1 hA
  let R := 2 * (((b : ℝ) - a) + ((d : ℝ) - c) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ k
  let roots (ω : ∀ p, Ω p) (q : ℕ) : Finset (ZMod q × ZMod q) :=
    if hq : q ∈ P then A ⟨q, hq⟩ (ω ⟨q, hq⟩) else ∅
  have hroot (ω : ∀ p, Ω p) (p : P) : roots ω p.val = A p (ω p) := by
    simp [roots, p.property]
  have hprod (ω : ∀ p, Ω p) (r s : ℕ) :
      (∏ p ∈ pairRootEvents P (roots ω) r s, (0 : ℝ)) =
        ∏ p : P, if ((r : ZMod p.val), (s : ZMod p.val)) ∈ A p (ω p) then 0 else 1 := by
    calc
      _ = ∏ p ∈ P, if ((r : ZMod p), (s : ZMod p)) ∈ roots ω p then (0 : ℝ) else 1 := by
        simp only [pairRootEvents, prod_filter]
      _ = ∏ p : P, if ((r : ZMod p.val), (s : ZMod p.val)) ∈ roots ω p.val then (0 : ℝ) else 1 :=
        (P.prod_coe_sort (fun p : ℕ =>
          if ((r : ZMod p), (s : ZMod p)) ∈ roots ω p then (0 : ℝ) else 1)).symm
      _ = _ := by simp_rw [hroot]
  have hpoint (ω : ∀ p, Ω p) :
      (∑ r ∈ Ico a b, ∑ s ∈ Ico c d, ∏ p : P,
        if ((r : ZMod p.val), (s : ZMod p.val)) ∈ A p (ω p) then (0 : ℝ) else 1) ≤
        C * ((b : ℝ) - a) * ((d : ℝ) - c) *
          (∏ p : P, (1 - ((A p (ω p)).card : ℝ) / (p.val : ℝ) ^ 2)) + R := by
    have h := hbound P (roots ω) (fun _ => 0) a b c d Z hab hcd hZ hP
      (fun p hp => by simpa [roots, hp] using hA ⟨p, hp⟩ (ω ⟨p, hp⟩))
      (by intros; norm_num)
    simp_rw [hprod] at h
    simpa only [mul_zero, add_zero,
      ← P.prod_coe_sort (fun p : ℕ => 1 - ((roots ω p).card : ℝ) / (p : ℝ) ^ 2), hroot] using h
  calc
    _ = ∑ ω, finiteProductMass μ ω *
        (∑ r ∈ Ico a b, ∑ s ∈ Ico c d, ∏ p : P,
          if ((r : ZMod p.val), (s : ZMod p.val)) ∈ A p (ω p) then (0 : ℝ) else 1) := by
      symm
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro r _
      rw [sum_comm]
      apply sum_congr rfl
      intro s _
      exact (finiteProductMass_product_expectation μ
        (fun p x => if ((r : ZMod p.val), (s : ZMod p.val)) ∈ A p x then 0 else 1))
    _ ≤ ∑ ω, finiteProductMass μ ω *
        (C * ((b : ℝ) - a) * ((d : ℝ) - c) *
          (∏ p : P, (1 - ((A p (ω p)).card : ℝ) / (p.val : ℝ) ^ 2)) + R) := by
      apply sum_le_sum
      intro ω _
      exact mul_le_mul_of_nonneg_left (hpoint ω) (finiteProductMass_nonneg μ hμ ω)
    _ = _ := by
      simp_rw [mul_add, sum_add_distrib]
      have hfirst : (∑ ω, finiteProductMass μ ω *
          (C * ((b : ℝ) - a) * ((d : ℝ) - c) *
            ∏ p : P, (1 - ((A p (ω p)).card : ℝ) / (p.val : ℝ) ^ 2))) =
          C * ((b : ℝ) - a) * ((d : ℝ) - c) * ∏ p : P, ∑ x, μ p x *
            (1 - ((A p x).card : ℝ) / (p.val : ℝ) ^ 2) := by
        rw [← finiteProductMass_product_expectation, mul_sum]
        apply sum_congr rfl
        intro ω _
        ring
      rw [hfirst, ← sum_mul, finiteProductMass_sum μ hμ1, one_mul]
      dsimp [R]
      ring

end JointDickman

end OAI
