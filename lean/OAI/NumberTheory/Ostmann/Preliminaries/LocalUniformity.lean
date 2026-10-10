import OAI.NumberTheory.Ostmann.Preliminaries.CollisionScale

namespace OAI

open Erdos970

namespace Ostmann.Preliminaries
open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
theorem weighted_A_test_error_le (d : Decomposition) (Q : ℕ)
    (a : α → ℕ) (μ : α → ℝ) (b : β → ℕ) (ν : β → ℝ)
    (f : (p : PrimeUpTo Q) → ZMod p.val → ℂ)
    (hf : ∀ p, ∑ r, ‖f p r‖ ^ 2 ≤ p.val) :
    (∑ p : PrimeUpTo Q, (Real.log p.val / p.val) *
      ‖(∑ i, (μ i : ℂ) * f p (a i)) -
        ∑ r, (uniformMass (d.residueSupport p.val) r : ℂ) * f p r‖ ^ 2) ≤
      collisionStability d Q a μ b ν := by
  apply Finset.sum_le_sum
  intro p _
  have hp : (0 : ℝ) < p.val := by exact_mod_cast (primeUpTo_prime p).pos
  have hlog : 0 ≤ Real.log (p.val : ℝ) := Real.log_nonneg
    (by exact_mod_cast (primeUpTo_prime p).one_le)
  have ht := actual_A_test_error d p.val a μ (f p) (hf p)
  obtain ⟨_, h2, h3⟩ := collision_stability_terms_nonneg (d.residueSupport p.val)
    (d.residueSupport_nonempty p.val) (d.residueSupport_compl_nonempty p.val (primeUpTo_prime p))
    (projectedMass (fun i => (a i : ZMod p.val)) μ)
    (projectedMass (fun i => -(b i : ZMod p.val)) ν)
  have hd : uniformDefect (d.residueSupport p.val)
      (projectedMass (fun i => (a i : ZMod p.val)) μ) ≤
      localCollisionStability d p.val a μ b ν := by
    unfold localCollisionStability Decomposition.residueDensity
    linarith
  calc
    _ ≤ (Real.log p.val / p.val) * ((p.val : ℝ) *
        uniformDefect (d.residueSupport p.val) (projectedMass (fun i => (a i : ZMod p.val)) μ)) :=
      mul_le_mul_of_nonneg_left ht (div_nonneg hlog hp.le)
    _ = Real.log p.val * uniformDefect (d.residueSupport p.val)
        (projectedMass (fun i => (a i : ZMod p.val)) μ) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hd hlog

omit [DecidableEq α] [DecidableEq β] in
theorem weighted_neg_B_test_error_le (d : Decomposition) (Q : ℕ)
    (a : α → ℕ) (μ : α → ℝ) (b : β → ℕ) (ν : β → ℝ)
    (f : (p : PrimeUpTo Q) → ZMod p.val → ℂ)
    (hf : ∀ p, ∑ r, ‖f p r‖ ^ 2 ≤ p.val) :
    (∑ p : PrimeUpTo Q, (Real.log p.val / p.val) *
      ‖(∑ i, (ν i : ℂ) * f p (-(b i : ZMod p.val))) -
        ∑ r, (uniformMass (d.residueSupport p.val)ᶜ r : ℂ) * f p r‖ ^ 2) ≤
      collisionStability d Q a μ b ν := by
  apply Finset.sum_le_sum
  intro p _
  have hp : (0 : ℝ) < p.val := by exact_mod_cast (primeUpTo_prime p).pos
  have hlog : 0 ≤ Real.log (p.val : ℝ) := Real.log_nonneg
    (by exact_mod_cast (primeUpTo_prime p).one_le)
  have ht := actual_neg_B_test_error d p.val b ν (f p) (hf p)
  obtain ⟨h1, _, h3⟩ := collision_stability_terms_nonneg (d.residueSupport p.val)
    (d.residueSupport_nonempty p.val) (d.residueSupport_compl_nonempty p.val (primeUpTo_prime p))
    (projectedMass (fun i => (a i : ZMod p.val)) μ)
    (projectedMass (fun i => -(b i : ZMod p.val)) ν)
  have hd : uniformDefect (d.residueSupport p.val)ᶜ
      (projectedMass (fun i => -(b i : ZMod p.val)) ν) ≤
      localCollisionStability d p.val a μ b ν := by
    unfold localCollisionStability Decomposition.residueDensity
    linarith
  calc
    _ ≤ (Real.log p.val / p.val) * ((p.val : ℝ) *
        uniformDefect (d.residueSupport p.val)ᶜ (projectedMass (fun i => -(b i : ZMod p.val)) ν)) :=
      mul_le_mul_of_nonneg_left ht (div_nonneg hlog hp.le)
    _ = Real.log p.val * uniformDefect (d.residueSupport p.val)ᶜ
        (projectedMass (fun i => -(b i : ZMod p.val)) ν) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hd hlog

omit [DecidableEq α] [DecidableEq β] in
theorem weighted_density_penalty_le (d : Decomposition) (Q : ℕ)
    (a : α → ℕ) (μ : α → ℝ) (b : β → ℕ) (ν : β → ℝ) :
    (∑ p : PrimeUpTo Q, Real.log p.val *
      (((d.residueDensity p.val)⁻¹ + (1 - d.residueDensity p.val)⁻¹ - 4) / p.val)) ≤
      collisionStability d Q a μ b ν := by
  apply Finset.sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg
    (by exact_mod_cast (primeUpTo_prime p).one_le))
  have h1 := uniformDefect_nonneg (d.residueSupport p.val)
    (projectedMass (fun i => (a i : ZMod p.val)) μ)
  have h2 := uniformDefect_nonneg (d.residueSupport p.val)ᶜ
    (projectedMass (fun i => -(b i : ZMod p.val)) ν)
  unfold localCollisionStability
  linarith

theorem probability_test_norm_le_of_norm_le_one (p : ℕ) [NeZero p]
    (f : ZMod p → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) : ∑ x, ‖f x‖ ^ 2 ≤ p := by
  calc
    (∑ x, ‖f x‖ ^ 2) ≤ ∑ _ : ZMod p, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      have h := hf x
      have hn := norm_nonneg (f x)
      nlinarith
    _ = p := by simp [ZMod.card p]

end Ostmann.Preliminaries

end OAI
