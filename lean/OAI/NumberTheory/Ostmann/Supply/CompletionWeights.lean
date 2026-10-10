import OAI.NumberTheory.Ostmann.Supply.CompletionCounting

namespace OAI

namespace Ostmann.Supply.CompletionCounting
open Finset

def completions (U t : ℕ) : Finset ℕ :=
  (Icc 1 U).filter (fun u => Squarefree u ∧ Nat.Coprime u t)

theorem completion_mul_squarefree {U t u : ℕ} (ht : Squarefree t)
    (hu : u ∈ completions U t) : Squarefree (t * u) := by
  obtain ⟨hu, hsu, hcu⟩ := mem_filter.mp hu
  exact (Nat.squarefree_mul hcu.symm).mpr ⟨ht, hsu⟩

def primeProduct (κ : ℕ → ℝ) (u : ℕ) : ℝ := ∏ p ∈ u.primeFactors, κ p

theorem primeProduct_mul {t u : ℕ} (h : Nat.Coprime t u) (κ : ℕ → ℝ) :
    primeProduct κ (t * u) = primeProduct κ t * primeProduct κ u := by
  simp only [primeProduct, h.primeFactors_mul, prod_union h.disjoint_primeFactors]

theorem primeProduct_pos (κ : ℕ → ℝ) (hκ : ∀ p, 0 < κ p) (u : ℕ) :
    0 < primeProduct κ u := prod_pos (fun p _ => hκ p)

theorem exp_neg_le_primeProduct (κ : ℕ → ℝ) (hκ : ∀ p, 0 < κ p)
    (u : ℕ) {B : ℝ} (hcost : primeCost (fun p => |Real.log (κ p)|) u ≤ B) :
    Real.exp (-B) ≤ primeProduct κ u := by
  have hsum : -B ≤ ∑ p ∈ u.primeFactors, Real.log (κ p) := by
    calc
      -B ≤ -primeCost (fun p => |Real.log (κ p)|) u := neg_le_neg hcost
      _ = ∑ p ∈ u.primeFactors, -|Real.log (κ p)| := by simp [primeCost]
      _ ≤ _ := sum_le_sum (fun p hp => neg_abs_le (Real.log (κ p)))
  have hlog : Real.log (primeProduct κ u) = ∑ p ∈ u.primeFactors, Real.log (κ p) :=
    Real.log_prod (fun p hp => (hκ p).ne')
  calc
    _ ≤ Real.exp (∑ p ∈ u.primeFactors, Real.log (κ p)) := Real.exp_le_exp.mpr hsum
    _ = _ := by rw [← hlog, Real.exp_log (primeProduct_pos κ hκ u)]

theorem exp_neg_le_primeProduct_inv (κ : ℕ → ℝ) (hκ : ∀ p, 0 < κ p)
    (u : ℕ) {B : ℝ} (hcost : primeCost (fun p => |Real.log (κ p)|) u ≤ B) :
    Real.exp (-B) ≤ (primeProduct κ u)⁻¹ := by
  have hi : ∀ p, 0 < (κ p)⁻¹ := fun p => inv_pos.mpr (hκ p)
  have hc : primeCost (fun p => |Real.log ((κ p)⁻¹)|) u ≤ B := by
    simpa only [Real.log_inv, abs_neg] using hcost
  simpa [primeProduct] using exp_neg_le_primeProduct (fun p => (κ p)⁻¹) hi u hc

theorem sum_primeProduct_ge (U t : ℕ) (ht : t ≠ 0) (κ : ℕ → ℝ)
    (hκ : ∀ p, 0 < κ p) {B : ℝ} (hB : 0 < B)
    (hcop : ∑ p ∈ t.primeFactors, (1 : ℝ) / p ≤ 1 / 16)
    (hmean : ∑ p ∈ primesUpTo U, |Real.log (κ p)| / p ≤ B / 16) :
    (U : ℝ) / 8 * Real.exp (-B) ≤ ∑ u ∈ completions U t, primeProduct κ u := by
  classical
  let good := goodCompletions U t (fun p => |Real.log (κ p)|) B
  have hcard : (U : ℝ) / 8 ≤ (good.card : ℝ) :=
    card_goodCompletions_ge U t ht _ (fun p => abs_nonneg _) hB hcop hmean
  have hsub : good ⊆ completions U t := by
    intro u hu
    obtain ⟨hu, hsq, hcp, hcost⟩ := mem_filter.mp hu
    exact mem_filter.mpr ⟨hu, hsq, hcp⟩
  calc
    _ ≤ (good.card : ℝ) * Real.exp (-B) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ = ∑ u ∈ good, Real.exp (-B) := by simp
    _ ≤ ∑ u ∈ good, primeProduct κ u := by
      apply sum_le_sum
      intro u hu
      exact exp_neg_le_primeProduct κ hκ u (mem_filter.mp hu).2.2.2
    _ ≤ ∑ u ∈ completions U t, primeProduct κ u := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro u hu hnot
      exact (primeProduct_pos κ hκ u).le

theorem sum_primeProduct_inv_ge (U t : ℕ) (ht : t ≠ 0) (κ : ℕ → ℝ)
    (hκ : ∀ p, 0 < κ p) {B : ℝ} (hB : 0 < B)
    (hcop : ∑ p ∈ t.primeFactors, (1 : ℝ) / p ≤ 1 / 16)
    (hmean : ∑ p ∈ primesUpTo U, |Real.log (κ p)| / p ≤ B / 16) :
    (U : ℝ) / 8 * Real.exp (-B) ≤ ∑ u ∈ completions U t, (primeProduct κ u)⁻¹ := by
  have hi : ∀ p, 0 < (κ p)⁻¹ := fun p => inv_pos.mpr (hκ p)
  have hm : ∑ p ∈ primesUpTo U, |Real.log ((κ p)⁻¹)| / p ≤ B / 16 := by
    simpa only [Real.log_inv, abs_neg] using hmean
  simpa [primeProduct] using sum_primeProduct_ge U t ht (fun p => (κ p)⁻¹) hi hB hcop hm

end Ostmann.Supply.CompletionCounting

end OAI
