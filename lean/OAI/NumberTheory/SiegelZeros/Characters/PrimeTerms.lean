import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W05

theorem primeTermComparison {X n : ℝ} (hX : 1 < X) (hn : 0 < n) (hnX : n ≤ X) :
    Real.exp (-1) / n ≤ n ^ (-(1 + 1 / Real.log X)) := by
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hratio : Real.log n / Real.log X ≤ 1 :=
    (div_le_one hlogX).2 (Real.log_le_log hn hnX)
  rw [Real.rpow_def_of_pos hn]
  calc
    Real.exp (-1) / n = Real.exp (-1 - Real.log n) := by
      rw [Real.exp_sub, Real.exp_log hn]
    _ ≤ Real.exp (Real.log n * -(1 + 1 / Real.log X)) := by
      apply Real.exp_le_exp.mpr
      have heq : Real.log n * -(1 + 1 / Real.log X) =
          -Real.log n - Real.log n / Real.log X := by ring
      rw [heq]
      linarith

noncomputable def eulerTerm (χ : ℕ → ℝ) (s : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * (1 + χ n) * (n : ℝ) ^ (-s)

theorem eulerTerm_nonneg {χ : ℕ → ℝ} {s : ℝ} {n : ℕ} (hχ : -1 ≤ χ n) :
    0 ≤ eulerTerm χ s n := by
  unfold eulerTerm
  exact mul_nonneg
    (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by linarith))
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem finite_prime_restriction {χ : ℕ → ℝ} {X : ℝ} (hX : 1 < X)
    (P S : Finset ℕ) (hPS : P ⊆ S)
    (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ X ∧ χ p = 1)
    (hχ : ∀ n ∈ S, -1 ≤ χ n) :
    2 * Real.exp (-1) * (∑ p ∈ P, Real.log p / p) ≤
      ∑ n ∈ S, eulerTerm χ (1 + 1 / Real.log X) n := by
  calc
    2 * Real.exp (-1) * (∑ p ∈ P, Real.log p / p) =
        ∑ p ∈ P, 2 * Real.exp (-1) * (Real.log p / p) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ P, eulerTerm χ (1 + 1 / Real.log X) p := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpp, hpX, hpχ⟩ := hP p hp
      have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hpp.pos
      have hterm := mul_le_mul_of_nonneg_left (primeTermComparison hX hp0 hpX)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.log_natCast_nonneg p))
      simp only [eulerTerm, ArithmeticFunction.vonMangoldt_apply_prime hpp, hpχ]
      convert hterm using 1 <;> ring
    _ ≤ ∑ n ∈ S, eulerTerm χ (1 + 1 / Real.log X) n :=
      Finset.sum_le_sum_of_subset_of_nonneg hPS
        (fun n hn _ => eulerTerm_nonneg (hχ n hn))

theorem infinite_prime_restriction {χ : ℕ → ℝ} {X : ℝ} (hX : 1 < X)
    (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ X ∧ χ p = 1)
    (hχ : ∀ n, -1 ≤ χ n)
    (hsum : Summable (eulerTerm χ (1 + 1 / Real.log X))) :
    2 * Real.exp (-1) * (∑ p ∈ P, Real.log p / p) ≤
      ∑' n, eulerTerm χ (1 + 1 / Real.log X) n := by
  apply (finite_prime_restriction hX P P (fun _ h => h) hP (fun n _ => hχ n)).trans
  exact hsum.sum_le_tsum P (fun n _ => eulerTerm_nonneg (hχ n))

end WeightedTorusJets.W05

end

end SiegelZeros

end OAI
