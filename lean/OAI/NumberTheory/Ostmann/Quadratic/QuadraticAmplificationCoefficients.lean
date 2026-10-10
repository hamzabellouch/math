import Mathlib.Analysis.Complex.Norm
import OAI.NumberTheory.Ostmann.Supply.PrimeSubsetProducts

namespace OAI

/-! # The single finite coefficient array shared by all quadratic kernels -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def primeSubsetCoefficient (P : Finset ℕ) (k : ℕ)
    (c : ℂ) (e : ℕ → ℂ) (s : ℕ) : ℂ :=
  if s ∈ primeSubsetProducts P k then c * ∏ p ∈ s.primeFactors, e p else 0

theorem primeSubsetCoefficient_norm_le (P : Finset ℕ) (k : ℕ) (c : ℂ) (e : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) (he : ∀ p ∈ P, ‖e p‖ ≤ 1) (s : ℕ) :
    ‖primeSubsetCoefficient P k c e s‖ ≤ ‖c‖ := by
  unfold primeSubsetCoefficient
  split_ifs with hs
  · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hs
    have hQP := (Finset.mem_powersetCard.mp hQ).1
    rw [Nat.primeFactors_prod (fun p hp => hP p (hQP hp)), norm_mul]
    have hprod : ‖∏ p ∈ Q, e p‖ ≤ 1 := by
      rw [Complex.norm_prod]
      exact Finset.prod_le_one₀ (fun p _ => norm_nonneg (e p)) (fun p hp => he p (hQP hp))
    simpa using mul_le_mul_of_nonneg_left hprod (norm_nonneg c)
  · simp

theorem primeSubsetCoefficient_energy_le (P : Finset ℕ) (k N : ℕ) (c : ℂ) (e : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) (he : ∀ p ∈ P, ‖e p‖ ≤ 1) :
    quadraticSieveEnergy N (primeSubsetCoefficient P k c e) ≤
      (P.card.choose k : ℝ) * ‖c‖ ^ 2 := by
  let T := primeSubsetProducts P k
  let R := oddSquarefreeRange N
  let f := fun s => ‖primeSubsetCoefficient P k c e s‖ ^ 2
  have hrestrict : (∑ s ∈ R ∩ T, f s) = ∑ s ∈ R, f s := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro s hs hst
    have hn : s ∉ T := fun ht => hst (Finset.mem_inter.mpr ⟨hs, ht⟩)
    change s ∉ primeSubsetProducts P k at hn
    simp [f, primeSubsetCoefficient, hn]
  calc
    _ = ∑ s ∈ R ∩ T, f s := hrestrict.symm
    _ ≤ ∑ s ∈ T, f s :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun s _ _ => sq_nonneg _)
    _ ≤ (T.card : ℝ) * ‖c‖ ^ 2 := by
      simpa only [nsmul_eq_mul] using
        (Finset.sum_le_card_nsmul T f (‖c‖ ^ 2) (fun s _ =>
          pow_le_pow_left₀ (norm_nonneg _) (primeSubsetCoefficient_norm_le P k c e hP he s) 2))
    _ = _ := by rw [show T.card = P.card.choose k from primeSubsetProducts_card P k hP]

theorem amplification_numeric_budget (J k : ℕ) (hJ : 0 < J) :
    (J.choose k : ℝ) * ((k.factorial : ℝ) / (J : ℝ) ^ k) ^ 2 ≤
      (k.factorial : ℝ) / (J : ℝ) ^ k := by
  have hp : (0 : ℝ) < (J : ℝ) ^ k := pow_pos (by exact_mod_cast hJ) k
  have hF : (0 : ℝ) ≤ k.factorial := by positivity
  have hchoose : (k.factorial : ℝ) * (J.choose k : ℝ) ≤ (J : ℝ) ^ k := by
    exact_mod_cast (show k.factorial * J.choose k ≤ J ^ k by
      rw [← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow J k)
  have hr : ((k.factorial : ℝ) * (J.choose k : ℝ)) / (J : ℝ) ^ k ≤ 1 :=
    (div_le_one hp).mpr hchoose
  calc
    _ = ((k.factorial : ℝ) / (J : ℝ) ^ k) *
      (((k.factorial : ℝ) * (J.choose k : ℝ)) / (J : ℝ) ^ k) := by ring
    _ ≤ ((k.factorial : ℝ) / (J : ℝ) ^ k) * 1 :=
      mul_le_mul_of_nonneg_left hr (div_nonneg hF hp.le)
    _ = _ := mul_one _

/-- This is the `k! / J^k` energy bound in the manuscript, for an actual
coefficient function supported on products of distinct primes. -/
theorem quadratic_amplification_energy (P : Finset ℕ) (k N : ℕ) (e : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) (he : ∀ p ∈ P, ‖e p‖ ≤ 1) (hcard : 0 < P.card) :
    quadraticSieveEnergy N (primeSubsetCoefficient P k
      (((k.factorial : ℝ) / (P.card : ℝ) ^ k : ℝ) : ℂ) e) ≤
        (k.factorial : ℝ) / (P.card : ℝ) ^ k := by
  have hc : 0 ≤ (k.factorial : ℝ) / (P.card : ℝ) ^ k := by positivity
  have h := primeSubsetCoefficient_energy_le P k N
    (((k.factorial : ℝ) / (P.card : ℝ) ^ k : ℝ) : ℂ) e hP he
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc] at h
  exact h.trans (amplification_numeric_budget P.card k hcard)

end Ostmann

end OAI
