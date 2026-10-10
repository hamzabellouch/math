import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDyadicBlockCost
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDetectorPolynomial

namespace OAI

/-! # Uniform estimates for the actual detector's dyadic blocks -/

namespace Ostmann

open scoped BigOperators Classical

 theorem density_actual_block_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ X M Q : ℕ, 1 ≤ X → X ≤ M → 1 ≤ Q →
      ∀ Y T σ : ℝ, 2 ≤ Y → 1 ≤ T → 1 / 2 ≤ σ → σ ≤ 1 →
      ∀ {ι : Type} (R : Finset ι) (c : ι → PrimitiveComplexCharacter) (t β : ι → ℝ),
      (∀ i ∈ R, (c i).modulus ≤ Q) → (∀ i ∈ R, |t i| ≤ T) →
      (∀ i ∈ R, ∀ j ∈ R, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∀ i ∈ R, σ ≤ β i ∧ β i ≤ 1) →
      (∑ i ∈ R, ‖densityCharacterPolynomial (Finset.Ioc M (2 * M))
        (densityVerticalCoeff (densityPolynomialCoefficient X Y) (β i)) (c i).character (t i)‖ ^ 2) ≤
        C * (1 + Real.log (2 * Y + 1)) ^ 7 *
          (Y ^ (2 - 2 * σ) + (Q : ℝ) ^ 2 * T * (X : ℝ) ^ (1 - 2 * σ)) := by
  obtain ⟨C, hC, hb⟩ := density_divisor_block_sieve
  refine ⟨792 * C, by positivity, ?_⟩
  intro X M Q hX hXM hQ Y T σ hY hT hσ hσ1 ι R c t β hc ht hs hβ
  have hM : 1 ≤ M := hX.trans hXM
  have hXp : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hMp : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  by_cases hMY : (M : ℝ) ≤ Y
  · have hU : Finset.Ioc M (2 * M) ⊆ Finset.Icc M (2 * M) := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ioc.mp hn).1.le, (Finset.mem_Ioc.mp hn).2⟩
    have h := hb M (2 * M) Q hM hQ T σ hT (by linarith) hσ1 _ hU
      (densityPolynomialCoefficient X Y)
      (fun n _ => densityPolynomialCoefficient_norm X Y (by linarith) n) R c t β hc ht hs hβ
    have hcost := density_dyadic_total_cost C X M Y Q T σ hC.le hXp
      (by exact_mod_cast hXM) hMY hT hσ hσ1
    apply h.trans
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using hcost
  · have hz (i : ι) : densityCharacterPolynomial (Finset.Ioc M (2 * M))
        (densityVerticalCoeff (densityPolynomialCoefficient X Y) (β i)) (c i).character (t i) = 0 := by
      unfold densityCharacterPolynomial
      apply Finset.sum_eq_zero
      intro n hn
      have hyn : Y ≤ n := (le_of_not_ge hMY).trans (by exact_mod_cast (Finset.mem_Ioc.mp hn).1.le)
      rw [densityVerticalCoeff, densityPolynomialCoefficient_above X n Y (by linarith) hyn]
      simp
    simp only [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero]
    have hl : 0 ≤ Real.log (2 * Y + 1) := Real.log_nonneg (by linarith)
    positivity

end Ostmann

end OAI
