import OAI.NumberTheory.Ostmann.ZeroDensity.DensityBlockWeights

namespace OAI

/-! # A uniform mean square for every finite dyadic tail -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators Classical

 theorem densityFiniteSquare_tail_assembly :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ N → 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      10 * (Q : ℝ) * T ≤ N → ∀ J : ℕ,
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ∫ t in Icc (-T) T,
        ‖∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ioc (2 ^ j * N) (2 ^ (j + 1) * N),
          densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n‖ ^ 2) ≤
          C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * (1 + Real.log N) ^ 3 := by
  obtain ⟨C, hC, hb⟩ := densityFiniteSquare_dyadic_mean
  refine ⟨4 * C * densityBlockEnergyConstant, by
    have := densityBlockEnergyConstant_pos
    positivity, ?_⟩
  intro N Q hN hQ T hT hscale J F hF
  let K := ((N : ℝ) + (Q : ℝ) ^ 2 * T) * (1 + Real.log N) ^ 3
  have hK : 0 ≤ K := by
    have hNl := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN)
    dsimp [K]
    positivity
  let f := fun (χ : PrimitiveComplexCharacter) (j : ℕ) (t : ℝ) =>
    ∑ n ∈ Finset.Ioc (2 ^ j * N) (2 ^ (j + 1) * N),
      densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n
  have hf (χ : PrimitiveComplexCharacter) (j : ℕ) : ContinuousOn (f χ j) (Icc (-T) T) := by
    apply densityFiniteSquare_continuousOn χ _ _ T hT
    intro n hn
    have hnp : 0 < n := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hn).1
    omega
  have hs : (∑ j ∈ Finset.range J,
      (∑ χ ∈ F, ∫ t in Icc (-T) T, ‖f χ j t‖ ^ 2) / (3 / 4 : ℝ) ^ j) ≤
      C * K * densityBlockEnergyConstant := by
    calc
      _ ≤ ∑ j ∈ Finset.range J,
          (C * K * (j + 2 : ℝ) ^ 3 / (2 : ℝ) ^ j) / (3 / 4 : ℝ) ^ j := by
        apply Finset.sum_le_sum
        intro j _
        have hj : (∑ χ ∈ F, ∫ t in Icc (-T) T, ‖f χ j t‖ ^ 2) ≤
            C * K * (j + 2 : ℝ) ^ 3 / (2 : ℝ) ^ j := by
          simpa only [f, K, mul_assoc] using hb N Q hN hQ T hT hscale j F hF
        exact div_le_div_of_nonneg_right hj (by positivity)
      _ = C * K * ∑ j ∈ Finset.range J,
          ((j + 2 : ℝ) ^ 3 / (2 : ℝ) ^ j) / (3 / 4 : ℝ) ^ j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (density_block_energy_sum J) (mul_nonneg hC.le hK)
  have h := density_weighted_block_mean F (Finset.range J) f (fun j => (3 / 4 : ℝ) ^ j)
    (fun j _ => by positivity) T (fun χ _ j _ => hf χ j)
  apply h.trans
  calc
    _ ≤ (∑ j ∈ Finset.range J, (3 / 4 : ℝ) ^ j) * (C * K * densityBlockEnergyConstant) :=
      mul_le_mul_of_nonneg_left hs (Finset.sum_nonneg (fun _ _ => by positivity))
    _ ≤ 4 * (C * K * densityBlockEnergyConstant) :=
      mul_le_mul_of_nonneg_right (density_block_weight_sum J)
        (mul_nonneg (mul_nonneg hC.le hK) densityBlockEnergyConstant_pos.le)
    _ = _ := by dsimp [K]; ring

end Ostmann

end OAI
