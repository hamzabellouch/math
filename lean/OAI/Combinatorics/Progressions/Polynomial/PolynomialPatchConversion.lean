import OAI.Combinatorics.Progressions.Nilpotent.PolynomialPatchWeightedChartNiltest

namespace OAI

section

namespace Erdos3

open scoped NNReal TensorProduct

theorem polynomial_patch_to_niltest (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] {d : ℕ}
      (A : PolynomialPatch σ s d) (p : ℝ),
      0 ≤ p → (Fintype.card σ : ℝ) ≤ p → (d : ℝ) ≤ p →
      Real.log (2 + (A.kernel.lip : ℝ)) ≤ p →
      ∃ B : PolynomialPatch σ s d, B.weight = A.weight ∧ B.kernel = A.kernel ∧
        (letI := polynomialShearIndexFintype B.weight (fun i => B.weight_pos i)
         letI := moduleTopology ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra B.weight ℚ)
         letI := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra B.weight ℚ)
         letI := realification_moduleTopology_t2 (polynomialShearOrderedBasis B.weight)
         Fintype.card (PolynomialShearIndex B.weight) ≤ (1 + d) ^ C ∧
         ∃ T : (polynomialShearNilmanifold B.weight s B.weight_le).Niltest (fun _ : σ => 1),
           T.UnitIntervalValued ∧ T.ComplexityLE ((p + 2) ^ C) ∧
           ∀ x : σ → ℤ, T.eval x = (A.value (fun i => (x i : ℝ)) : ℂ)) := by
  obtain ⟨c, hc, hconvert⟩ := exists_normalized_patch_niltest_budget s
  let C := max c (s + 1)
  refine ⟨C, hc.trans (le_max_left _ _), ?_⟩
  intro σ _ d A p hp hn hd hLip
  obtain ⟨B, hw, hkernel, hnorm, hvalue⟩ := A.exists_coefficient_normalized
  refine ⟨B, hw, hkernel, ?_⟩
  let := polynomialShearIndexFintype B.weight (fun i => B.weight_pos i)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra B.weight ℚ)
  let := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra B.weight ℚ)
  let := realification_moduleTopology_t2 (polynomialShearOrderedBasis B.weight)
  have hB : (B.kernel.lip : ℝ) ≤ Real.exp p := by
    have h := (Real.log_le_iff_le_exp (by positivity : 0 < 2 + (A.kernel.lip : ℝ))).mp hLip
    rw [hkernel]
    linarith
  obtain ⟨T, hTunit, hTc, hTeval⟩ := hconvert B p hp hn hd hnorm hB
  have hD : Fintype.card (PolynomialShearIndex B.weight) ≤ d * (d + 1) ^ s := by
    simpa only [Fintype.card_fin] using polynomialShearIndex_card_le B.weight s
      (fun i => lt_of_lt_of_le Nat.zero_lt_one (B.weight_pos i)) B.weight_le
  have hdim : Fintype.card (PolynomialShearIndex B.weight) ≤ (1 + d) ^ C := by
    calc
      _ ≤ d * (d + 1) ^ s := hD
      _ ≤ (d + 1) * (d + 1) ^ s := Nat.mul_le_mul_right _ (Nat.le_succ d)
      _ = (1 + d) ^ (s + 1) := by rw [Nat.add_comm 1 d, pow_succ']
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  refine ⟨hdim, T, hTunit, hTc.mono ?_, ?_⟩
  · exact pow_le_pow_right₀ (by linarith) (le_max_left _ _)
  · intro x
    rw [hTeval, hvalue]

end Erdos3

end

end OAI
