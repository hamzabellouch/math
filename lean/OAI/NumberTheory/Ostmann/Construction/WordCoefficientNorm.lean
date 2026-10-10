import OAI.NumberTheory.Ostmann.Construction.WordUnitCoefficient

namespace OAI

/-! # Uniform norms and valid support of the constructed coefficients -/

namespace Ostmann.WordFourierParameters

open scoped BigOperators Classical SchwartzMap

theorem coefficient_norm {σ : Type*} {n : ℕ} (p : WordFourierParameters n)
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (ht : NonzeroInternalFrequencies n t) (x : σ → ℤ) :
    ‖p.coefficient template t ht x‖ ≤ (SchwartzMap.seminorm ℝ 0 0 p.profile) ^ (2 ^ n) := by
  have hS : 0 ≤ SchwartzMap.seminorm ℝ 0 0 p.profile :=
    (norm_nonneg (p.profile 0)).trans (p.profile.norm_le_seminorm ℝ 0)
  unfold coefficient
  split_ifs with h
  · simp only [one_mul, norm_prod]
    calc
      _ ≤ ∏ _j : Fin (2 ^ n), SchwartzMap.seminorm ℝ 0 0 p.profile := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro j _
        exact normalizedFourierProfile_norm p.profile _ _ _
          (p.profile.norm_le_seminorm ℝ)
          ((p.lower_one j).trans (h.2 j).1)
      _ = _ := by simp
  · simpa only [zero_mul, norm_zero] using pow_nonneg hS (2 ^ n)

theorem unitRangedCoefficient_norm {σ : Type*} {n : ℕ} (p : WordFourierParameters n)
    (U D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : σ → ℤ) :
    ‖p.unitRangedCoefficient U D template t ht x‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 p.profile) ^ (2 ^ n) := by
  have hS : 0 ≤ SchwartzMap.seminorm ℝ 0 0 p.profile :=
    (norm_nonneg (p.profile 0)).trans (p.profile.norm_le_seminorm ℝ 0)
  unfold unitRangedCoefficient rangedCoefficient
  split_ifs <;> simp only [one_mul, zero_mul, norm_zero]
  · exact p.coefficient_norm template t ht x
  all_goals exact pow_nonneg hS (2 ^ n)

theorem unitRangedCoefficient_valid {σ : Type*} {n : ℕ} (p : WordFourierParameters n)
    (U D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : σ → ℕ)
    (hx : p.unitRangedCoefficient U D template t ht (fun i => (x i : ℤ)) ≠ 0) :
    ValidTransferHistory (wordTransferSystem σ) n (template.state x) t := by
  by_contra hv
  apply hx
  simp only [unitRangedCoefficient, rangedCoefficient,
    p.coefficient_eq_zero_of_not_valid template t ht x hv, mul_zero]

end Ostmann.WordFourierParameters

end OAI
