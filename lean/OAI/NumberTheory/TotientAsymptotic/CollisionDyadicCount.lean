import OAI.NumberTheory.TotientAsymptotic.DyadicSuffix

namespace OAI

/-! From counts in dyadic suffix intervals to their reciprocal mass. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- The dyadic count has the exact normalization `C*y/log(y)` times its
strict-slack saving. Weighting each suffix by its reciprocal cancels `y`. -/
theorem collision_dyadic_reciprocal_bound {α : Type*} (Q : Finset α)
    (idx : α → ℕ) (v : α → ℝ) {N : ℕ} (hN : 1 ≤ N) {C σ B : ℝ}
    (hC : 0 ≤ C) (hσ : 0 < σ) (hB : Real.exp B ≤ (N : ℝ)*Real.log 2)
    (hlo : ∀ a ∈ Q, (2 : ℝ)^(idx a+N+1)/2 < v a)
    (hcount : ∀ k : ℕ, ((Q.filter (fun a => idx a=k)).card : ℝ) ≤
      C*(2 : ℝ)^(k+N+1)*dyadicSuffixWeight σ (k+N+1)) :
    (∑ a ∈ Q, (v a)⁻¹) ≤ (2*C)/(σ*Real.log 2)*Real.exp (-σ*B) := by
  classical
  have hmap : ∀ a ∈ Q, idx a ∈ Q.image idx := fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  have hfiber (k : ℕ) : (∑ a ∈ Q.filter (fun a => idx a=k), (v a)⁻¹) ≤
      2*C*dyadicSuffixWeight σ (k+N+1) := by
    have hy : (0 : ℝ) < (2 : ℝ)^(k+N+1) := by positivity
    calc
      _ ≤ ∑ _a ∈ Q.filter (fun a => idx a=k), 2/(2 : ℝ)^(k+N+1) := by
        apply Finset.sum_le_sum
        intro a ha
        obtain ⟨ha, hk⟩ := Finset.mem_filter.mp ha
        have hl := hlo a ha
        rw [hk] at hl
        have hh := inv_anti₀ (div_pos hy (by norm_num)) hl.le
        simpa only [inv_div] using hh
      _ = ((Q.filter (fun a => idx a=k)).card : ℝ)*(2/(2 : ℝ)^(k+N+1)) := by simp
      _ ≤ (C*(2 : ℝ)^(k+N+1)*dyadicSuffixWeight σ (k+N+1))*(2/(2 : ℝ)^(k+N+1)) :=
        mul_le_mul_of_nonneg_right (hcount k) (by positivity)
      _ = _ := by field_simp
  calc
    _ ≤ ∑ k ∈ Q.image idx, 2*C*dyadicSuffixWeight σ (k+N+1) :=
      Finset.sum_le_sum (fun k _ => hfiber k)
    _ = 2*C*∑ k ∈ Q.image idx, dyadicSuffixWeight σ (k+N+1) := by rw [Finset.mul_sum]
    _ ≤ 2*C*∑' k : ℕ, dyadicSuffixWeight σ (k+N+1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (dyadic_suffix_summable hσ N).sum_le_tsum
      intro k _
      unfold dyadicSuffixWeight
      exact div_nonneg (Real.exp_pos _).le (mul_nonneg (Nat.cast_nonneg _)
        (Real.log_pos (by norm_num)).le)
    _ ≤ 2*C*(Real.exp (-σ*B)/(σ*Real.log 2)) :=
      mul_le_mul_of_nonneg_left (dyadic_suffix_exponential_bound hσ hN hB) (by positivity)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
