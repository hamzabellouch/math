import OAI.NumberTheory.Ostmann.ZeroDensity.DensitySeparatedCount
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityZeroBins

namespace OAI

/-! # The separated density bound for every zero, with analytic multiplicities -/

namespace Ostmann

open scoped BigOperators Classical

 theorem density_all_zero_count :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T σ : ℝ,
      2 ≤ T → 4 ≤ (Q : ℝ) ^ 2 * T → 1 / 2 < σ → σ ≤ 1 →
      1 / Real.log ((Q : ℝ) ^ 2 * T) ≤ σ - 1 / 2 →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ((actualCharacterZeros χ).count σ T : ℝ)) ≤
        C * ((Q : ℝ) ^ 2 * T) ^ densityTargetExponent σ *
          (Real.log ((Q : ℝ) * T)) ^ 10 := by
  obtain ⟨C, hC, hsep⟩ := density_separated_zero_count
  refine ⟨80 * C / Real.log (14 / 13), by positivity, ?_⟩
  intro Q hQ T σ hT hB hσ hσ1 hgap F hF
  let S := densityZeroIndices F σ T
  let K := S.image densityZeroBin
  let I := {k : DensityZeroBin // k ∈ K}
  have hex (k : I) : ∃ n : ℕ, (⟨k.val.1, n⟩ : DensityZeroIndex) ∈ S ∧
      ⌊((actualCharacterZeros k.val.1).zeros n).im⌋ = k.val.2 :=
    densityZeroBin_nonempty S k.val k.property
  choose idx hidx using hex
  let c : I → PrimitiveComplexCharacter := fun k => k.val.1
  let z : I → ℂ := fun k => (actualCharacterZeros (c k)).zeros (idx k)
  let t : I → ℝ := fun k => (z k).im / (2 * Real.pi)
  let β : I → ℝ := fun k => (z k).re
  have hdata (k : I) : c k ∈ F ∧ |(z k).im| ≤ T ∧ σ ≤ β k :=
    (densityZeroIndices_mem F σ T ⟨c k, idx k⟩).mp (hidx k).1
  have hfloor (k : I) : ⌊(z k).im⌋ = k.val.2 := (hidx k).2
  have hz (k : I) : densityVerticalPoint (β k) (t k) = z k := by
    apply Complex.ext
    · simp [densityVerticalPoint, β]
    · have him (a b : ℝ) : (densityVerticalPoint a b).im = 2 * Real.pi * b := by
        simp [densityVerticalPoint]
      rw [him]
      dsimp [t]
      field_simp
  let color : I → ℤ := fun k => k.val.2 % 10
  let U : Finset I := Finset.univ
  have hcount (j : ℤ) : ((U.filter fun k => color k = j).card : ℝ) ≤
      C * ((Q : ℝ) ^ 2 * T) ^ densityTargetExponent σ *
        (Real.log ((Q : ℝ) * T)) ^ 9 := by
    apply hsep Q hQ T σ hT hB hσ hσ1 hgap (U.filter fun k => color k = j) c t β
    · intro k _
      exact hF (c k) (hdata k).1
    · intro k _
      dsimp [t]
      rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      exact (div_le_self (abs_nonneg _) (by nlinarith [Real.pi_gt_three])).trans (hdata k).2.1
    · intro k hk l hl hcl hne
      apply density_ordinate_bin_separation
      · rw [hfloor k, hfloor l]
        exact (Finset.mem_filter.mp hk).2.trans (Finset.mem_filter.mp hl).2.symm
      · rw [hfloor k, hfloor l]
        intro hb
        apply hne
        apply Subtype.ext
        exact Sigma.ext hcl (heq_of_eq hb)
    · intro k _
      refine ⟨(hdata k).2.2, (actualCharacterZeros (c k)).in_strip (idx k) |>.2.le, ?_⟩
      rw [hz]
      exact (actualCharacterZeros (c k)).actual_zero (idx k)
  have hcolors : U.card = ∑ j ∈ Finset.Ico (0 : ℤ) 10, (U.filter fun k => color k = j).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro k _
    exact Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  have hK : (K.card : ℝ) ≤ 10 * (C * ((Q : ℝ) ^ 2 * T) ^ densityTargetExponent σ *
      (Real.log ((Q : ℝ) * T)) ^ 9) := by
    have heq : U.card = K.card := by simp [U, I]
    rw [← heq, hcolors, Nat.cast_sum]
    calc
      _ ≤ ∑ _j ∈ Finset.Ico (0 : ℤ) 10,
          C * ((Q : ℝ) ^ 2 * T) ^ densityTargetExponent σ *
            (Real.log ((Q : ℝ) * T)) ^ 9 := Finset.sum_le_sum fun j _ => hcount j
      _ = _ := by norm_num
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hlog : 0 ≤ Real.log ((Q : ℝ) * T) := Real.log_nonneg (by nlinarith)
  rw [← densityZeroIndices_card]
  have hb := densityZeroIndices_bin_bound Q hQ T σ hT hσ.le F hF
  calc
    _ ≤ (K.card : ℝ) * ((8 / Real.log (14 / 13)) * Real.log ((Q : ℝ) * T)) := hb
    _ ≤ (10 * (C * ((Q : ℝ) ^ 2 * T) ^ densityTargetExponent σ *
          (Real.log ((Q : ℝ) * T)) ^ 9)) *
        ((8 / Real.log (14 / 13)) * Real.log ((Q : ℝ) * T)) := by
      exact mul_le_mul_of_nonneg_right hK (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
