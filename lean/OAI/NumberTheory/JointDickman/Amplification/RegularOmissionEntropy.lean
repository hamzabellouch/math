import OAI.NumberTheory.JointDickman.Amplification.RegularOmissionChoices

namespace OAI

/-! # Uniform entropy bound for old coefficient choices -/

namespace JointDickman
open Finset Classical

theorem regularOmissionChoices_entropy {L k : ℕ} (hk : k ∈ Icc 1 L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ (τ : ℝ), 0 < τ → τ ≤ τ₀ →
      ∀ (B : ℕ) (C : ℝ) (A U : Finset ℕ) (d : ℕ), 0 < auxiliaryLogLength B →
        RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C U →
        ((regularOmissionChoices B L k τ C A U d).card : ℝ) ≤
          ((A.card : ℝ)+1)*Real.exp
            (((((k : ℝ)/L)/2)*Real.binEntropy
              (2*min ((d : ℝ)/(((k : ℝ)/L)*auxiliaryLogLength B)) (1/2))+
                ε+highOmissionExponent τ)*auxiliaryLogLength B) := by
  have hL : 1 ≤ L := (mem_Icc.mp hk).1.trans (mem_Icc.mp hk).2
  have hg : 0 < (k : ℝ)/L := div_pos
    (by exact_mod_cast (by have := (mem_Icc.mp hk).1; omega : 0 < k))
    (by exact_mod_cast (by omega : 0 < L))
  obtain ⟨τ₁,hτ₁,hwin⟩ := subset_card_window_entropy hg hε
  refine ⟨min τ₁ (1/100),lt_min hτ₁ (by norm_num),?_⟩
  intro τ hτ hτsmall B C A U d hℓ hA hU
  have hτ₁' : τ ≤ τ₁ := hτsmall.trans (min_le_left _ _)
  have hsmall : τ ≤ 1/100 := hτsmall.trans (min_le_right _ _)
  let Q := primePrefix B ((k : ℝ)/L) (A ∪ U)
  let r : ℝ := min ((d : ℝ)/(((k : ℝ)/L)*auxiliaryLogLength B)) (1/2)
  have hr : 0 ≤ r := le_min (div_nonneg (Nat.cast_nonneg _) (mul_nonneg hg.le hℓ.le)) (by norm_num)
  have hr1 : r ≤ 1/2 := min_le_right _ _
  have hAQ : A ∩ Q = primePrefix B ((k : ℝ)/L) A := by
    dsimp [Q]
    rw [← primePrefix_inter,inter_eq_left.mpr subset_union_left]
  have hP : |((A ∩ Q).card : ℝ)/auxiliaryLogLength B-((k : ℝ)/L)/2| ≤ τ := by
    rw [hAQ]
    have hlo := (le_div_iff₀ hℓ).mpr (hA.1 k hk).1
    have hup := (div_le_iff₀ hℓ).mpr (hA.1 k hk).2
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hpre := hwin (A ∩ Q) (auxiliaryLogLength B) r τ hℓ hτ.le hτ₁' hr hr1 hP
  have hregion : ((A \ Q).card : ℝ) ≤ (1/2+τ)*auxiliaryLogLength B :=
    (show ((A \ Q).card : ℝ) ≤ A.card by exact_mod_cast card_le_card sdiff_subset).trans (hA.total_upper hL)
  have hhigh := high_omission_count_bound (A \ Q) hτ hsmall hℓ.le hregion
  have hc : ((regularOmissionChoices B L k τ C A U d).card : ℝ) ≤
      (subsetCardWindow (A ∩ Q) (auxiliaryLogLength B) ((k : ℝ)/L) r τ).card*
        (((A \ Q).powerset.filter (fun R => (R.card : ℝ) ≤ 4*τ*auxiliaryLogLength B)).card : ℝ) := by
    exact_mod_cast regularOmissionChoices_count A U d hL hk hτ.le hℓ hA hU
  have hcA : ((A ∩ Q).card : ℝ)+1 ≤ (A.card : ℝ)+1 := by
    have hh : ((A ∩ Q).card : ℝ) ≤ A.card := by exact_mod_cast card_le_card inter_subset_left
    linarith
  have hpre' := hpre.trans (mul_le_mul_of_nonneg_right hcA (Real.exp_pos _).le)
  refine hc.trans ((mul_le_mul hpre' hhigh (Nat.cast_nonneg _)
    (mul_nonneg (by positivity) (Real.exp_pos _).le)).trans_eq ?_)
  rw [mul_assoc,← Real.exp_add]
  congr 2
  dsimp [highOmissionExponent,r]
  ring

end JointDickman

end OAI
