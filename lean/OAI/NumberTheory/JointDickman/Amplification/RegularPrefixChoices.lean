import OAI.NumberTheory.JointDickman.Counting.SubsetWindowEntropy
import OAI.NumberTheory.JointDickman.Arithmetic.RegularPrimeSets

namespace OAI

/-! # Counting prescribed-size additions inside a regular remainder -/

namespace JointDickman
open Finset Classical

noncomputable def regularPrefixChoices (B L k : ℕ) (R : Finset ℕ) (d : ℕ) : Finset (Finset ℕ) :=
  (primePrefix B ((k : ℝ)/L) R).powerset.filter (fun Y => Y.card = d)

theorem regularPrefixChoices_entropy {L k : ℕ} (hk : k ∈ Icc 1 L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ (τ : ℝ), 0 ≤ τ → τ ≤ τ₀ →
      ∀ (B : ℕ) (C : ℝ) (R : Finset ℕ) (d : ℕ), 0 < auxiliaryLogLength B →
        RegularPrimeSet B L τ C R →
        ((regularPrefixChoices B L k R d).card : ℝ) ≤
          ((R.card : ℝ)+1)*Real.exp
            (((((k : ℝ)/L)/2)*Real.binEntropy
              (2*min ((d : ℝ)/(((k : ℝ)/L)*auxiliaryLogLength B)) (1/2))+ε)*auxiliaryLogLength B) := by
  have hg : 0 < (k : ℝ)/L := div_pos
    (by exact_mod_cast (by have := (mem_Icc.mp hk).1; omega : 0 < k))
    (by exact_mod_cast (by have := (mem_Icc.mp hk).1; have := (mem_Icc.mp hk).2; omega : 0 < L))
  obtain ⟨τ₀,hτ₀,hwin⟩ := subset_card_window_entropy hg hε
  refine ⟨τ₀,hτ₀,?_⟩
  intro τ hτ hτsmall B C R d hℓ hR
  let g := (k : ℝ)/L
  let Q := primePrefix B g R
  let r := min ((d : ℝ)/(g*auxiliaryLogLength B)) (1/2)
  have hQsub : Q ⊆ R := by
    dsimp only [Q,primePrefix]
    split_ifs
    · exact filter_subset _ _
    · exact subset_rfl
  have hQcard := hR.1 k hk
  have hQnorm : |(Q.card : ℝ)/auxiliaryLogLength B-g/2| ≤ τ := by
    have hl := (le_div_iff₀ hℓ).mpr hQcard.1
    have hu := (div_le_iff₀ hℓ).mpr hQcard.2
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hr : 0 ≤ r := le_min (div_nonneg (Nat.cast_nonneg _) (mul_pos hg hℓ).le) (by norm_num)
  have hr1 : r ≤ 1/2 := min_le_right _ _
  have hwindow : regularPrefixChoices B L k R d ⊆ subsetCardWindow Q (auxiliaryLogLength B) g r τ := by
    intro Y hY
    obtain ⟨hY,hcard⟩ := mem_filter.mp hY
    have hsub : Y ⊆ Q := mem_powerset.mp hY
    apply mem_filter.mpr
    refine ⟨hY,?_⟩
    rw [hcard]
    have hdc : (d : ℝ) ≤ Q.card := by exact_mod_cast (hcard ▸ card_le_card hsub)
    have hdu : (d : ℝ) ≤ (g/2+τ)*auxiliaryLogLength B := hdc.trans hQcard.2
    by_cases hd : (d : ℝ)/(g*auxiliaryLogLength B) ≤ 1/2
    · dsimp only [r]
      rw [min_eq_left hd]
      have he : (d : ℝ)/auxiliaryLogLength B-g*((d : ℝ)/(g*auxiliaryLogLength B)) = 0 := by
        field_simp [show g ≠ 0 from hg.ne',hℓ.ne']
        ring
      rw [he,abs_zero]
      linarith
    · dsimp only [r]
      rw [min_eq_right (le_of_not_ge hd)]
      have hlow := (le_div_iff₀ (mul_pos hg hℓ)).mp (le_of_not_ge hd)
      have hhigh := (div_le_iff₀ hℓ).mpr hdu
      rw [abs_of_nonneg (by
        have hh : g/2 ≤ (d : ℝ)/auxiliaryLogLength B :=
          (le_div_iff₀ hℓ).mpr (by nlinarith [hlow])
        nlinarith : 0 ≤ (d : ℝ)/auxiliaryLogLength B-g*(1/2))]
      linarith
  have hcount : ((regularPrefixChoices B L k R d).card : ℝ) ≤
      (subsetCardWindow Q (auxiliaryLogLength B) g r τ).card := by exact_mod_cast card_le_card hwindow
  have hh := hwin Q (auxiliaryLogLength B) r τ hℓ hτ hτsmall hr hr1 hQnorm
  have hcard : (Q.card : ℝ)+1 ≤ (R.card : ℝ)+1 := by
    have hc : (Q.card : ℝ) ≤ R.card := by exact_mod_cast card_le_card hQsub
    linarith
  exact hcount.trans (hh.trans (mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le))

end JointDickman

end OAI
