import Mathlib
import OAI.Analysis.FreeWords.GramCounting
import OAI.Analysis.FreeWords.WeightedInverse

namespace OAI

noncomputable section

namespace KKWeingarten

open scoped BigOperators

noncomputable section

theorem power_weight_bound (L t : ℝ) (hL : 1 ≤ L) (ht : 0 < t) (hs : L*t ≤ 1)
    (a b c : ℕ) (ha : 0 < a) (hc : c ≤ a+b) :
    t^a*(L*t)^b/(L*t)^c ≤ L⁻¹ := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hs0 : 0 < L*t := mul_pos hL0 ht
  have hi : L⁻¹ ≤ 1 := (inv_le_one₀ hL0).mpr hL
  have htval : L⁻¹*(L*t)=t := by field_simp
  have hp : (L⁻¹)^a ≤ L⁻¹ := by
    simpa only [pow_one] using pow_le_pow_of_le_one (inv_nonneg.mpr hL0.le) hi ha
  calc
    _ = ((L⁻¹)^a*(L*t)^(a+b))/(L*t)^c := by
      rw [pow_add,← mul_assoc,← mul_pow,htval]
    _ ≤ (L⁻¹*(L*t)^c)/(L*t)^c := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hs0.le _)
      exact mul_le_mul hp (pow_le_pow_of_le_one hs0.le hs hc) (pow_nonneg hs0.le _) (inv_nonneg.mpr hL0.le)
    _ = _ := mul_div_cancel_right₀ _ (pow_ne_zero _ hs0.ne')

theorem distanceMatrix_inverse_bound {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (δ : ι → ι → ℕ) (hself : ∀ i, δ i i=0)
    (hpos : ∀ i k, i ≠ k → 0 < δ i k)
    (htri : ∀ i k j, δ i j ≤ δ i k+δ k j)
    (t : ℝ) (ht : 0 < t) (hs : 2*(Fintype.card ι : ℝ)*t ≤ 1)
    (B : Matrix ι ι ℂ) (hB : distanceMatrix δ t*B=1) :
    ∀ i j, ‖B i j‖ ≤ 2*(2*(Fintype.card ι : ℝ)*t)^(δ i j) := by
  have hm : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hL : 1 ≤ 2*(Fintype.card ι : ℝ) := by
    have hm1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
    linarith
  have hs0 : 0 < 2*(Fintype.card ι : ℝ)*t := by positivity
  intro i j
  apply inverse_entry_bound_of_scaled_error (distanceMatrix δ t) B hB
    (fun k => (2*(Fintype.card ι : ℝ)*t)^(δ k j)) (fun _ => pow_pos hs0 _) j
    (by simp [hself]) _ i
  intro a b
  by_cases hab : a=b
  · subst b
    have hzc : (((2*(Fintype.card ι : ℝ)*t)^(δ a j) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (pow_pos hs0 (δ a j)).ne'
    simp only [distanceMatrix,hself,pow_zero,one_mul,ite_true,div_self hzc,sub_self,norm_zero]
    positivity
  · have hh := power_weight_bound (2*(Fintype.card ι : ℝ)) t hL ht hs
      (δ a b) (δ b j) (δ a j) (hpos a b hab) (htri a b j)
    simpa [distanceMatrix,hab,norm_div,norm_mul,norm_pow,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht,abs_of_pos hs0,abs_of_pos hm] using hh

end

end KKWeingarten
end

end OAI
