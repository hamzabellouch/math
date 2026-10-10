import OAI.NumberTheory.TotientAsymptotic.PrefixRelaxation
import OAI.NumberTheory.TotientAsymptotic.FullPrimeGrid

namespace OAI

/-! Slice bounds for the additive enlargement needed by banded witness boxes. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma pow_budget_bound {B E : ℝ} (hB : 0 < B) (hE : 0 ≤ E) (n : ℕ) :
    (B+E)^n ≤ B^n*Real.exp ((n : ℝ)*E/B) := by
  have hr : 0 ≤ 1+E/B := by positivity
  have hp := pow_le_pow_left₀ hr (show 1+E/B ≤ Real.exp (E/B) by
    simpa only [add_comm] using Real.add_one_le_exp (E/B)) n
  rw [← Real.exp_nat_mul] at hp
  have he : (B+E)^n = B^n*(1+E/B)^n := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [he]
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hp (pow_nonneg hB.le n)

lemma pow_budget_pred_bound {B E : ℝ} (hB : 0 < B) (hE : 0 ≤ E) (n : ℕ) :
    (B+E)^(n-1) ≤ B^(n-1)*Real.exp ((n : ℝ)*E/B) := by
  apply (pow_budget_bound hB hE (n-1)).trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hB.le _)
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ hB.le
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le n 1) hE

/-- A single slack slice has its usual linear slice cost even in the
additively enlarged simplex. -/
theorem additive_slack_shell_bound {x : ℝ} {N : ℕ} (hB : 0 < B x) (hN : 0 < N)
    (δ₀ : ℝ) (δ : Fin N → ℝ) (hδ₀ : 0 ≤ δ₀) (hδ : ∀ i, 0 ≤ δ i)
    (i : Fin N) {t : ℝ} (ht : 0 ≤ t) :
    volume.real (prefixRegion N (B x+δ₀) 0 (-δ) \
      prefixRegion N (B x+δ₀) 0 (raiseThreshold (-δ) i t)) ≤
      (t*N*g (i.val+1)/B x)*
        Real.exp ((N : ℝ)/B x*(δ₀+∑ j, g (j.val+1)*δ j))*G x N := by
  let E := δ₀+∑ j, g (j.val+1)*δ j
  have hE : 0 ≤ E := add_nonneg hδ₀
    (Finset.sum_nonneg (fun j _ => mul_nonneg (g_pos _).le (hδ j)))
  have he : B x+δ₀-0-∑ j, g (j.val+1)*(-δ) j = B x+E := by
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, sub_zero]
    dsimp [E]
    ring
  have hs := prefix_slack_shell_bound hN (B x+δ₀) 0 (-δ) i ht
    (by rw [he]; positivity)
  rw [he] at hs
  apply hs.trans
  have hden : 0 < (N.factorial : ℝ)*∏ j : Fin N, g (j.val+1) :=
    mul_pos (by positivity) (Finset.prod_pos (fun j _ => g_pos _))
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_budget_pred_bound hB hE N)
      (mul_nonneg (mul_nonneg ht (Nat.cast_nonneg _)) (g_pos _).le)) hden.le).trans_eq
  have hp : (B x)^N = B x*(B x)^(N-1) := by
    rw [← pow_succ', Nat.sub_add_cancel hN]
  unfold G
  rw [prod_fin_shifted]
  rw [hp]
  dsimp [E]
  field_simp

/-- The top-budget slice obeys the same estimate, with coefficient one. -/
theorem additive_top_shell_bound {x : ℝ} {N : ℕ} (hB : 0 < B x) (hN : 0 < N)
    (δ₀ : ℝ) (δ : Fin N → ℝ) (hδ₀ : 0 ≤ δ₀) (hδ : ∀ i, 0 ≤ δ i)
    {t : ℝ} (ht : 0 ≤ t) :
    volume.real (prefixRegion N (B x+δ₀) 0 (-δ) \
      prefixRegion N (B x+δ₀-t) 0 (-δ)) ≤
      (t*N/B x)*Real.exp ((N : ℝ)/B x*(δ₀+∑ j, g (j.val+1)*δ j))*G x N := by
  let E := δ₀+∑ j, g (j.val+1)*δ j
  have hE : 0 ≤ E := add_nonneg hδ₀
    (Finset.sum_nonneg (fun j _ => mul_nonneg (g_pos _).le (hδ j)))
  have hsub : prefixRegion N (B x+δ₀-t) 0 (-δ) ⊆ prefixRegion N (B x+δ₀) 0 (-δ) := by
    intro u hu
    exact ⟨hu.1, by have := hu.2; linarith⟩
  have hf : volume (prefixRegion N (B x+δ₀) 0 (-δ)) ≠ ⊤ := by
    rw [volume_prefixRegion_explicit _ hN]
    exact ENNReal.ofReal_ne_top
  have hden : 0 < (N.factorial : ℝ)*∏ j : Fin N, g (j.val+1) :=
    mul_pos (by positivity) (Finset.prod_pos (fun j _ => g_pos _))
  rw [measureReal_sdiff hsub (measurableSet_prefixRegion _ _ _ _) hf]
  change (volume _).toReal-(volume _).toReal ≤ _
  rw [volume_prefixRegion_explicit _ hN, volume_prefixRegion_explicit _ hN,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
  have he : B x+δ₀-0-∑ j, g (j.val+1)*(-δ) j = B x+E := by
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, sub_zero]
    dsimp [E]
    ring
  have he' : B x+δ₀-t-0-∑ j, g (j.val+1)*(-δ) j = B x+E-t := by
    linarith [he]
  rw [he, he', max_eq_left (show 0 ≤ B x+E by positivity), ← sub_div]
  apply (div_le_div_of_nonneg_right (pow_sub_positivePart_le (by positivity) ht N) hden.le).trans
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_budget_pred_bound hB hE N)
      (show 0 ≤ t*N by positivity)) hden.le).trans_eq
  have hp : (B x)^N = B x*(B x)^(N-1) := by
    rw [← pow_succ', Nat.sub_add_cancel hN]
  unfold G
  rw [prod_fin_shifted, hp]
  dsimp [E]
  field_simp

end TotientAsymptotic

end

end OAI
