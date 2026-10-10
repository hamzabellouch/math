import OAI.NumberTheory.Ostmann.Construction.PrimeLogBlockMass
import OAI.NumberTheory.Ostmann.Supply.PrimeBandSelectionBalance
import OAI.NumberTheory.Ostmann.Supply.ResidueBudgetScale

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter Ostmann.Supply
open scoped BigOperators

lemma actualRatio_outside_balanced (d : Decomposition) {p : ℕ} (hp : p.Prime)
    (hb : ¬balancedDensity d p) : actualRatio d p≤(1/2:ℝ) ∨ 2≤actualRatio d p := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hσ := d.residueDensity_pos p hp
  have hd : residueDensityTotal d p=d.residueDensity p := by
    simp [residueDensityTotal,NeZero.ne p]
  change ¬((1/3:ℝ)≤residueDensityTotal d p ∧ residueDensityTotal d p≤(2/3:ℝ)) at hb
  rw [hd] at hb
  rw [actualRatio_eq_density]
  by_cases hlo : d.residueDensity p<(1/3:ℝ)
  · right
    exact (le_div_iff₀ hσ).mpr (by linarith)
  · left
    have hhi : (2/3:ℝ)<d.residueDensity p := by
      by_contra h
      exact hb ⟨le_of_not_gt hlo,le_of_not_gt h⟩
    exact (div_le_iff₀ hσ).mpr (by linarith)

lemma actualRatio_penalty_unbalanced (d : Decomposition) {p : ℕ} (hp : p.Prime)
    (hb : ¬balancedDensity d p) :
    (1/2:ℝ)≤actualRatio d p+(actualRatio d p)⁻¹-2 := by
  let x := actualRatio d p
  have hx : 0<x := actualRatio_pos d hp
  have hi : x*x⁻¹=1 := mul_inv_cancel₀ hx.ne'
  have hprod : 0≤(x-2)*(x-1/2) := by
    rcases actualRatio_outside_balanced d hp hb with hl|hr
    · exact mul_nonneg_of_nonpos_of_nonpos (by dsimp [x]; linarith) (by dsimp [x]; linarith)
    · exact mul_nonneg (by dsimp [x]; linarith) (by dsimp [x]; linarith)
  have hid : x*(x+x⁻¹-2-1/2)=(x-2)*(x-1/2) := by nlinarith
  change (1/2:ℝ)≤x+x⁻¹-2
  by_contra h
  have hn : x+x⁻¹-2-1/2<0 := by linarith
  have hm := mul_neg_of_pos_of_neg hx hn
  rw [hid] at hm
  linarith

theorem unbalancedPrimePrefix_log_mass_le (d : Decomposition) (Q : ℕ) :
    (1/2:ℝ)*primeLogMass (unbalancedPrimePrefix d Q)≤ratioWeightedSum d Q := by
  classical
  unfold primeLogMass
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑p∈unbalancedPrimePrefix d Q,
      (actualRatio d p+(actualRatio d p)⁻¹-2)*Real.log p/(p:ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp,hb⟩ := Finset.mem_filter.mp hp
      have hpen := actualRatio_penalty_unbalanced d (Nat.mem_primesLE.mp hp).2 hb
      have hw : 0≤Real.log p/(p:ℝ) := div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
      have hm := mul_le_mul_of_nonneg_right hpen hw
      simpa only [mul_div_assoc] using hm
    _ ≤ ratioWeightedSum d Q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro p hp _
      have hprime := (Nat.mem_primesLE.mp hp).2
      exact div_nonneg (mul_nonneg (ratio_penalty_nonneg (actualRatio_pos d hprime))
        (Real.log_natCast_nonneg p)) (Nat.cast_nonneg p)

theorem eventually_unbalanced_log_mass_le (d : Decomposition) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ Q : ℕ in atTop,
      primeLogMass (unbalancedPrimePrefix d Q)≤C*Real.log (Real.log (Q:ℝ)) := by
  obtain ⟨C,hC,hbudget⟩ := eventually_ratioWeightedSum_le d
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [hbudget] with Q hQ
  have h := unbalancedPrimePrefix_log_mass_le d Q
  linarith

end Ostmann.Construction

end

end OAI
