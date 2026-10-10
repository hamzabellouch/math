import OAI.NumberTheory.Ostmann.Construction.SourcePriors
import OAI.NumberTheory.Ostmann.Supply.ActualLogBudget
import OAI.NumberTheory.Ostmann.Supply.Statement

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Supply
open Filter Ostmann.Construction
open scoped BigOperators

def balancedDensity (d : Decomposition) (p : ℕ) : Prop :=
  (1/3:ℝ)≤residueDensityTotal d p ∧ residueDensityTotal d p≤(2/3:ℝ)

theorem log_ratio_lower_of_unbalanced (d : Decomposition) {p : ℕ} (hp : p.Prime)
    (hbal : ¬balancedDensity d p) : Real.log 2≤|Real.log (actualRatio d p)| := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hσ0 := d.residueDensity_pos p hp
  have hσ1 := d.residueDensity_lt_one p hp
  have hr := actualRatio_eq_density d p
  have hd : residueDensityTotal d p=d.residueDensity p := by
    simp [residueDensityTotal,NeZero.ne p]
  change ¬((1/3:ℝ)≤residueDensityTotal d p ∧ residueDensityTotal d p≤(2/3:ℝ)) at hbal
  rw [hd] at hbal
  by_cases hlo : d.residueDensity p<(1/3:ℝ)
  · have htwo : (2:ℝ)≤actualRatio d p := by
      rw [hr]
      exact (le_div_iff₀ hσ0).mpr (by linarith)
    exact (Real.log_le_log (by norm_num) htwo).trans (le_abs_self _)
  · have hhi : (2/3:ℝ)<d.residueDensity p := by
      by_contra h
      exact hbal ⟨le_of_not_gt hlo,le_of_not_gt h⟩
    have hhalf : actualRatio d p≤(1/2:ℝ) := by
      rw [hr]
      exact (div_le_iff₀ hσ0).mpr (by linarith)
    have hl := Real.log_le_log (actualRatio_pos d hp) hhalf
    have he : Real.log (1/2:ℝ) = -Real.log 2 := by rw [one_div,Real.log_inv]
    rw [he] at hl
    exact (by linarith : Real.log 2≤ -Real.log (actualRatio d p)).trans (neg_le_abs _)

def unbalancedPrimePrefix (d : Decomposition) (Q : ℕ) : Finset ℕ :=
  by classical exact Q.primesLE.filter (fun p => ¬balancedDensity d p)

theorem unbalancedPrimePrefix_mass_le (d : Decomposition) (Q : ℕ) :
    Real.log 2*harmonicPrimeMass (unbalancedPrimePrefix d Q)≤actualLogBudget d Q := by
  classical
  unfold harmonicPrimeMass
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑p∈unbalancedPrimePrefix d Q, |Real.log (actualRatio d p)|/(p:ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp,hbad⟩ := Finset.mem_filter.mp hp
      have hl := log_ratio_lower_of_unbalanced d (Nat.mem_primesLE.mp hp).2 hbad
      simpa only [mul_one_div] using div_le_div_of_nonneg_right hl (Nat.cast_nonneg p)
    _ ≤ actualLogBudget d Q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro p hp _
      exact div_nonneg (abs_nonneg _) (Nat.cast_nonneg p)

end Ostmann.Supply

end

end OAI
