import OAI.NumberTheory.Ostmann.Construction.UnbalancedLogMass
import OAI.NumberTheory.Ostmann.Section07SmoothPartition

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter
open scoped BigOperators

def badLogCellMass (d : Decomposition) (Q : ℕ) (c : ℝ) : ℝ :=
  ∑p∈Supply.unbalancedPrimePrefix d Q,
    (Real.log p/(p:ℝ))*Ostmann.smoothPartition (Real.log p-c)

lemma badLogCellMass_nonneg (d : Decomposition) (Q : ℕ) (c : ℝ) :
    0≤badLogCellMass d Q c := by
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
    (Ostmann.smoothPartition_nonneg _)

lemma smoothPartition_finite_sum_le (K : Finset ℤ) (x : ℝ) :
    (∑c∈K,Ostmann.smoothPartition (x-c))≤1 := by
  rw [← Ostmann.smoothPartition_translate_tsum x]
  exact Summable.sum_le_tsum K (fun c _ => Ostmann.smoothPartition_nonneg _)
    (Ostmann.smoothPartition_translate_summable x)

theorem sum_badLogCellMass_le (d : Decomposition) (Q : ℕ) (K : Finset ℤ) :
    (∑c∈K,badLogCellMass d Q c)≤primeLogMass (Supply.unbalancedPrimePrefix d Q) := by
  unfold badLogCellMass primeLogMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro p hp
  rw [← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left (smoothPartition_finite_sum_le K (Real.log p))
    (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
  simpa only [mul_one] using h

def badLogCellCenters (d : Decomposition) (Q : ℕ) (K : Finset ℤ) (η : ℝ) : Finset ℤ := by
  classical
  exact K.filter (fun c => η≤badLogCellMass d Q c)

theorem badLogCellCenters_card_le (d : Decomposition) (Q : ℕ) (K : Finset ℤ) (η : ℝ) :
    η*((badLogCellCenters d Q K η).card:ℝ)≤
      primeLogMass (Supply.unbalancedPrimePrefix d Q) := by
  classical
  have hsum : (∑c∈badLogCellCenters d Q K η,η)≤
      ∑c∈badLogCellCenters d Q K η,badLogCellMass d Q c :=
    Finset.sum_le_sum (fun c hc => (Finset.mem_filter.mp hc).2)
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset
      (fun c : ℤ => η≤badLogCellMass d Q c) K)
    (fun c hc _ => badLogCellMass_nonneg d Q c)
  have htotal := sum_badLogCellMass_le d Q K
  simp only [Finset.sum_const,nsmul_eq_mul] at hsum
  change (∑c∈badLogCellCenters d Q K η,badLogCellMass d Q c)≤∑c∈K,badLogCellMass d Q c at hle
  nlinarith

theorem eventually_badLogCellCenters_card_le (d : Decomposition) {η : ℝ} (hη : 0<η) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ Q : ℕ in atTop, ∀ K : Finset ℤ,
      ((badLogCellCenters d Q K η).card:ℝ)≤C*Real.log (Real.log (Q:ℝ)) := by
  obtain ⟨C,hC,hbudget⟩ := eventually_unbalanced_log_mass_le d
  refine ⟨C/η,div_pos hC hη,?_⟩
  filter_upwards [hbudget] with Q hQ
  intro K
  have h := (badLogCellCenters_card_le d Q K η).trans hQ
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hη).mpr
  convert h using 1; ring

end Ostmann.Construction

end

end OAI
