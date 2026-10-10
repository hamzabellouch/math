import Mathlib
import OAI.NumberTheory.Ostmann.Construction.LogCellDefs

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

theorem logCellWeight_zero_below (c : ℝ) (p : ℕ) (hp : p≤⌊Real.exp (c-1)⌋₊) :
    logCellWeight c p=0 := by
  by_cases hp0 : p=0
  · simp only [hp0, logCellWeight, Nat.cast_zero, div_zero]
  have hpos : (0:ℝ)<p := by exact_mod_cast Nat.pos_of_ne_zero hp0
  have hle : (p:ℝ)≤Real.exp (c-1) :=
    (by exact_mod_cast hp : (p:ℝ)≤(⌊Real.exp (c-1)⌋₊ :ℝ)).trans
      (Nat.floor_le (Real.exp_pos _).le)
  have hlog := Real.log_le_log hpos hle
  rw [Real.log_exp] at hlog
  rw [logCellWeight, Ostmann.smoothPartition_zero_of_le_neg_one (by linarith), zero_div]

theorem logCellWeight_zero_above (c : ℝ) (p : ℕ) (hp : ⌊Real.exp (c+1)⌋₊<p) :
    logCellWeight c p=0 := by
  have hlarge : Real.exp (c+1)<(p:ℝ) := (Nat.floor_lt (Real.exp_pos _).le).mp hp
  have hlog := Real.log_lt_log (Real.exp_pos (c+1)) hlarge
  rw [Real.log_exp] at hlog
  rw [logCellWeight, Ostmann.smoothPartition_zero_of_one_le (by linarith), zero_div]

theorem logCellLogMass_eq_abel_sum (c : ℝ) :
    logCellLogMass c ∅ =
      ∑ p ∈ (Finset.Ioc ⌊Real.exp (c-1)⌋₊ ⌊Real.exp (c+1)⌋₊).filter Nat.Prime,
        Real.log p*Ostmann.smoothPartition (Real.log p-c)/(p:ℝ) := by
  classical
  let s := (Finset.Ioc ⌊Real.exp (c-1)⌋₊ ⌊Real.exp (c+1)⌋₊).filter Nat.Prime
  have hsub : s⊆logCellPrimes c := by
    intro p hp
    obtain ⟨hpI,hprime⟩ := Finset.mem_filter.mp hp
    obtain ⟨hlo,hhi⟩ := Finset.mem_Ioc.mp hpI
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨by omega, ?_⟩,hprime⟩
    exact hhi.trans (Nat.floor_le_ceil _)
  have hsum : (∑ p∈s, Real.log p*logCellWeight c p) =
      ∑ p∈logCellPrimes c, Real.log p*logCellWeight c p := by
    apply Finset.sum_subset hsub
    intro p hp hnot
    have hprime : p.Prime := (Finset.mem_filter.mp hp).2
    have hnotI : ¬(⌊Real.exp (c-1)⌋₊<p ∧ p≤⌊Real.exp (c+1)⌋₊) := by
      intro h
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr h,hprime⟩)
    have hz : logCellWeight c p=0 := by
      by_cases hlo : ⌊Real.exp (c-1)⌋₊<p
      · apply logCellWeight_zero_above
        have : ¬p≤⌊Real.exp (c+1)⌋₊ := fun hhi => hnotI ⟨hlo,hhi⟩
        omega
      · apply logCellWeight_zero_below
        omega
    rw [hz, mul_zero]
  simpa only [logCellLogMass, Finset.sdiff_empty, s, logCellWeight, mul_div_assoc] using hsum.symm

end Ostmann.Construction

end

end OAI
