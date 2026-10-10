import Mathlib.NumberTheory.Chebyshev
import OAI.NumberTheory.Ostmann.Construction.SourcePriors

namespace OAI

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open scoped BigOperators
open Construction

def primeLogCellConstant : ℝ := Real.log 4 * Real.exp 1

theorem primeLogCellConstant_pos : 0 < primeLogCellConstant := by
  unfold primeLogCellConstant
  exact mul_pos (Real.log_pos (by norm_num)) (Real.exp_pos _)

theorem harmonicPrimeMass_le_logCell (E : Finset ℕ) (hE : ∀ p∈E,p.Prime)
    (h : ℝ) (hh : 0 < h) (hband : ∀ p∈E,h ≤ Real.log p ∧ Real.log p ≤ h+1) :
    harmonicPrimeMass E ≤ primeLogCellConstant/h := by
  have hsub : E ⊆ Nat.primesLE ⌊Real.exp (h+1)⌋₊ := by
    intro p hp
    apply Nat.mem_primesLE.mpr
    refine ⟨?_,hE p hp⟩
    apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
    have hpp : (0:ℝ)<p := by exact_mod_cast (hE p hp).pos
    rw [←Real.exp_log hpp]
    exact Real.exp_le_exp.mpr (hband p hp).2
  have htheta : (∑ p∈E,Real.log p) ≤ Real.log 4*Real.exp (h+1) := by
    apply le_trans _ (Chebyshev.theta_le_log4_mul_x (Real.exp_pos _).le)
    rw [Chebyshev.theta_eq_sum_primesLE]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p hp _ => Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le))
  have hsum : h*harmonicPrimeMass E ≤ Real.exp (-h)*(∑ p∈E,Real.log p) := by
    rw [harmonicPrimeMass,Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp : (0:ℝ)<p := by exact_mod_cast (hE p hp).pos
    have hlog : 0 ≤ Real.log p := le_trans hh.le (hband p hp).1
    have hinv : (1:ℝ)/p ≤ Real.exp (-h) := by
      rw [Real.exp_neg]
      have hep : Real.exp h ≤ (p:ℝ) := by
        rw [←Real.exp_log hpp]
        exact Real.exp_le_exp.mpr (hband p hp).1
      simpa only [one_div] using inv_anti₀ (Real.exp_pos h) hep
    calc
      h*((1:ℝ)/p) ≤ Real.log p*((1:ℝ)/p) :=
        mul_le_mul_of_nonneg_right (hband p hp).1 (by positivity)
      _ ≤ Real.log p*Real.exp (-h) := mul_le_mul_of_nonneg_left hinv hlog
      _ = _ := by ring
  have hc : h*harmonicPrimeMass E ≤ primeLogCellConstant := by
    apply hsum.trans
    calc
      _ ≤ Real.exp (-h)*(Real.log 4*Real.exp (h+1)) :=
        mul_le_mul_of_nonneg_left htheta (Real.exp_pos _).le
      _ = primeLogCellConstant := by
        unfold primeLogCellConstant
        rw [show Real.exp (-h)*(Real.log 4*Real.exp (h+1)) =
          Real.log 4*(Real.exp (-h)*Real.exp (h+1)) by ring,←Real.exp_add]
        congr 2
        ring
  apply (le_div_iff₀ hh).mpr
  nlinarith

end Ostmann.Characters.HigherBiasSource

end

end OAI
