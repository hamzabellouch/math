import OAI.NumberTheory.Ostmann.Characters.OneSidedScaleGapAsymptotics
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPrior

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedNumericInputs
open Filter Preliminaries TemplateOneSidedPrior

theorem primeShellPrior_mass_le_scale {N : ℕ} (E : Finset (PrimeUpTo N))
    (hE : 0 < primeShellMass E) (α c L : ℝ)
    (hZ : Real.exp (-c*L) ≤ primeShellMass E)
    (hlog : ∀p∈E,Real.exp (α*L) ≤ Real.log p.val) (p : PrimeUpTo N) :
    (primeShellPrior E hE).mass p ≤ Real.exp (c*L-Real.exp (α*L)) := by
  rw [primeShellPrior_mass]
  by_cases hp : p∈E
  · rw [ite_eq_left hp,div_eq_mul_inv]
    have hp0 : (0:ℝ) < p.val := by exact_mod_cast (primeUpTo_prime p).pos
    have he : Real.exp (Real.exp (α*L)) ≤ (p.val:ℝ) := by
      simpa only [Real.exp_log hp0] using Real.exp_le_exp.mpr (hlog p hp)
    have hinv : (p.val:ℝ)⁻¹ ≤ Real.exp (-Real.exp (α*L)) := by
      simpa only [one_div,Real.exp_neg] using one_div_le_one_div_of_le (Real.exp_pos _) he
    have hZinv : (primeShellMass E)⁻¹ ≤ Real.exp (c*L) := by
      simpa only [one_div] using source_normalization_le E hZ
    calc
      _ ≤ Real.exp (-Real.exp (α*L))*Real.exp (c*L) :=
        mul_le_mul hinv hZinv (inv_nonneg.mpr hE.le) (Real.exp_pos _).le
      _ = _ := by rw [←Real.exp_add]; congr 1; ring
  · rw [ite_eq_right hp,zero_div]
    exact (Real.exp_pos _).le

theorem eventually_primeShellPrior_mass_le {α c : ℝ} (hα : 0 < α) (hc : 0 ≤ c) :
    ∀ᶠ L : ℝ in atTop,∀ {N : ℕ} (E : Finset (PrimeUpTo N))
      (hE : 0 < primeShellMass E),
      Real.exp (-c*L) ≤ primeShellMass E →
      (∀p∈E,Real.exp (α*L) ≤ Real.log p.val) →
      ∀p,(primeShellPrior E hE).mass p ≤ Real.exp (-(1/2:ℝ)*Real.exp (α*L)) := by
  filter_upwards [eventually_historyPolynomialCost_le c 1 1 (by norm_num) hα
    (by norm_num : (0:ℝ)<1/2)] with L hL
  have hf : L ≤ 1+(⌊L⌋₊:ℝ) := by
    simpa only [add_comm] using (Nat.lt_floor_add_one L).le
  have hcl : c*L ≤ (1/2:ℝ)*Real.exp (α*L) := by
    apply (mul_le_mul_of_nonneg_left hf hc).trans
    simpa only [historyPolynomialCost,one_mul,pow_one] using hL
  intro N E hE hZ hlog p
  exact (primeShellPrior_mass_le_scale E hE α c L hZ hlog p).trans
    (Real.exp_le_exp.mpr (by linarith))

theorem eventually_budget_modulus_lt_prime (C z : ℝ) (d : ℕ) {α : ℝ}
    (hz : 0 ≤ z) (hα : 0 < α) :
    ∀ᶠ L : ℝ in atTop,∀ Q p : ℕ,
      (Q:ℝ) ≤ Real.exp (historyPolynomialCost C z d L) →
      Real.exp (α*L) ≤ Real.log p → Q < p := by
  filter_upwards [eventually_historyPolynomialCost_le C z d hz hα
    (by norm_num : (0:ℝ)<1/2)] with L hL
  intro Q p hQ hp
  have hp0 : p≠0 := by
    intro h
    subst p
    simp only [Nat.cast_zero,Real.log_zero] at hp
    exact (not_le_of_gt (Real.exp_pos _)) hp
  have hpR : (0:ℝ)<p := by exact_mod_cast Nat.pos_of_ne_zero hp0
  have hc : historyPolynomialCost C z d L < Real.exp (α*L) := by
    nlinarith [Real.exp_pos (α*L)]
  have he : Real.exp (historyPolynomialCost C z d L) < (p:ℝ) := by
    simpa only [Real.exp_log hpR] using Real.exp_lt_exp.mpr (hc.trans_le hp)
  exact_mod_cast hQ.trans_lt he

theorem pair_modulus_budget (C₁ C₂ z L : ℝ) (d Q₁ Q₂ : ℕ)
    (h₁ : (Q₁:ℝ) ≤ Real.exp (historyPolynomialCost C₁ z d L))
    (h₂ : (Q₂:ℝ) ≤ Real.exp (historyPolynomialCost C₂ z d L)) :
    ((Q₁*Q₂:ℕ):ℝ) ≤ Real.exp (historyPolynomialCost (C₁+C₂) z d L) := by
  rw [Nat.cast_mul]
  calc
    _ ≤ Real.exp (historyPolynomialCost C₁ z d L)*Real.exp (historyPolynomialCost C₂ z d L) :=
      mul_le_mul h₁ h₂ (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [←Real.exp_add]; congr 1; unfold historyPolynomialCost; ring

end Ostmann.Characters.TemplateOneSidedNumericInputs

end

end OAI
