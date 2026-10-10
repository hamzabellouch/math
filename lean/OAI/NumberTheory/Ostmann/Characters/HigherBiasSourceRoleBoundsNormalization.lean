import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceCellsBounded
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceWordStatistic
import OAI.NumberTheory.Ostmann.Characters.PivotProductNormalizationCells

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HigherBiasSourceRoleBounds
open Construction Preliminaries HigherBiasSourceWord PivotProductFibers

def halfRoleShells {Q nc : ℕ} (bulk top : Finset (PrimeUpTo Q)) (m : ℕ)
    (cells : Fin nc → Finset (PrimeUpTo Q)) : Fin ((m+1)+nc) → Finset (PrimeUpTo Q) :=
  Fin.append (roleShells bulk top m) cells

theorem normalization_halfRoleShells {Q nc : ℕ} (bulk top : Finset (PrimeUpTo Q))
    (m : ℕ) (cells : Fin nc → Finset (PrimeUpTo Q)) :
    normalization (halfRoleShells bulk top m cells) =
      ((primeShellMass bulk)⁻¹)^m * (primeShellMass top)⁻¹ * normalization cells := by
  unfold normalization halfRoleShells
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  congr 1
  unfold roleShells
  rw [Fin.prod_univ_add]
  simp

theorem cell_normalization_le {Q nc : ℕ} (cells : Fin nc → Finset (PrimeUpTo Q))
    (a : Fin nc → ℝ) {c β L : ℝ} (hc : 0 < c)
    (hmass : ∀ i, c / Real.exp (a i) ≤ primeShellMass (cells i))
    (ha : ∀ i, a i ≤ β*L) (hL : -Real.log c ≤ L) :
    normalization cells ≤ Real.exp ((β+1)*(nc:ℝ)*L) := by
  have h := PivotProductNormalization.normalization_le_exp cells (fun _ => (β+1)*L)
    (fun i => PivotProductNormalization.primeShellMass_exp_lower (cells i)
      hc (Real.exp_pos _) (hmass i) (Real.exp_le_exp.mpr (ha i)) hL)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_left_comm, mul_assoc] using h

theorem halfRole_normalization_le {Q nc : ℕ} (bulk top : Finset (PrimeUpTo Q))
    (m : ℕ) (cells : Fin nc → Finset (PrimeUpTo Q)) (a : Fin nc → ℝ)
    {ρ c₀ c β L : ℝ} (hρL : 0 < ρ*L) (hc₀ : 0 < c₀) (hc : 0 < c)
    (hbulk : ρ*L ≤ primeShellMass bulk) (htop : c₀ ≤ primeShellMass top)
    (hmass : ∀ i, c / Real.exp (a i) ≤ primeShellMass (cells i))
    (ha : ∀ i, a i ≤ β*L) (hL : -Real.log c ≤ L) :
    normalization (halfRoleShells bulk top m cells) ≤
      ((ρ*L)⁻¹)^m / c₀ * Real.exp ((β+1)*(nc:ℝ)*L) := by
  rw [normalization_halfRoleShells, div_eq_mul_inv]
  have hb : 0 ≤ (primeShellMass bulk)⁻¹ := inv_nonneg.mpr (hρL.trans_le hbulk).le
  have ht : 0 ≤ (primeShellMass top)⁻¹ := inv_nonneg.mpr (hc₀.trans_le htop).le
  have hcell : ∀ i, 0 < primeShellMass (cells i) :=
    fun i => (div_pos hc (Real.exp_pos _)).trans_le (hmass i)
  apply mul_le_mul
  · exact mul_le_mul (pow_le_pow_left₀ hb (inv_anti₀ hρL hbulk) m)
      (inv_anti₀ hc₀ htop) ht (by positivity)
  · exact cell_normalization_le cells a hc hmass ha hL
  · exact normalization_nonneg cells hcell
  · positivity

theorem halfRole_normalization_le_count {Q nc : ℕ} (bulk top : Finset (PrimeUpTo Q))
    (m : ℕ) (cells : Fin nc → Finset (PrimeUpTo Q)) (a : Fin nc → ℝ)
    {ρ c₀ c β L : ℝ} (hρL : 0 < ρ*L) (hc₀ : 0 < c₀) (hc : 0 < c)
    (hbulk : ρ*L ≤ primeShellMass bulk) (htop : c₀ ≤ primeShellMass top)
    (hmass : ∀ i, c / Real.exp (a i) ≤ primeShellMass (cells i))
    (ha : ∀ i, a i ≤ β*L) (hL : -Real.log c ≤ L)
    (hβ : 0 ≤ β+1) (hL0 : 0 ≤ L) (nmax : ℕ) (hn : nc ≤ nmax) :
    normalization (halfRoleShells bulk top m cells) ≤
      ((ρ*L)⁻¹)^m / c₀ * Real.exp ((β+1)*(nmax:ℝ)*L) := by
  apply (halfRole_normalization_le bulk top m cells a hρL hc₀ hc hbulk htop hmass ha hL).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hn) hβ) hL0

theorem halfRole_mass_pos {Q nc : ℕ} (bulk top : Finset (PrimeUpTo Q))
    (m : ℕ) (cells : Fin nc → Finset (PrimeUpTo Q))
    (hb : 0 < primeShellMass bulk) (ht : 0 < primeShellMass top)
    (hc : ∀ i, 0 < primeShellMass (cells i)) :
    ∀ i, 0 < primeShellMass (halfRoleShells bulk top m cells i) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [halfRoleShells, Fin.append_left] using roleShells_mass_pos hb ht m j
  · intro j
    simpa only [halfRoleShells, Fin.append_right] using hc j

end Ostmann.Characters.HigherBiasSourceRoleBounds

end

end OAI
