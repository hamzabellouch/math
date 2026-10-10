import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceRoleBoundsNormalization

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HigherBiasSourceRoleBounds
open Construction Preliminaries PivotProductFibers

theorem halfRole_prior_mass_le {Q nc : ℕ} (bulk top : Finset (PrimeUpTo Q))
    (m : ℕ) (cells : Fin nc → Finset (PrimeUpTo Q)) (a : Fin nc → ℝ)
    {ρ c₀ c β L : ℝ} (hρL : 0 < ρ*L) (hc₀ : 0 < c₀) (hc : 0 < c)
    (hbulk : ρ*L ≤ primeShellMass bulk) (htop : c₀ ≤ primeShellMass top)
    (hmass : ∀ i, c / Real.exp (a i) ≤ primeShellMass (cells i))
    (ha : ∀ i, a i ≤ β*L) (hL : -Real.log c ≤ L)
    (hE : ∀ i, 0 < primeShellMass (halfRoleShells bulk top m cells i))
    (w : Fin ((m+1)+nc) → PrimeUpTo Q) :
    (characterTuplePrior (halfRoleShells bulk top m cells) hE).mass w ≤
      (((ρ*L)⁻¹)^m / c₀ * Real.exp ((β+1)*(nc:ℝ)*L)) /
        (characterTupleProduct w:ℝ) := by
  apply (characterTuplePrior_mass_le _ hE w).trans
  exact div_le_div_of_nonneg_right
    (halfRole_normalization_le bulk top m cells a hρL hc₀ hc hbulk htop hmass ha hL)
    (Nat.cast_nonneg _)

theorem halfRole_normalization_le_zpow {Q nc : ℕ} (bulk top : Finset (PrimeUpTo Q))
    (m : ℕ) (cells : Fin nc → Finset (PrimeUpTo Q)) (a : Fin nc → ℝ)
    {ρ c₀ c β L : ℝ} (hρL : 0 < ρ*L) (hc₀ : 0 < c₀) (hc : 0 < c)
    (hbulk : ρ*L ≤ primeShellMass bulk) (htop : c₀ ≤ primeShellMass top)
    (hmass : ∀ i, c / Real.exp (a i) ≤ primeShellMass (cells i))
    (ha : ∀ i, a i ≤ β*L) (hL : -Real.log c ≤ L) :
    normalization (halfRoleShells bulk top m cells) ≤
      (ρ*L)^(-(m:ℤ)) / c₀ * Real.exp ((β+1)*(nc:ℝ)*L) := by
  simpa only [zpow_neg, zpow_natCast, inv_pow] using
    halfRole_normalization_le bulk top m cells a hρL hc₀ hc hbulk htop hmass ha hL

end Ostmann.Characters.HigherBiasSourceRoleBounds

end

end OAI
