import OAI.NumberTheory.EgyptianFractions.GeometricRawDensity

namespace OAI
noncomputable section

open Filter

namespace Problem337.RawDensityParameters

/-- The fixed denominator constant from the residue construction. -/
abbrev DM : ℝ := 204204
/-- The terminal binary cutoff exponent. -/
abbrev D₀ : ℝ := 100000
/-- The fixed geometric contraction rate. -/
abbrev η : ℝ := 1 / 10000
/-- The exponent in the exceptional-set estimate. -/
abbrev c : ℝ := 1 / 1000
/-- The logarithmic bound for the number of geometric levels. -/
abbrev K : ℝ := 3 * (DM + 2) / η
/-- A fixed moment exponent sufficient for the density recurrence. -/
abbrev r : ℝ := 8 * K
/-- The terminal expansion budget plus the backward descent budget. -/
abbrev L : ℝ := TerminalAssembly.terminalCoefficient D₀ (1 - η) + K + 1

theorem DM_gt_one : 1 < DM := by norm_num [DM]
theorem D₀_ge_one : 1 ≤ D₀ := by norm_num [D₀]
theorem eta_pos : 0 < η := by norm_num [η]
theorem eta_le_half : η ≤ 1 / 2 := by norm_num [η]
theorem c_pos : 0 < c := by norm_num [c]
theorem K_nonneg : 0 ≤ K := by norm_num [K, DM, η]
theorem r_ge_two : 2 ≤ r := by norm_num [r, K, DM, η]
theorem eight_K_le_r : 8 * K ≤ r := le_rfl
theorem L_pos : 0 < L := by
  have h := TerminalAssembly.terminalCoefficient_pos D₀_ge_one
    (show 0 < 1 - η by norm_num [η]) (show 1 - η < 1 by norm_num [η])
  dsimp [L]
  linarith [K_nonneg]

/-- All scalar conditions required by the fixed-loss geometric constructor hold
at one common onset, independently of the natural values `C` and `M`. -/
theorem eventually_constructor_conditions : ∀ᶠ S : ℝ in atTop,
    1 ≤ S ∧ 1 ≤ Real.log S ∧ 2 ≤ ResidueLevels.scale S ∧
    S / (2 * Real.log S) ≤ (ResidueLevels.scale S : ℝ) ∧
    1 + 2 * Real.exp (S ^ (1 / 4 : ℝ) / r) ≤
      Real.exp (2 * S ^ (1 / 4 : ℝ)) := by
  have hpower : ∀ᶠ S : ℝ in atTop, (2 : ℝ) ≤ S ^ (1 / 4 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually_ge_atTop 2
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    ResidueLevels.eventually_scale_bounds, hpower] with S hS hscale hpower
  exact ⟨hS, hscale.1, hscale.2.1, hscale.2.2.1,
    descent_coefficient_bound _ _ hpower (by linarith [r_ge_two])⟩

/-- Canonical numerical specialization of the geometric constructor. This
lemma supplies only scalar conditions: genuine residue data, the denominator
window, and binary divisibility are still required explicitly. -/
theorem eventually_raw_density_supply_of_residue_data :
    ∀ᶠ S : ℝ in atTop, ∀ C M : ℕ,
      Real.exp (4 * (DM + 2) * S) ≤ (C : ℝ) →
      Real.exp S < (M : ℝ) →
      (M : ℝ) ≤ Real.exp (DM * S) →
      2 ^ TerminalDepth.binaryExponent D₀ S ∣ M →
      GeometricDensity.ResidueData DM D₀ η c r S 2 C M →
      RawDensitySupply DM L c K r S C := by
  filter_upwards [eventually_constructor_conditions] with S hS
  intro C M hC hM hMupper hbinary H
  have hCpos : 0 < C := by
    exact_mod_cast (Real.exp_pos _).trans_le hC
  exact GeometricDensity.raw_density_supply_of_geometric_residues H
    DM_gt_one D₀_ge_one eta_pos eta_le_half hS.1 hS.2.1 hS.2.2.1
    hS.2.2.2.1 hCpos hM hMupper hbinary (by norm_num) hS.2.2.2.2

end Problem337.RawDensityParameters

end

end OAI
