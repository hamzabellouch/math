import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateNormalizationPower
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceScaleCutoff

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.DiagonalEstimate
open Template HigherBiasSource HigherBiasSource.SourceTemplate HigherBiasSourceWord Preliminaries
open InitialCharacterScale Filter
attribute [local instance] Classical.propDecidable

theorem eventually_fixedConfiguration_copiedNormalization (d : Decomposition)
    {α β ρ γ c₀ c δ : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hρ : 0 < ρ) (hγ : 0 < γ) (hc₀ : 0 < c₀) (hc : 0 < c) :
    ∀ᶠ k : ℕ in atTop, ∀ BD : ℝ, ∀ᶠ L : ℝ in atTop,
      ∀ E : Finset ℕ, (∀ p ∈ E, p.Prime) →
      ∀ s : SelectedWordSource d E δ L k α β ρ γ c₀,
      ∀ w : FixedConfigurationWitness s c BD, ∀ j : ℕ, j ≤ k →
      copiedNormalization (actualCopiedShells w.configuration (wordSize k L) j
        (s.locations.base 0) (s.locations.base 2) s.locations.primes) ≤
      L ^ (-((2^j*wordSize k L:ℕ):ℝ)) * Real.exp
        ((|Real.log ρ|+2)*((2^j*wordSize k L:ℕ):ℝ)+(2^k:ℕ)*|Real.log c₀|) := by
  classical
  have hβ : 0 < β := hα.trans hαβ
  filter_upwards [eventually_maxCells_le_depthScale (8*(β+1))] with k hk
  intro BD
  have hnum : ∀ᶠ L : ℝ in atTop, 1 ≤ α*L :=
    (Filter.tendsto_id.const_mul_atTop hα).eventually_ge_atTop 1
  filter_upwards [eventually_higherSource_collisionScale10 k α hα,hnum,
    eventually_gt_atTop (0:ℝ),eventually_ge_atTop (-Real.log c),
    (wordSize_tendsto k).eventually_ge_atTop 1] with L hcut hnum hL hLc hm
  intro E hE s w j hj
  have hu : 0 ≤ s.locations.u := by linarith [s.locations.top_lower]
  have hsource := source_base_mass s.locations hu (mul_nonneg hγ.le hL.le)
    hE (hcut s.locations.u s.locations.top_lower)
  have hnc : (configCellCount w.configuration:ℝ) ≤ maxCells 4 k := by
    have hh := configCellCount_le w.configuration (by
      intro a
      simpa only [show 2*((1/10000:ℝ)*k)=2*(k:ℝ)/10000 by ring] using w.geometry.length_upper a)
    simpa only [maxCells,show (2/10000:ℝ)*k=2*(k:ℝ)/10000 by ring] using hh
  have hcost : 2*(β+1)*maxCells 4 k ≤ depthScale k := by
    convert hk using 1; unfold maxCells; ring
  have hbudget : 2*(β+1)*(configCellCount w.configuration:ℝ)*L ≤
      2*(wordSize k L:ℝ) := by
    calc
      _ ≤ depthScale k*L := mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left hnc (by positivity)).trans hcost) hL.le
      _ ≤ (wordSize k L:ℝ)+1 := by linarith [(wordSize_bounds k hL.le).1]
      _ ≤ _ := by linarith
  obtain ⟨n,hn⟩ := w.nonempty
  have hcells : ∀ a, c/Real.exp (β*L) ≤
      primeShellMass (configurationCells s.locations.primes w.configuration a) :=
    fun a => (w.good n hn a).2.2.1
  have hmain := actualCopiedNormalization_le_power w.configuration (wordSize k L) j
    (s.locations.base 0) (s.locations.base 2) s.locations.primes
    hρ hc₀ hc hL (by linarith) hsource.1 hsource.2.2 hcells hLc hbudget
  apply hmain.trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hL.le _)
  apply Real.exp_le_exp.mpr
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  exact_mod_cast (Nat.pow_le_pow_right (by omega : 1 ≤ (2:ℕ)) hj)

end Ostmann.Characters.DiagonalEstimate

end

end OAI
