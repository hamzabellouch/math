import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateCodeFamily
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateNormalizationActual

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Template HigherBiasSource HigherBiasSource.SourceTemplate Preliminaries
open InitialCharacterScale Filter
attribute [local instance] Classical.propDecidable

theorem fixedConfiguration_cell_count {d : Decomposition} {E : Finset ℕ}
    {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀}
    (w : FixedConfigurationWitness s c BD) :
    (configCellCount w.configuration:ℝ) ≤ maxCells 4 k := by
  have hh := configCellCount_le w.configuration (by
    intro a
    simpa only [show 2*((1/10000:ℝ)*k)=2*(k:ℝ)/10000 by ring] using w.geometry.length_upper a)
  simpa only [maxCells,show (2/10000:ℝ)*k=2*(k:ℝ)/10000 by ring] using hh

theorem eventually_fixedConfiguration_code_factor (d : Decomposition)
    {α β ρ γ c₀ c δ : ℝ} (hα : 0<α) (hαβ : α<β)
    (hρ : 0<ρ) (hγ : 0<γ) (hc₀ : 0<c₀) (hc : 0<c) :
    ∀ᶠ k : ℕ in atTop, ∀ BD : ℝ, ∀ᶠ L : ℝ in atTop,
      ∀ E : Finset ℕ, (∀ p∈E,p.Prime) →
      ∀ s : SelectedWordSource d E δ L k α β ρ γ c₀,
      ∀ w : FixedConfigurationWitness s c BD, ∀j : ℕ,j≤k → ∀D W : ℝ,
      ((codePreservingMatchings w.configuration (wordSize k L) j).card:ℝ)*
        copiedNormalization (actualCopiedShells w.configuration (wordSize k L) j
          (s.locations.base 0) (s.locations.base 2) s.locations.primes)*
        Real.exp (-D+W)*Real.exp ((β+1)*(2:ℝ)^j*L+(wordSize k L:ℝ)) ≤
      Real.exp (-D+((2^j*wordSize k L:ℕ):ℝ)*
          (Real.log (depthScale k)+(|Real.log ρ|+2)+Real.log 2)+
        (β+1)*(2:ℝ)^j*L+(wordSize k L:ℝ)+
        (2^k:ℕ)*|Real.log c₀|+W+sourceNonbulkLogCost k) := by
  filter_upwards [eventually_fixedConfiguration_copiedNormalization d hα hαβ hρ hγ hc₀ hc] with k hk
  intro BD
  filter_upwards [hk BD,eventually_gt_atTop (0:ℝ)] with L hLnorm hL
  intro E hE s w j hj D W
  simpa only [one_mul] using codePreserving_normalized_factor_le
    w.configuration (wordSize k L) j hj (fixedConfiguration_cell_count w)
    L (depthScale k) (|Real.log ρ|+2) ((2^k:ℕ)*|Real.log c₀|) (β+1) 1 D W
    (copiedNormalization (actualCopiedShells w.configuration (wordSize k L) j
      (s.locations.base 0) (s.locations.base 2) s.locations.primes))
    hL (depthScale_pos k) (wordSize_bounds k hL.le).2 (hLnorm E hE s w j hj)

end Ostmann.Characters.DiagonalEstimate

end

end OAI
