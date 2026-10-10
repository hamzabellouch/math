import OAI.NumberTheory.Ostmann.Construction.LogCellLimit
import OAI.NumberTheory.Ostmann.Construction.LogCellPrior
import OAI.NumberTheory.Ostmann.Construction.LogCellWeightedLimit

namespace OAI

open Filter
open scoped Topology
namespace Ostmann.Construction

theorem logCellMass_tendsto :
    Tendsto (fun c : ℝ => c*logCellMass c ∅) atTop (𝓝 1) :=
  logCellMass_limit_of_logMass_limit logCellLogMass_tendsto

theorem logCellMass_uniform_delete_two :
    ∀ ε : ℝ, 0<ε → ∀ᶠ c : ℝ in atTop, ∀ E : Finset ℕ, E.card≤2 →
      |c*logCellMass c E-1|<ε :=
  logCellMass_limit_uniform_delete_two logCellLogMass_tendsto

theorem logCellLogMass_uniform_delete_two :
    ∀ ε : ℝ, 0<ε → ∀ᶠ c : ℝ in atTop, ∀ E : Finset ℕ, E.card≤2 →
      |logCellLogMass c E-1|<ε :=
  logCellLogMass_limit_uniform_delete_two logCellLogMass_tendsto

theorem logCell_normalization_eventually :
    ∀ᶠ c : ℝ in atTop, ∀ E : Finset ℕ, E.card≤2 →
      0<logCellMass c E ∧ c/2≤(logCellMass c E)⁻¹ ∧ (logCellMass c E)⁻¹≤2*c :=
  logCellMass_eventually_normalizable logCellLogMass_tendsto

end Ostmann.Construction

end OAI
