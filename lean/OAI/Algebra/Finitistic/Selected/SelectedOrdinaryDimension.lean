import OAI.Algebra.Finitistic.Selected.SelectedOrdinaryAlgebra
import OAI.Algebra.Finitistic.Ordinary.OrdinaryGlobalDimension

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.SelectedOrdinaryDimension
open SelectedOrdinaryAlgebra SelectedFixedDiagram

/-- A fixed numerical bound determined solely by the fixed selecting bimodule. -/
abbrev bound : ℕ := 3 * length + 2

/-- The actual D has the manuscript's global dimension bound on both sides. -/
theorem both_sides :
    (⨆ M : ModuleCat.{0} D, projectiveDimension M) ≤ bound ∧
    (⨆ M : ModuleCat.{0} Dᵐᵒᵖ, projectiveDimension M) ≤ bound :=
  OrdinarySimulation.source_ordinary_globalDimension_bound (QuadraticEncoding.composition P) length

theorem left_module (M : ModuleCat.{0} D) : HasProjectiveDimensionLE M bound := by
  apply (projectiveDimension_le_iff M bound).mp
  exact (le_iSup (fun N : ModuleCat.{0} D => projectiveDimension N) M).trans both_sides.1

theorem right_module (M : ModuleCat.{0} Dᵐᵒᵖ) : HasProjectiveDimensionLE M bound := by
  apply (projectiveDimension_le_iff M bound).mp
  exact (le_iSup (fun N : ModuleCat.{0} Dᵐᵒᵖ => projectiveDimension N) M).trans both_sides.2
end LittleFinitistic.SelectedOrdinaryDimension

end

end OAI
