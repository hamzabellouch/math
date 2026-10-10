import OAI.Combinatorics.BalancedRyser.Selection.SelectionConcentrationUniform
import OAI.Combinatorics.BalancedRyser.Selection.SelectionOccupancyUniform

namespace OAI

namespace Balanced
open scoped _root_.Balanced

universe u v w

theorem selection_proof : SelectionStatement.{u,v,w} := by
  apply Selection.Process.selectionStatement_of_uniform_concentration
  intro p hp
  exact Selection.Process.exists_uniformConcentratedPath_estimate p hp

end Balanced

end OAI
