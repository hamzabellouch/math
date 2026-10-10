import OAI.Combinatorics.ContingencyTables.Machines.BinaryPowerProgram

namespace OAI

/-! # Constructing the bounded unary loop markers used in tabulation -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

def unaryMarkers (n : ℕ) : List Bool := (List.range n).map (fun _ => false)

def unaryMarkersRealizer : Realizer unaryMarkers :=
  composition range (map (constant false))

lemma unaryMarkers_length (n : ℕ) : (unaryMarkers n).length=n := by
  simp only [unaryMarkers,List.length_map,List.length_range]

/-- Unary markers are charged by the actual requested loop length. -/
lemma work_unaryMarkers : WorkBound unaryMarkersRealizer id :=
  work_then_polynomial range_numeric_work (polynomial_map (polynomial_constant false))

end ContingencyTables.DensePrograms

end OAI
