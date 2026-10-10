import Mathlib
import OAI.Combinatorics.IndependentSets.Expansion.PreprocessingTables

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PreprocessingStageMaps
open PreprocessingRegularTables

abbrev BaseTable := PreprocessingTables.BaseTable

def regular (H : BaseTable) (t : GraphTables.Table) : PortTables.Input (internalDegree + 1) :=
  ⟨vertexCount t (PreprocessingRegularTables.padding t), regularize H t⟩

def padding (d : Nat) (input : PortTables.Input d) : PortTables.Input d :=
  ⟨PreprocessingLevels.paddedSize input.1,
    PreprocessingPaddingTables.pad input.2 (PreprocessingLevels.le_paddedSize input.1)⟩

def familyAt (H : BaseTable) (n : Nat) :
    ExpanderTables.Table (PreprocessingLevels.paddedSize n) internalDegree :=
  resizeTable (PreprocessingLevels.table_vertexCount_eq_paddedSize n)
    (ExpanderTables.family H (PreprocessingLevels.boundedLevel n))

def paddedOverlay (H : BaseTable) (d : Nat) (input : PortTables.Input d) :
    PortTables.Input (d + internalDegree) :=
  ⟨PreprocessingLevels.paddedSize input.1,
    PreprocessingOverlayTables.overlay (padding d input).2 (familyAt H input.1)⟩

def lazy (d : Nat) (input : PortTables.Input d) : PortTables.Input (2 * d) :=
  ⟨input.1, PreprocessingOverlayTables.lazy input.2⟩

theorem output_eq (H : BaseTable) (t : GraphTables.Table) :
    PreprocessingTables.output H t =
      lazy ((internalDegree + 1) + internalDegree)
        (paddedOverlay H (internalDegree + 1) (regular H t)) := rfl

end IndependentSetsGames.Foundations.PCP.PreprocessingStageMaps

end OAI
