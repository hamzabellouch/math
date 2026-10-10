import Mathlib
import OAI.Computability.VertexCover.PCP.PreprocessingRegularTables
import OAI.Computability.VertexCover.PCP.PreprocessingPaddingTables
import OAI.Computability.VertexCover.PCP.PreprocessingOverlayTables
import OAI.Computability.VertexCover.PCP.Preprocessing

namespace OAI

                                                                                            

namespace UniqueGames.Foundations.PCP.PreprocessingTables

open PreprocessingRegularTables

abbrev BaseTable := PreprocessingRegularTables.BaseTable

def degree : Nat := 2 * ((internalDegree + 1) + internalDegree)

theorem degree_eq : degree = Preprocessing.degree := by
  unfold degree internalDegree Preprocessing.degree
  rw [pow_two]
  omega

def regularVertices (t : GraphTables.Table) : Nat := vertexCount t (padding t)
def vertices (t : GraphTables.Table) : Nat := PreprocessingLevels.paddedSize (regularVertices t)

def padded (H : BaseTable) (t : GraphTables.Table) :
    PortTables.Table (vertices t) (internalDegree + 1) :=
  PreprocessingPaddingTables.pad (regularize H t)
    (PreprocessingLevels.le_paddedSize (regularVertices t))

def overlayFamily (H : BaseTable) (t : GraphTables.Table) :
    ExpanderTables.Table (vertices t) internalDegree :=
  resizeTable (PreprocessingLevels.table_vertexCount_eq_paddedSize (regularVertices t))
    (ExpanderTables.family H (PreprocessingLevels.boundedLevel (regularVertices t)))

def preprocess (H : BaseTable) (t : GraphTables.Table) :
    PortTables.Table (vertices t) degree :=
  PreprocessingOverlayTables.lazy
    (PreprocessingOverlayTables.overlay (padded H t) (overlayFamily H t))

def output (H : BaseTable) (t : GraphTables.Table) : PortTables.Input degree :=
  ⟨vertices t, preprocess H t⟩

def graphTable (H : BaseTable) (t : GraphTables.Table) : GraphTables.Table :=
  PortTables.graphTable (preprocess H t)

def outputBits (H : BaseTable) (t : GraphTables.Table) : List Bool :=
  PortTables.tableBits (preprocess H t)

theorem regularVertices_ge_darts (t : GraphTables.Table) : t.darts ≤ regularVertices t := by
  change t.darts ≤ t.darts + _
  omega

theorem regularVertices_le (t : GraphTables.Table) :
    regularVertices t ≤ ExpanderFamily.growth * t.darts := vertexCount_le t

theorem vertices_positive (t : GraphTables.Table) : 0 < vertices t :=
  PreprocessingLevels.paddedSize_positive _

theorem vertices_le_of_positive (t : GraphTables.Table) (ht : 0 < t.darts) :
    vertices t ≤ ExpanderFamily.growth ^ 2 * t.darts := by
  have hr : 0 < regularVertices t := ht.trans_le (regularVertices_ge_darts t)
  calc
    _ ≤ ExpanderFamily.growth * regularVertices t :=
      (PreprocessingLevels.paddedSize_bounds hr).2
    _ ≤ ExpanderFamily.growth * (ExpanderFamily.growth * t.darts) :=
      Nat.mul_le_mul_left _ (regularVertices_le t)
    _ = _ := by ring

theorem vertices_eq_one_of_no_darts (t : GraphTables.Table) (ht : t.darts = 0) :
    vertices t = 1 := by
  unfold vertices regularVertices
  rw [vertexCount_eq_zero_of_no_darts t ht, PreprocessingLevels.paddedSize_zero]

theorem vertices_le (t : GraphTables.Table) :
    vertices t ≤ ExpanderFamily.growth ^ 2 * (t.darts + 1) := by
  by_cases ht : t.darts = 0
  · rw [vertices_eq_one_of_no_darts t ht, ht]
    have hg : 0 < ExpanderFamily.growth := Nat.zero_lt_one.trans ExpanderFamily.growth_gt_one
    have hp : 0 < ExpanderFamily.growth ^ 2 := Nat.pow_pos hg
    simpa using Nat.succ_le_of_lt hp
  · exact (vertices_le_of_positive t (Nat.pos_of_ne_zero ht)).trans
      (Nat.mul_le_mul_left _ (Nat.le_succ _))

theorem darts_eq (H : BaseTable) (t : GraphTables.Table) :
    (graphTable H t).darts = vertices t * degree := rfl

theorem darts_le (H : BaseTable) (t : GraphTables.Table) :
    (graphTable H t).darts ≤ Preprocessing.sizeFactor * (t.darts + 1) := by
  rw [darts_eq]
  calc
    _ ≤ (ExpanderFamily.growth ^ 2 * (t.darts + 1)) * degree :=
      Nat.mul_le_mul_right _ (vertices_le t)
    _ = _ := by rw [degree_eq]; unfold Preprocessing.sizeFactor; ring

theorem vertices_le_inputBits (t : GraphTables.Table) :
    vertices t ≤ ExpanderFamily.growth ^ 2 * ((GraphTables.tableBits t).length + 1) :=
  (vertices_le t).trans (Nat.mul_le_mul_left _
    (Nat.add_le_add_right (GraphTables.darts_le_tableBits_length t) 1))

theorem darts_le_inputBits (H : BaseTable) (t : GraphTables.Table) :
    (graphTable H t).darts ≤
      Preprocessing.sizeFactor * ((GraphTables.tableBits t).length + 1) :=
  (darts_le H t).trans (Nat.mul_le_mul_left _
    (Nat.add_le_add_right (GraphTables.darts_le_tableBits_length t) 1))

end UniqueGames.Foundations.PCP.PreprocessingTables

end OAI
