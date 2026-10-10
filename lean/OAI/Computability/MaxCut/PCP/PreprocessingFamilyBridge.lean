import Mathlib
import OAI.Computability.MaxCut.Machines.MachinePaddedExpanderFamilyBounds

namespace OAI

/-!
# Exact serialized family tables at actual regularization vertices

The geometric family maps request zero to a one-vertex table. Empty clouds in
regularization instead remain empty. The bridge therefore requires positive
cloud size, derived here from each actual original or dummy vertex.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingFamilyBridge

open PreprocessingCloudIndex PreprocessingRegularTables ExpanderTableWords
open MaxCutGames.Foundations.Complexity (encodeWords)

/-- Transporting only the size equality leaves every serialized rotor entry
unchanged; no relabeling or alternative numbering is introduced. -/
theorem rotationWords_resizeTable {n m q : Nat} (h : n = m)
    (table : ExpanderTables.Table n q) :
    rotationWords (resizeTable h table) = rotationWords table := by
  cases h
  rfl

/-- This left side is definitionally the output `MachineRegularFamily.rotor`
for the request on its physical core tape 4. The right side is exactly the
archive expected on core tape 7 by the internal-row machine. -/
theorem familyRotor_eq_familyCloudTable (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (hk : 0 < cloudSize t v) :
    encodeWords (rotationWords (ExpanderTables.family H
      (PreprocessingLevels.boundedLevel (cloudSize t v)))) =
      encodeWords (rotationWords (familyCloudTable H t v)) := by
  unfold familyCloudTable
  rw [dite_eq_right (Nat.ne_of_gt hk)]
  erw [rotationWords_resizeTable]
  rfl

/-- An actual original dart supplies a member of its owner's cloud. -/
theorem cloudSize_pos_of_dart (t : GraphTables.Table) (e : Fin t.darts) :
    0 < cloudSize t t.rows[e].tail := by
  have h := (oldCloudIndex t e).isLt
  omega

/-- An empty cloud has no padding vertices either. -/
theorem padding_zero_of_cloudSize_zero (t : GraphTables.Table) (v : Fin t.vertices)
    (hk : cloudSize t v = 0) : padding t v = 0 := by
  simp only [padding, hk, PreprocessingLevels.cloudPaddedSize_zero, Nat.sub_zero]

/-- Every actual dummy vertex also belongs to a positive original cloud. -/
theorem cloudSize_pos_of_dummy (t : GraphTables.Table) (v : Fin t.vertices)
    (j : Fin (padding t v)) : 0 < cloudSize t v := by
  by_contra h
  have hk := Nat.eq_zero_of_not_pos h
  have hp := padding_zero_of_cloudSize_zero t v hk
  have hj := j.isLt
  omega

/-- The same positivity fact for the common local coordinate interface. -/
theorem cloudSize_pos_of_paddedCloud (t : GraphTables.Table) (v : Fin t.vertices)
    (x : PaddedCloud t (padding t) v) : 0 < cloudSize t v := by
  by_contra h
  have hk := Nat.eq_zero_of_not_pos h
  have hp := padding_zero_of_cloudSize_zero t v hk
  have hx := (paddedCloudRank t (padding t) v x).isLt
  omega

/-- The zero-cloud branch remains genuinely empty, including its serialized
rotor archive. It is not replaced by the geometric family at request zero. -/
theorem familyCloudWords_of_zero (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (hk : cloudSize t v = 0) :
    encodeWords (rotationWords (familyCloudTable H t v)) = [] := by
  have hl : (rotationWords (familyCloudTable H t v)).length = 0 := by
    rw [rotationWords_length, cloudSize_add_padding, hk,
      PreprocessingLevels.cloudPaddedSize_zero, Nat.zero_mul]
  rw [List.length_eq_zero_iff.mp hl]
  rfl

end MaxCutGames.Foundations.PCP.PreprocessingFamilyBridge

end OAI
