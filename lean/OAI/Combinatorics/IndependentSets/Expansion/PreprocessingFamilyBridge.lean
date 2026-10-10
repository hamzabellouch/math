import Mathlib
import OAI.Combinatorics.IndependentSets.Expansion.PreprocessingRegularTables
import OAI.Combinatorics.IndependentSets.Expansion.ExpanderTableWords

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PreprocessingFamilyBridge

open PreprocessingCloudIndex PreprocessingRegularTables ExpanderTableWords
open IndependentSetsGames.Foundations.Complexity (encodeWords)

theorem rotationWords_resizeTable {n m q : Nat} (h : n = m)
    (table : ExpanderTables.Table n q) :
    rotationWords (resizeTable h table) = rotationWords table := by
  cases h
  rfl

theorem familyRotor_eq_familyCloudTable (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (hk : 0 < cloudSize t v) :
    encodeWords (rotationWords (ExpanderTables.family H
      (PreprocessingLevels.boundedLevel (cloudSize t v)))) =
      encodeWords (rotationWords (familyCloudTable H t v)) := by
  unfold familyCloudTable
  rw [dite_eq_right (Nat.ne_of_gt hk)]
  exact congrArg encodeWords (rotationWords_resizeTable _ _).symm

theorem cloudSize_pos_of_dart (t : GraphTables.Table) (e : Fin t.darts) :
    0 < cloudSize t t.rows[e].tail := by
  have h := (oldCloudIndex t e).isLt
  omega

theorem padding_zero_of_cloudSize_zero (t : GraphTables.Table) (v : Fin t.vertices)
    (hk : cloudSize t v = 0) : padding t v = 0 := by
  simp only [padding, hk, PreprocessingLevels.cloudPaddedSize_zero, Nat.sub_zero]

theorem cloudSize_pos_of_dummy (t : GraphTables.Table) (v : Fin t.vertices)
    (j : Fin (padding t v)) : 0 < cloudSize t v := by
  by_contra h
  have hk := Nat.eq_zero_of_not_pos h
  have hp := padding_zero_of_cloudSize_zero t v hk
  have hj := j.isLt
  omega

theorem cloudSize_pos_of_paddedCloud (t : GraphTables.Table) (v : Fin t.vertices)
    (x : PaddedCloud t (padding t) v) : 0 < cloudSize t v := by
  by_contra h
  have hk := Nat.eq_zero_of_not_pos h
  have hp := padding_zero_of_cloudSize_zero t v hk
  have hx := (paddedCloudRank t (padding t) v x).isLt
  omega

theorem familyCloudWords_of_zero (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (hk : cloudSize t v = 0) :
    encodeWords (rotationWords (familyCloudTable H t v)) = [] := by
  have hl : (rotationWords (familyCloudTable H t v)).length = 0 := by
    rw [rotationWords_length, cloudSize_add_padding, hk,
      PreprocessingLevels.cloudPaddedSize_zero, Nat.zero_mul]
  rw [List.length_eq_zero_iff.mp hl]
  rfl

end IndependentSetsGames.Foundations.PCP.PreprocessingFamilyBridge

end OAI
