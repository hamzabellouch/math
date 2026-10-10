import OAI.GameTheory.SnakyConditional.Regions.Region603
import OAI.GameTheory.SnakyConditional.Templates.Level13Part07
import OAI.GameTheory.SnakyConditional.Templates.Level16Part07
import OAI.GameTheory.SnakyConditional.Templates.Level21Part05
import OAI.GameTheory.SnakyConditional.Templates.Level24Part04
import OAI.GameTheory.SnakyConditional.Templates.Level28Part04

namespace OAI

namespace SnakyConditional
theorem Internal.SnakyRows011H.named_envelope_603_5_head : (named_envelope_603_5.map Internal.SnakyRows011H.namedCellKey).head? = some (-772 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_4_head : (named_envelope_603_4.map Internal.SnakyRows011H.namedCellKey).head? = some (-772 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_5 Internal.SnakyRows011H.named_envelope_603_6 (-772 : ℤ) Internal.SnakyRows011H.named_envelope_603_5_head
theorem Internal.SnakyRows011H.named_envelope_603_3_head : (named_envelope_603_3.map Internal.SnakyRows011H.namedCellKey).head? = some (-772 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_4 Internal.SnakyRows011H.named_envelope_603_7 (-772 : ℤ) Internal.SnakyRows011H.named_envelope_603_4_head
theorem Internal.SnakyRows011H.named_envelope_603_2_head : (named_envelope_603_2.map Internal.SnakyRows011H.namedCellKey).head? = some (-772 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_3 Internal.SnakyRows011H.named_envelope_603_10 (-772 : ℤ) Internal.SnakyRows011H.named_envelope_603_3_head
theorem Internal.SnakyRows011H.named_envelope_603_1_head : (named_envelope_603_1.map Internal.SnakyRows011H.namedCellKey).head? = some (-772 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_2 Internal.SnakyRows011H.named_envelope_603_17 (-772 : ℤ) Internal.SnakyRows011H.named_envelope_603_2_head
theorem Internal.SnakyRows011H.named_envelope_603_62_last : (named_envelope_603_62.map Internal.SnakyRows011H.namedCellKey).getLast? = some (1539 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_60_last : (named_envelope_603_60.map Internal.SnakyRows011H.namedCellKey).getLast? = some (1539 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_61 Internal.SnakyRows011H.named_envelope_603_62 (1539 : ℤ) Internal.SnakyRows011H.named_envelope_603_62_last
theorem Internal.SnakyRows011H.named_envelope_603_56_last : (named_envelope_603_56.map Internal.SnakyRows011H.namedCellKey).getLast? = some (1539 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_57 Internal.SnakyRows011H.named_envelope_603_60 (1539 : ℤ) Internal.SnakyRows011H.named_envelope_603_60_last
theorem Internal.SnakyRows011H.named_envelope_603_48_last : (named_envelope_603_48.map Internal.SnakyRows011H.namedCellKey).getLast? = some (1539 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_49 Internal.SnakyRows011H.named_envelope_603_56 (1539 : ℤ) Internal.SnakyRows011H.named_envelope_603_56_last
theorem Internal.SnakyRows011H.named_envelope_603_32_last : (named_envelope_603_32.map Internal.SnakyRows011H.namedCellKey).getLast? = some (1539 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_33 Internal.SnakyRows011H.named_envelope_603_48 (1539 : ℤ) Internal.SnakyRows011H.named_envelope_603_48_last
theorem Internal.SnakyRows011H.named_envelope_603_0_head : (named_envelope_603_0.map Internal.SnakyRows011H.namedCellKey).head? = some (-772 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_1 Internal.SnakyRows011H.named_envelope_603_32 (-772 : ℤ) Internal.SnakyRows011H.named_envelope_603_1_head
theorem Internal.SnakyRows011H.named_envelope_603_0_last : (named_envelope_603_0.map Internal.SnakyRows011H.namedCellKey).getLast? = some (1539 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_1 Internal.SnakyRows011H.named_envelope_603_32 (1539 : ℤ) Internal.SnakyRows011H.named_envelope_603_32_last
def childrenC_603 : Fin 12 → Finset Cell := ![(placedSet 1 (1, 0) required_505), (placedSet 5 (1, 0) required_505), (placedSet 5 (1, 0) required_586), (placedSet 7 (1, 0) required_551), (placedSet 6 (0, -2) required_531), (placedSet 1 (1, 0) required_586), (placedSet 1 (1, 0) required_585), (placedSet 5 (1, 0) required_585), (placedSet 3 (1, 0) required_551), (placedSet 1 (1, 0) required_573), (placedSet 5 (1, 0) required_533), (placedSet 1 (1, 0) required_533)]
def childrenD_603 : Fin 12 → Finset Cell := ![(placedSet 1 (1, 0) envelope_505), (placedSet 5 (1, 0) envelope_505), (placedSet 5 (1, 0) envelope_586), (placedSet 7 (1, 0) envelope_551), (placedSet 6 (0, -2) envelope_531), (placedSet 1 (1, 0) envelope_586), (placedSet 1 (1, 0) envelope_585), (placedSet 5 (1, 0) envelope_585), (placedSet 3 (1, 0) envelope_551), (placedSet 1 (1, 0) envelope_573), (placedSet 5 (1, 0) envelope_533), (placedSet 1 (1, 0) envelope_533)]
theorem common_sub_603 : commonEnvelope childrenD_603 ⊆ insert (0, 0) required_603 := by decide
theorem child_required_sub_603 : ∀ j, childrenC_603 j ⊆ insert (0, 0) required_603 := by decide
theorem Internal.SnakyRows011H.containment_603_0 :
    placedSet 1 (1, 0) envelope_505 ⊆ envelope_603 := by decide
theorem Internal.SnakyRows011H.containment_603_1 :
    placedSet 5 (1, 0) envelope_505 ⊆ envelope_603 := by decide
theorem Internal.SnakyRows011H.containment_603_2 :
    placedSet 5 (1, 0) envelope_586 ⊆ envelope_603 := by decide +kernel
theorem Internal.SnakyRows011H.containment_603_3 :
    placedSet 7 (1, 0) envelope_551 ⊆ envelope_603 := by decide
theorem Internal.SnakyRows011H.containment_603_4 :
    placedSet 6 (0, -2) envelope_531 ⊆ envelope_603 := by decide
theorem Internal.SnakyRows011H.containment_603_5 :
    placedSet 1 (1, 0) envelope_586 ⊆ envelope_603 := by decide +kernel
theorem Internal.SnakyRows011H.containment_603_6 :
    placedSet 1 (1, 0) envelope_585 ⊆ envelope_603 := by decide +kernel
theorem Internal.SnakyRows011H.containment_603_7 :
    placedSet 5 (1, 0) envelope_585 ⊆ envelope_603 := by decide +kernel
theorem Internal.SnakyRows011H.containment_603_8 :
    placedSet 3 (1, 0) envelope_551 ⊆ envelope_603 := by decide
theorem Internal.SnakyRows011H.containment_603_9 :
    placedSet 1 (1, 0) envelope_573 ⊆ envelope_603 := by decide +kernel
theorem Internal.SnakyRows011H.containment_603_10 :
    placedSet 5 (1, 0) envelope_533 ⊆ envelope_603 := by decide
theorem Internal.SnakyRows011H.containment_603_11 :
    placedSet 1 (1, 0) envelope_533 ⊆ envelope_603 := by decide
theorem child_envelope_sub_603 : ∀ j, childrenD_603 j ⊆ envelope_603 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows011H.containment_603_0
  · exact Internal.SnakyRows011H.containment_603_1
  · exact Internal.SnakyRows011H.containment_603_2
  · exact Internal.SnakyRows011H.containment_603_3
  · exact Internal.SnakyRows011H.containment_603_4
  · exact Internal.SnakyRows011H.containment_603_5
  · exact Internal.SnakyRows011H.containment_603_6
  · exact Internal.SnakyRows011H.containment_603_7
  · exact Internal.SnakyRows011H.containment_603_8
  · exact Internal.SnakyRows011H.containment_603_9
  · exact Internal.SnakyRows011H.containment_603_10
  · exact Internal.SnakyRows011H.containment_603_11
theorem pivot_mem_603 : (0, 0) ∈ envelope_603 := by decide
theorem children_work_603 : ∀ j, Template HasSnaky 26 (childrenC_603 j) (childrenD_603 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_505 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_505 5 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_586 5 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_551 7 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_531 6 (0, -2)).mono (by decide)
  · exact (placed_template_map row_works_586 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_585 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_585 5 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_551 3 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_573 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_533 5 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_533 1 (1, 0)).mono (by decide)
theorem row_works_603 : Template HasSnaky 27 required_603 envelope_603 := by
  refine compose HasSnaky 26 childrenC_603 childrenD_603 children_work_603 (0, 0)
    required_603 envelope_603 pivot_mem_603 child_required_sub_603 child_envelope_sub_603 ?_
  intro b hb; exact common_sub_603 (mem_commonEnvelope childrenD_603 b hb)
end SnakyConditional

end OAI
