import OAI.GameTheory.SnakyConditional.Templates.Level16Part07
import OAI.GameTheory.SnakyConditional.Templates.Level27Part02
import OAI.GameTheory.SnakyConditional.Templates.Level28Part04

namespace OAI

namespace SnakyConditional
theorem Internal.SnakyRows010.named_envelope_595_4_head : (named_envelope_595_4.map Internal.SnakyRows010.namedCellKey).head? = some (-769 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_595_3_head : (named_envelope_595_3.map Internal.SnakyRows010.namedCellKey).head? = some (-769 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_595_4 Internal.SnakyRows010.named_envelope_595_5 (-769 : ℤ) Internal.SnakyRows010.named_envelope_595_4_head
theorem Internal.SnakyRows010.named_envelope_595_2_head : (named_envelope_595_2.map Internal.SnakyRows010.namedCellKey).head? = some (-769 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_595_3 Internal.SnakyRows010.named_envelope_595_6 (-769 : ℤ) Internal.SnakyRows010.named_envelope_595_3_head
theorem Internal.SnakyRows010.named_envelope_595_1_head : (named_envelope_595_1.map Internal.SnakyRows010.namedCellKey).head? = some (-769 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_595_2 Internal.SnakyRows010.named_envelope_595_9 (-769 : ℤ) Internal.SnakyRows010.named_envelope_595_2_head
theorem Internal.SnakyRows010.named_envelope_595_30_last : (named_envelope_595_30.map Internal.SnakyRows010.namedCellKey).getLast? = some (1535 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_595_28_last : (named_envelope_595_28.map Internal.SnakyRows010.namedCellKey).getLast? = some (1535 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_595_29 Internal.SnakyRows010.named_envelope_595_30 (1535 : ℤ) Internal.SnakyRows010.named_envelope_595_30_last
theorem Internal.SnakyRows010.named_envelope_595_24_last : (named_envelope_595_24.map Internal.SnakyRows010.namedCellKey).getLast? = some (1535 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_595_25 Internal.SnakyRows010.named_envelope_595_28 (1535 : ℤ) Internal.SnakyRows010.named_envelope_595_28_last
theorem Internal.SnakyRows010.named_envelope_595_16_last : (named_envelope_595_16.map Internal.SnakyRows010.namedCellKey).getLast? = some (1535 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_595_17 Internal.SnakyRows010.named_envelope_595_24 (1535 : ℤ) Internal.SnakyRows010.named_envelope_595_24_last
theorem Internal.SnakyRows010.named_envelope_595_0_head : (named_envelope_595_0.map Internal.SnakyRows010.namedCellKey).head? = some (-769 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_595_1 Internal.SnakyRows010.named_envelope_595_16 (-769 : ℤ) Internal.SnakyRows010.named_envelope_595_1_head
theorem Internal.SnakyRows010.named_envelope_595_0_last : (named_envelope_595_0.map Internal.SnakyRows010.namedCellKey).getLast? = some (1535 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_595_1 Internal.SnakyRows010.named_envelope_595_16 (1535 : ℤ) Internal.SnakyRows010.named_envelope_595_16_last
def childrenC_595 : Fin 7 → Finset Cell := ![(placedSet 4 (-2, 0) required_460), (placedSet 2 (1, 0) required_460), (placedSet 1 (1, 0) required_586), (placedSet 4 (1, 0) required_411), (placedSet 1 (-2, 0) required_551), (placedSet 5 (1, 0) required_406), (placedSet 0 (-2, 0) required_572)]
def childrenD_595 : Fin 7 → Finset Cell := ![(placedSet 4 (-2, 0) envelope_460), (placedSet 2 (1, 0) envelope_460), (placedSet 1 (1, 0) envelope_586), (placedSet 4 (1, 0) envelope_411), (placedSet 1 (-2, 0) envelope_551), (placedSet 5 (1, 0) envelope_406), (placedSet 0 (-2, 0) envelope_572)]
theorem common_sub_595 : commonEnvelope childrenD_595 ⊆ insert (0, 0) required_595 := by decide
theorem child_required_sub_595 : ∀ j, childrenC_595 j ⊆ insert (0, 0) required_595 := by decide
theorem Internal.SnakyRows010.containment_595_0 :
    placedSet 4 (-2, 0) envelope_460 ⊆ envelope_595 := by decide
theorem Internal.SnakyRows010.containment_595_1 :
    placedSet 2 (1, 0) envelope_460 ⊆ envelope_595 := by decide
theorem Internal.SnakyRows010.containment_595_2 :
    placedSet 1 (1, 0) envelope_586 ⊆ envelope_595 := by decide +kernel
theorem Internal.SnakyRows010.containment_595_3 :
    placedSet 4 (1, 0) envelope_411 ⊆ envelope_595 := by decide
theorem Internal.SnakyRows010.containment_595_4 :
    placedSet 1 (-2, 0) envelope_551 ⊆ envelope_595 := by decide
theorem Internal.SnakyRows010.containment_595_5 :
    placedSet 5 (1, 0) envelope_406 ⊆ envelope_595 := by decide
theorem Internal.SnakyRows010.containment_595_6 :
    placedSet 0 (-2, 0) envelope_572 ⊆ envelope_595 := by decide +kernel
theorem child_envelope_sub_595 : ∀ j, childrenD_595 j ⊆ envelope_595 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows010.containment_595_0
  · exact Internal.SnakyRows010.containment_595_1
  · exact Internal.SnakyRows010.containment_595_2
  · exact Internal.SnakyRows010.containment_595_3
  · exact Internal.SnakyRows010.containment_595_4
  · exact Internal.SnakyRows010.containment_595_5
  · exact Internal.SnakyRows010.containment_595_6
theorem pivot_mem_595 : (0, 0) ∈ envelope_595 := by decide
theorem children_work_595 : ∀ j, Template HasSnaky 26 (childrenC_595 j) (childrenD_595 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_460 4 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_460 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_586 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_411 4 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_551 1 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_406 5 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_572 0 (-2, 0)).mono (by decide)
theorem row_works_595 : Template HasSnaky 27 required_595 envelope_595 := by
  refine compose HasSnaky 26 childrenC_595 childrenD_595 children_work_595 (0, 0)
    required_595 envelope_595 pivot_mem_595 child_required_sub_595 child_envelope_sub_595 ?_
  intro b hb; exact common_sub_595 (mem_commonEnvelope childrenD_595 b hb)
end SnakyConditional

end OAI
