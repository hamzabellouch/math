import OAI.GameTheory.SnakyConditional.Templates.Level03Part05
import OAI.GameTheory.SnakyConditional.Templates.Level04Part01
import OAI.GameTheory.SnakyConditional.Templates.Level04Part02
import OAI.GameTheory.SnakyConditional.Templates.Level04Part04

namespace OAI

namespace SnakyConditional
def required_19 : Finset Cell := ⟨(([(-2, 0), (-2, 1), (-1, 0), (1, 0), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_19 : Finset Cell := ⟨(([(-3, 1), (-2, 0), (-2, 1), (-1, 0), (0, 0), (1, 0), (1, 1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_19 : Fin 2 → Finset Cell := ![(placedSet 4 (-3, 1) required_6), (placedSet 0 (2, 1) required_6)]
def childrenD_19 : Fin 2 → Finset Cell := ![(placedSet 4 (-3, 1) envelope_6), (placedSet 0 (2, 1) envelope_6)]
theorem common_sub_19 : commonEnvelope childrenD_19 ⊆ insert (0, 0) required_19 := by decide
theorem child_required_sub_19 : ∀ j, childrenC_19 j ⊆ insert (0, 0) required_19 := by decide
theorem child_envelope_sub_19 : ∀ j, childrenD_19 j ⊆ envelope_19 := by decide
theorem pivot_mem_19 : (0, 0) ∈ envelope_19 := by decide
theorem children_work_19 : ∀ j, Template HasSnaky 2 (childrenC_19 j) (childrenD_19 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 4 (-3, 1)).mono (by decide)
  · exact (placed_template_map row_works_6 0 (2, 1)).mono (by decide)
theorem row_works_19 : Template HasSnaky 3 required_19 envelope_19 := by
  refine compose HasSnaky 2 childrenC_19 childrenD_19 children_work_19 (0, 0)
    required_19 envelope_19 pivot_mem_19 child_required_sub_19 child_envelope_sub_19 ?_
  intro b hb; exact common_sub_19 (mem_commonEnvelope childrenD_19 b hb)
def required_20 : Finset Cell := ⟨(([(-3, 0), (-3, 1), (-2, 0), (-1, 0), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_20 : Finset Cell := ⟨(([(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (0, 0), (0, 1), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_20 : Fin 2 → Finset Cell := ![(placedSet 4 (-4, 1) required_6), (placedSet 0 (1, 1) required_6)]
def childrenD_20 : Fin 2 → Finset Cell := ![(placedSet 4 (-4, 1) envelope_6), (placedSet 0 (1, 1) envelope_6)]
theorem common_sub_20 : commonEnvelope childrenD_20 ⊆ insert (0, 0) required_20 := by decide
theorem child_required_sub_20 : ∀ j, childrenC_20 j ⊆ insert (0, 0) required_20 := by decide
theorem child_envelope_sub_20 : ∀ j, childrenD_20 j ⊆ envelope_20 := by decide
theorem pivot_mem_20 : (0, 0) ∈ envelope_20 := by decide
theorem children_work_20 : ∀ j, Template HasSnaky 2 (childrenC_20 j) (childrenD_20 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 4 (-4, 1)).mono (by decide)
  · exact (placed_template_map row_works_6 0 (1, 1)).mono (by decide)
theorem row_works_20 : Template HasSnaky 3 required_20 envelope_20 := by
  refine compose HasSnaky 2 childrenC_20 childrenD_20 children_work_20 (0, 0)
    required_20 envelope_20 pivot_mem_20 child_required_sub_20 child_envelope_sub_20 ?_
  intro b hb; exact common_sub_20 (mem_commonEnvelope childrenD_20 b hb)
def required_21 : Finset Cell := ⟨(([(-3, -1), (-2, 0), (-1, 0), (1, 0), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_21 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-2, 0), (-1, 0), (0, 0), (1, 0), (1, 1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_21 : Fin 2 → Finset Cell := ![(placedSet 6 (-2, -1) required_4), (placedSet 0 (2, 1) required_6)]
def childrenD_21 : Fin 2 → Finset Cell := ![(placedSet 6 (-2, -1) envelope_4), (placedSet 0 (2, 1) envelope_6)]
theorem common_sub_21 : commonEnvelope childrenD_21 ⊆ insert (0, 0) required_21 := by decide
theorem child_required_sub_21 : ∀ j, childrenC_21 j ⊆ insert (0, 0) required_21 := by decide
theorem child_envelope_sub_21 : ∀ j, childrenD_21 j ⊆ envelope_21 := by decide
theorem pivot_mem_21 : (0, 0) ∈ envelope_21 := by decide
theorem children_work_21 : ∀ j, Template HasSnaky 2 (childrenC_21 j) (childrenD_21 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_4 6 (-2, -1)).mono (by decide)
  · exact (placed_template_map row_works_6 0 (2, 1)).mono (by decide)
theorem row_works_21 : Template HasSnaky 3 required_21 envelope_21 := by
  refine compose HasSnaky 2 childrenC_21 childrenD_21 children_work_21 (0, 0)
    required_21 envelope_21 pivot_mem_21 child_required_sub_21 child_envelope_sub_21 ?_
  intro b hb; exact common_sub_21 (mem_commonEnvelope childrenD_21 b hb)
def required_24 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_24 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_24 : Fin 2 → Finset Cell := ![(placedSet 0 (-4, -1) required_0), (placedSet 0 (1, 0) required_17)]
def childrenD_24 : Fin 2 → Finset Cell := ![(placedSet 0 (-4, -1) envelope_0), (placedSet 0 (1, 0) envelope_17)]
theorem common_sub_24 : commonEnvelope childrenD_24 ⊆ insert (0, 0) required_24 := by decide
theorem child_required_sub_24 : ∀ j, childrenC_24 j ⊆ insert (0, 0) required_24 := by decide
theorem child_envelope_sub_24 : ∀ j, childrenD_24 j ⊆ envelope_24 := by decide
theorem pivot_mem_24 : (0, 0) ∈ envelope_24 := by decide
theorem children_work_24 : ∀ j, Template HasSnaky 2 (childrenC_24 j) (childrenD_24 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 0 (-4, -1)).mono (by decide)
  · exact (placed_template_map row_works_17 0 (1, 0)).mono (by decide)
theorem row_works_24 : Template HasSnaky 3 required_24 envelope_24 := by
  refine compose HasSnaky 2 childrenC_24 childrenD_24 children_work_24 (0, 0)
    required_24 envelope_24 pivot_mem_24 child_required_sub_24 child_envelope_sub_24 ?_
  intro b hb; exact common_sub_24 (mem_commonEnvelope childrenD_24 b hb)
def required_25 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_25 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_25 : Fin 2 → Finset Cell := ![(placedSet 0 (-4, -1) required_0), (placedSet 0 (1, 0) required_14)]
def childrenD_25 : Fin 2 → Finset Cell := ![(placedSet 0 (-4, -1) envelope_0), (placedSet 0 (1, 0) envelope_14)]
theorem common_sub_25 : commonEnvelope childrenD_25 ⊆ insert (0, 0) required_25 := by decide
theorem child_required_sub_25 : ∀ j, childrenC_25 j ⊆ insert (0, 0) required_25 := by decide
theorem child_envelope_sub_25 : ∀ j, childrenD_25 j ⊆ envelope_25 := by decide
theorem pivot_mem_25 : (0, 0) ∈ envelope_25 := by decide
theorem children_work_25 : ∀ j, Template HasSnaky 2 (childrenC_25 j) (childrenD_25 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 0 (-4, -1)).mono (by decide)
  · exact (placed_template_map row_works_14 0 (1, 0)).mono (by decide)
theorem row_works_25 : Template HasSnaky 3 required_25 envelope_25 := by
  refine compose HasSnaky 2 childrenC_25 childrenD_25 children_work_25 (0, 0)
    required_25 envelope_25 pivot_mem_25 child_required_sub_25 child_envelope_sub_25 ?_
  intro b hb; exact common_sub_25 (mem_commonEnvelope childrenD_25 b hb)
end SnakyConditional

end OAI
