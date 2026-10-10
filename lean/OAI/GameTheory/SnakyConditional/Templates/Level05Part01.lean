import OAI.GameTheory.SnakyConditional.Templates.Level03Part05
import OAI.GameTheory.SnakyConditional.Templates.Level04Part01

namespace OAI

namespace SnakyConditional
def required_7 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-2, -1), (-1, -1), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_7 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_7 : Fin 2 → Finset Cell := ![(placedSet 0 (-1, 0) required_4), (placedSet 0 (1, 0) required_6)]
def childrenD_7 : Fin 2 → Finset Cell := ![(placedSet 0 (-1, 0) envelope_4), (placedSet 0 (1, 0) envelope_6)]
theorem common_sub_7 : commonEnvelope childrenD_7 ⊆ insert (0, 0) required_7 := by decide
theorem child_required_sub_7 : ∀ j, childrenC_7 j ⊆ insert (0, 0) required_7 := by decide
theorem child_envelope_sub_7 : ∀ j, childrenD_7 j ⊆ envelope_7 := by decide
theorem pivot_mem_7 : (0, 0) ∈ envelope_7 := by decide
theorem children_work_7 : ∀ j, Template HasSnaky 2 (childrenC_7 j) (childrenD_7 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_4 0 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_6 0 (1, 0)).mono (by decide)
theorem row_works_7 : Template HasSnaky 3 required_7 envelope_7 := by
  refine compose HasSnaky 2 childrenC_7 childrenD_7 children_work_7 (0, 0)
    required_7 envelope_7 pivot_mem_7 child_required_sub_7 child_envelope_sub_7 ?_
  intro b hb; exact common_sub_7 (mem_commonEnvelope childrenD_7 b hb)
def required_8 : Finset Cell := ⟨(([(0, -1), (1, -1), (1, 0), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_8 : Finset Cell := ⟨(([(-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_8 : Fin 2 → Finset Cell := ![(placedSet 4 (4, -1) required_0), (placedSet 4 (-1, 0) required_6)]
def childrenD_8 : Fin 2 → Finset Cell := ![(placedSet 4 (4, -1) envelope_0), (placedSet 4 (-1, 0) envelope_6)]
theorem common_sub_8 : commonEnvelope childrenD_8 ⊆ insert (0, 0) required_8 := by decide
theorem child_required_sub_8 : ∀ j, childrenC_8 j ⊆ insert (0, 0) required_8 := by decide
theorem child_envelope_sub_8 : ∀ j, childrenD_8 j ⊆ envelope_8 := by decide
theorem pivot_mem_8 : (0, 0) ∈ envelope_8 := by decide
theorem children_work_8 : ∀ j, Template HasSnaky 2 (childrenC_8 j) (childrenD_8 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 4 (4, -1)).mono (by decide)
  · exact (placed_template_map row_works_6 4 (-1, 0)).mono (by decide)
theorem row_works_8 : Template HasSnaky 3 required_8 envelope_8 := by
  refine compose HasSnaky 2 childrenC_8 childrenD_8 children_work_8 (0, 0)
    required_8 envelope_8 pivot_mem_8 child_required_sub_8 child_envelope_sub_8 ?_
  intro b hb; exact common_sub_8 (mem_commonEnvelope childrenD_8 b hb)
def required_9 : Finset Cell := ⟨(([(-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_9 : Finset Cell := ⟨(([(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (0, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_9 : Fin 2 → Finset Cell := ![(placedSet 4 (1, 0) required_0), (placedSet 4 (-4, 1) required_6)]
def childrenD_9 : Fin 2 → Finset Cell := ![(placedSet 4 (1, 0) envelope_0), (placedSet 4 (-4, 1) envelope_6)]
theorem common_sub_9 : commonEnvelope childrenD_9 ⊆ insert (0, 0) required_9 := by decide
theorem child_required_sub_9 : ∀ j, childrenC_9 j ⊆ insert (0, 0) required_9 := by decide
theorem child_envelope_sub_9 : ∀ j, childrenD_9 j ⊆ envelope_9 := by decide
theorem pivot_mem_9 : (0, 0) ∈ envelope_9 := by decide
theorem children_work_9 : ∀ j, Template HasSnaky 2 (childrenC_9 j) (childrenD_9 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 4 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_6 4 (-4, 1)).mono (by decide)
theorem row_works_9 : Template HasSnaky 3 required_9 envelope_9 := by
  refine compose HasSnaky 2 childrenC_9 childrenD_9 children_work_9 (0, 0)
    required_9 envelope_9 pivot_mem_9 child_required_sub_9 child_envelope_sub_9 ?_
  intro b hb; exact common_sub_9 (mem_commonEnvelope childrenD_9 b hb)
def required_11 : Finset Cell := ⟨(([(-1, -1), (-1, 0), (-1, 1), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_11 : Finset Cell := ⟨(([(-2, -1), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, 0), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_11 : Fin 2 → Finset Cell := ![(placedSet 4 (-2, 1) required_6), (placedSet 6 (-2, -1) required_6)]
def childrenD_11 : Fin 2 → Finset Cell := ![(placedSet 4 (-2, 1) envelope_6), (placedSet 6 (-2, -1) envelope_6)]
theorem common_sub_11 : commonEnvelope childrenD_11 ⊆ insert (0, 0) required_11 := by decide
theorem child_required_sub_11 : ∀ j, childrenC_11 j ⊆ insert (0, 0) required_11 := by decide
theorem child_envelope_sub_11 : ∀ j, childrenD_11 j ⊆ envelope_11 := by decide
theorem pivot_mem_11 : (0, 0) ∈ envelope_11 := by decide
theorem children_work_11 : ∀ j, Template HasSnaky 2 (childrenC_11 j) (childrenD_11 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 4 (-2, 1)).mono (by decide)
  · exact (placed_template_map row_works_6 6 (-2, -1)).mono (by decide)
theorem row_works_11 : Template HasSnaky 3 required_11 envelope_11 := by
  refine compose HasSnaky 2 childrenC_11 childrenD_11 children_work_11 (0, 0)
    required_11 envelope_11 pivot_mem_11 child_required_sub_11 child_envelope_sub_11 ?_
  intro b hb; exact common_sub_11 (mem_commonEnvelope childrenD_11 b hb)
def required_13 : Finset Cell := ⟨(([(-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_13 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (0, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_13 : Fin 2 → Finset Cell := ![(placedSet 6 (-4, -1) required_6), (placedSet 4 (-4, 1) required_6)]
def childrenD_13 : Fin 2 → Finset Cell := ![(placedSet 6 (-4, -1) envelope_6), (placedSet 4 (-4, 1) envelope_6)]
theorem common_sub_13 : commonEnvelope childrenD_13 ⊆ insert (0, 0) required_13 := by decide
theorem child_required_sub_13 : ∀ j, childrenC_13 j ⊆ insert (0, 0) required_13 := by decide
theorem child_envelope_sub_13 : ∀ j, childrenD_13 j ⊆ envelope_13 := by decide
theorem pivot_mem_13 : (0, 0) ∈ envelope_13 := by decide
theorem children_work_13 : ∀ j, Template HasSnaky 2 (childrenC_13 j) (childrenD_13 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 6 (-4, -1)).mono (by decide)
  · exact (placed_template_map row_works_6 4 (-4, 1)).mono (by decide)
theorem row_works_13 : Template HasSnaky 3 required_13 envelope_13 := by
  refine compose HasSnaky 2 childrenC_13 childrenD_13 children_work_13 (0, 0)
    required_13 envelope_13 pivot_mem_13 child_required_sub_13 child_envelope_sub_13 ?_
  intro b hb; exact common_sub_13 (mem_commonEnvelope childrenD_13 b hb)
end SnakyConditional

end OAI
