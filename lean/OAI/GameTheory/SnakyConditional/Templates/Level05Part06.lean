import OAI.GameTheory.SnakyConditional.Templates.Level03Part02
import OAI.GameTheory.SnakyConditional.Templates.Level04Part01

namespace OAI

namespace SnakyConditional
def required_41 : Finset Cell := ⟨(([(-1, 0), (0, -3), (0, -2), (0, -1), (1, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_41 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -1), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_41 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, 1) required_6), (placedSet 4 (2, -1) required_1)]
def childrenD_41 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, 1) envelope_6), (placedSet 4 (2, -1) envelope_1)]
theorem common_sub_41 : commonEnvelope childrenD_41 ⊆ insert (0, 0) required_41 := by decide
theorem child_required_sub_41 : ∀ j, childrenC_41 j ⊆ insert (0, 0) required_41 := by decide
theorem child_envelope_sub_41 : ∀ j, childrenD_41 j ⊆ envelope_41 := by decide
theorem pivot_mem_41 : (0, 0) ∈ envelope_41 := by decide
theorem children_work_41 : ∀ j, Template HasSnaky 2 (childrenC_41 j) (childrenD_41 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_1 4 (2, -1)).mono (by decide)
theorem row_works_41 : Template HasSnaky 3 required_41 envelope_41 := by
  refine compose HasSnaky 2 childrenC_41 childrenD_41 children_work_41 (0, 0)
    required_41 envelope_41 pivot_mem_41 child_required_sub_41 child_envelope_sub_41 ?_
  intro b hb; exact common_sub_41 (mem_commonEnvelope childrenD_41 b hb)
def required_42 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_42 : Finset Cell := ⟨(([(-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (0, 0), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_42 : Fin 2 → Finset Cell := ![(placedSet 6 (2, 0) required_0), (placedSet 4 (-3, 1) required_6)]
def childrenD_42 : Fin 2 → Finset Cell := ![(placedSet 6 (2, 0) envelope_0), (placedSet 4 (-3, 1) envelope_6)]
theorem common_sub_42 : commonEnvelope childrenD_42 ⊆ insert (0, 0) required_42 := by decide
theorem child_required_sub_42 : ∀ j, childrenC_42 j ⊆ insert (0, 0) required_42 := by decide
theorem child_envelope_sub_42 : ∀ j, childrenD_42 j ⊆ envelope_42 := by decide
theorem pivot_mem_42 : (0, 0) ∈ envelope_42 := by decide
theorem children_work_42 : ∀ j, Template HasSnaky 2 (childrenC_42 j) (childrenD_42 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 6 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_6 4 (-3, 1)).mono (by decide)
theorem row_works_42 : Template HasSnaky 3 required_42 envelope_42 := by
  refine compose HasSnaky 2 childrenC_42 childrenD_42 children_work_42 (0, 0)
    required_42 envelope_42 pivot_mem_42 child_required_sub_42 child_envelope_sub_42 ?_
  intro b hb; exact common_sub_42 (mem_commonEnvelope childrenD_42 b hb)
def required_43 : Finset Cell := ⟨(([(-1, 0), (0, -3), (0, -2), (0, -1), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_43 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -1), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_43 : Fin 2 → Finset Cell := ![(placedSet 4 (1, -1) required_2), (placedSet 3 (-1, 1) required_6)]
def childrenD_43 : Fin 2 → Finset Cell := ![(placedSet 4 (1, -1) envelope_2), (placedSet 3 (-1, 1) envelope_6)]
theorem common_sub_43 : commonEnvelope childrenD_43 ⊆ insert (0, 0) required_43 := by decide
theorem child_required_sub_43 : ∀ j, childrenC_43 j ⊆ insert (0, 0) required_43 := by decide
theorem child_envelope_sub_43 : ∀ j, childrenD_43 j ⊆ envelope_43 := by decide
theorem pivot_mem_43 : (0, 0) ∈ envelope_43 := by decide
theorem children_work_43 : ∀ j, Template HasSnaky 2 (childrenC_43 j) (childrenD_43 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_2 4 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_6 3 (-1, 1)).mono (by decide)
theorem row_works_43 : Template HasSnaky 3 required_43 envelope_43 := by
  refine compose HasSnaky 2 childrenC_43 childrenD_43 children_work_43 (0, 0)
    required_43 envelope_43 pivot_mem_43 child_required_sub_43 child_envelope_sub_43 ?_
  intro b hb; exact common_sub_43 (mem_commonEnvelope childrenD_43 b hb)
def required_47 : Finset Cell := ⟨(([(-1, 0), (0, -3), (0, -2), (0, -1), (1, 0), (2, -1), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_47 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, 0), (2, -1), (2, 0), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_47 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, 1) required_6), (placedSet 2 (3, -1) required_6)]
def childrenD_47 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, 1) envelope_6), (placedSet 2 (3, -1) envelope_6)]
theorem common_sub_47 : commonEnvelope childrenD_47 ⊆ insert (0, 0) required_47 := by decide
theorem child_required_sub_47 : ∀ j, childrenC_47 j ⊆ insert (0, 0) required_47 := by decide
theorem child_envelope_sub_47 : ∀ j, childrenD_47 j ⊆ envelope_47 := by decide
theorem pivot_mem_47 : (0, 0) ∈ envelope_47 := by decide
theorem children_work_47 : ∀ j, Template HasSnaky 2 (childrenC_47 j) (childrenD_47 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_6 2 (3, -1)).mono (by decide)
theorem row_works_47 : Template HasSnaky 3 required_47 envelope_47 := by
  refine compose HasSnaky 2 childrenC_47 childrenD_47 children_work_47 (0, 0)
    required_47 envelope_47 pivot_mem_47 child_required_sub_47 child_envelope_sub_47 ?_
  intro b hb; exact common_sub_47 (mem_commonEnvelope childrenD_47 b hb)
def required_48 : Finset Cell := ⟨(([(1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (3, -1), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_48 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (3, -1), (3, 0), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_48 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_6), (placedSet 2 (4, -1) required_6)]
def childrenD_48 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_6), (placedSet 2 (4, -1) envelope_6)]
theorem common_sub_48 : commonEnvelope childrenD_48 ⊆ insert (0, 0) required_48 := by decide
theorem child_required_sub_48 : ∀ j, childrenC_48 j ⊆ insert (0, 0) required_48 := by decide
theorem child_envelope_sub_48 : ∀ j, childrenD_48 j ⊆ envelope_48 := by decide
theorem pivot_mem_48 : (0, 0) ∈ envelope_48 := by decide
theorem children_work_48 : ∀ j, Template HasSnaky 2 (childrenC_48 j) (childrenD_48 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_6 2 (4, -1)).mono (by decide)
theorem row_works_48 : Template HasSnaky 3 required_48 envelope_48 := by
  refine compose HasSnaky 2 childrenC_48 childrenD_48 children_work_48 (0, 0)
    required_48 envelope_48 pivot_mem_48 child_required_sub_48 child_envelope_sub_48 ?_
  intro b hb; exact common_sub_48 (mem_commonEnvelope childrenD_48 b hb)
end SnakyConditional

end OAI
