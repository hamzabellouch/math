import OAI.GameTheory.SnakyConditional.Templates.Level03Part02
import OAI.GameTheory.SnakyConditional.Templates.Level04Part01
import OAI.GameTheory.SnakyConditional.Templates.Level04Part02

namespace OAI

namespace SnakyConditional
def required_26 : Finset Cell := ⟨(([(-2, 0), (-2, 1), (-1, 0), (-1, 1), (1, 0), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_26 : Finset Cell := ⟨(([(-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (1, 0), (1, 1), (2, 0), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_26 : Fin 2 → Finset Cell := ![(placedSet 4 (2, 0) required_0), (placedSet 0 (2, 1) required_6)]
def childrenD_26 : Fin 2 → Finset Cell := ![(placedSet 4 (2, 0) envelope_0), (placedSet 0 (2, 1) envelope_6)]
theorem common_sub_26 : commonEnvelope childrenD_26 ⊆ insert (0, 0) required_26 := by decide
theorem child_required_sub_26 : ∀ j, childrenC_26 j ⊆ insert (0, 0) required_26 := by decide
theorem child_envelope_sub_26 : ∀ j, childrenD_26 j ⊆ envelope_26 := by decide
theorem pivot_mem_26 : (0, 0) ∈ envelope_26 := by decide
theorem children_work_26 : ∀ j, Template HasSnaky 2 (childrenC_26 j) (childrenD_26 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 4 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_6 0 (2, 1)).mono (by decide)
theorem row_works_26 : Template HasSnaky 3 required_26 envelope_26 := by
  refine compose HasSnaky 2 childrenC_26 childrenD_26 children_work_26 (0, 0)
    required_26 envelope_26 pivot_mem_26 child_required_sub_26 child_envelope_sub_26 ?_
  intro b hb; exact common_sub_26 (mem_commonEnvelope childrenD_26 b hb)
def required_27 : Finset Cell := ⟨(([(-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_27 : Finset Cell := ⟨(([(-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, 0), (0, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_27 : Fin 2 → Finset Cell := ![(placedSet 6 (1, 0) required_0), (placedSet 4 (-4, 1) required_6)]
def childrenD_27 : Fin 2 → Finset Cell := ![(placedSet 6 (1, 0) envelope_0), (placedSet 4 (-4, 1) envelope_6)]
theorem common_sub_27 : commonEnvelope childrenD_27 ⊆ insert (0, 0) required_27 := by decide
theorem child_required_sub_27 : ∀ j, childrenC_27 j ⊆ insert (0, 0) required_27 := by decide
theorem child_envelope_sub_27 : ∀ j, childrenD_27 j ⊆ envelope_27 := by decide
theorem pivot_mem_27 : (0, 0) ∈ envelope_27 := by decide
theorem children_work_27 : ∀ j, Template HasSnaky 2 (childrenC_27 j) (childrenD_27 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 6 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_6 4 (-4, 1)).mono (by decide)
theorem row_works_27 : Template HasSnaky 3 required_27 envelope_27 := by
  refine compose HasSnaky 2 childrenC_27 childrenD_27 children_work_27 (0, 0)
    required_27 envelope_27 pivot_mem_27 child_required_sub_27 child_envelope_sub_27 ?_
  intro b hb; exact common_sub_27 (mem_commonEnvelope childrenD_27 b hb)
def required_28 : Finset Cell := ⟨(([(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_28 : Finset Cell := ⟨(([(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_28 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_6), (placedSet 6 (2, 0) required_0)]
def childrenD_28 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_6), (placedSet 6 (2, 0) envelope_0)]
theorem common_sub_28 : commonEnvelope childrenD_28 ⊆ insert (0, 0) required_28 := by decide
theorem child_required_sub_28 : ∀ j, childrenC_28 j ⊆ insert (0, 0) required_28 := by decide
theorem child_envelope_sub_28 : ∀ j, childrenD_28 j ⊆ envelope_28 := by decide
theorem pivot_mem_28 : (0, 0) ∈ envelope_28 := by decide
theorem children_work_28 : ∀ j, Template HasSnaky 2 (childrenC_28 j) (childrenD_28 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_0 6 (2, 0)).mono (by decide)
theorem row_works_28 : Template HasSnaky 3 required_28 envelope_28 := by
  refine compose HasSnaky 2 childrenC_28 childrenD_28 children_work_28 (0, 0)
    required_28 envelope_28 pivot_mem_28 child_required_sub_28 child_envelope_sub_28 ?_
  intro b hb; exact common_sub_28 (mem_commonEnvelope childrenD_28 b hb)
def required_29 : Finset Cell := ⟨(([(1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_29 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_29 : Fin 2 → Finset Cell := ![(placedSet 4 (3, -1) required_1), (placedSet 3 (0, 1) required_6)]
def childrenD_29 : Fin 2 → Finset Cell := ![(placedSet 4 (3, -1) envelope_1), (placedSet 3 (0, 1) envelope_6)]
theorem common_sub_29 : commonEnvelope childrenD_29 ⊆ insert (0, 0) required_29 := by decide
theorem child_required_sub_29 : ∀ j, childrenC_29 j ⊆ insert (0, 0) required_29 := by decide
theorem child_envelope_sub_29 : ∀ j, childrenD_29 j ⊆ envelope_29 := by decide
theorem pivot_mem_29 : (0, 0) ∈ envelope_29 := by decide
theorem children_work_29 : ∀ j, Template HasSnaky 2 (childrenC_29 j) (childrenD_29 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_1 4 (3, -1)).mono (by decide)
  · exact (placed_template_map row_works_6 3 (0, 1)).mono (by decide)
theorem row_works_29 : Template HasSnaky 3 required_29 envelope_29 := by
  refine compose HasSnaky 2 childrenC_29 childrenD_29 children_work_29 (0, 0)
    required_29 envelope_29 pivot_mem_29 child_required_sub_29 child_envelope_sub_29 ?_
  intro b hb; exact common_sub_29 (mem_commonEnvelope childrenD_29 b hb)
def required_30 : Finset Cell := ⟨(([(-2, -1), (-1, -1), (0, -1), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_30 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_30 : Fin 2 → Finset Cell := ![(placedSet 0 (-3, -1) required_0), (placedSet 0 (2, 0) required_14)]
def childrenD_30 : Fin 2 → Finset Cell := ![(placedSet 0 (-3, -1) envelope_0), (placedSet 0 (2, 0) envelope_14)]
theorem common_sub_30 : commonEnvelope childrenD_30 ⊆ insert (0, 0) required_30 := by decide
theorem child_required_sub_30 : ∀ j, childrenC_30 j ⊆ insert (0, 0) required_30 := by decide
theorem child_envelope_sub_30 : ∀ j, childrenD_30 j ⊆ envelope_30 := by decide
theorem pivot_mem_30 : (0, 0) ∈ envelope_30 := by decide
theorem children_work_30 : ∀ j, Template HasSnaky 2 (childrenC_30 j) (childrenD_30 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 0 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_14 0 (2, 0)).mono (by decide)
theorem row_works_30 : Template HasSnaky 3 required_30 envelope_30 := by
  refine compose HasSnaky 2 childrenC_30 childrenD_30 children_work_30 (0, 0)
    required_30 envelope_30 pivot_mem_30 child_required_sub_30 child_envelope_sub_30 ?_
  intro b hb; exact common_sub_30 (mem_commonEnvelope childrenD_30 b hb)
end SnakyConditional

end OAI
