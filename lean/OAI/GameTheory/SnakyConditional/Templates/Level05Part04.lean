import OAI.GameTheory.SnakyConditional.Templates.Level03Part02
import OAI.GameTheory.SnakyConditional.Templates.Level04Part01
import OAI.GameTheory.SnakyConditional.Templates.Level04Part02
import OAI.GameTheory.SnakyConditional.Templates.Level04Part04

namespace OAI

namespace SnakyConditional
def required_31 : Finset Cell := ⟨(([(-2, 0), (-1, 0), (0, 1), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_31 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_31 : Fin 2 → Finset Cell := ![(placedSet 0 (-3, 0) required_0), (placedSet 0 (2, 1) required_17)]
def childrenD_31 : Fin 2 → Finset Cell := ![(placedSet 0 (-3, 0) envelope_0), (placedSet 0 (2, 1) envelope_17)]
theorem common_sub_31 : commonEnvelope childrenD_31 ⊆ insert (0, 0) required_31 := by decide
theorem child_required_sub_31 : ∀ j, childrenC_31 j ⊆ insert (0, 0) required_31 := by decide
theorem child_envelope_sub_31 : ∀ j, childrenD_31 j ⊆ envelope_31 := by decide
theorem pivot_mem_31 : (0, 0) ∈ envelope_31 := by decide
theorem children_work_31 : ∀ j, Template HasSnaky 2 (childrenC_31 j) (childrenD_31 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 0 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_17 0 (2, 1)).mono (by decide)
theorem row_works_31 : Template HasSnaky 3 required_31 envelope_31 := by
  refine compose HasSnaky 2 childrenC_31 childrenD_31 children_work_31 (0, 0)
    required_31 envelope_31 pivot_mem_31 child_required_sub_31 child_envelope_sub_31 ?_
  intro b hb; exact common_sub_31 (mem_commonEnvelope childrenD_31 b hb)
def required_32 : Finset Cell := ⟨(([(1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_32 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_32 : Fin 2 → Finset Cell := ![(placedSet 4 (4, -1) required_0), (placedSet 3 (0, 1) required_6)]
def childrenD_32 : Fin 2 → Finset Cell := ![(placedSet 4 (4, -1) envelope_0), (placedSet 3 (0, 1) envelope_6)]
theorem common_sub_32 : commonEnvelope childrenD_32 ⊆ insert (0, 0) required_32 := by decide
theorem child_required_sub_32 : ∀ j, childrenC_32 j ⊆ insert (0, 0) required_32 := by decide
theorem child_envelope_sub_32 : ∀ j, childrenD_32 j ⊆ envelope_32 := by decide
theorem pivot_mem_32 : (0, 0) ∈ envelope_32 := by decide
theorem children_work_32 : ∀ j, Template HasSnaky 2 (childrenC_32 j) (childrenD_32 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 4 (4, -1)).mono (by decide)
  · exact (placed_template_map row_works_6 3 (0, 1)).mono (by decide)
theorem row_works_32 : Template HasSnaky 3 required_32 envelope_32 := by
  refine compose HasSnaky 2 childrenC_32 childrenD_32 children_work_32 (0, 0)
    required_32 envelope_32 pivot_mem_32 child_required_sub_32 child_envelope_sub_32 ?_
  intro b hb; exact common_sub_32 (mem_commonEnvelope childrenD_32 b hb)
def required_33 : Finset Cell := ⟨(([(-1, 0), (1, 0), (1, 1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_33 : Finset Cell := ⟨(([(-2, 0), (-1, 0), (0, 0), (1, 0), (1, 1), (2, 0), (2, 1), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_33 : Fin 2 → Finset Cell := ![(placedSet 0 (-2, 0) required_0), (placedSet 0 (3, 1) required_17)]
def childrenD_33 : Fin 2 → Finset Cell := ![(placedSet 0 (-2, 0) envelope_0), (placedSet 0 (3, 1) envelope_17)]
theorem common_sub_33 : commonEnvelope childrenD_33 ⊆ insert (0, 0) required_33 := by decide
theorem child_required_sub_33 : ∀ j, childrenC_33 j ⊆ insert (0, 0) required_33 := by decide
theorem child_envelope_sub_33 : ∀ j, childrenD_33 j ⊆ envelope_33 := by decide
theorem pivot_mem_33 : (0, 0) ∈ envelope_33 := by decide
theorem children_work_33 : ∀ j, Template HasSnaky 2 (childrenC_33 j) (childrenD_33 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 0 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_17 0 (3, 1)).mono (by decide)
theorem row_works_33 : Template HasSnaky 3 required_33 envelope_33 := by
  refine compose HasSnaky 2 childrenC_33 childrenD_33 children_work_33 (0, 0)
    required_33 envelope_33 pivot_mem_33 child_required_sub_33 child_envelope_sub_33 ?_
  intro b hb; exact common_sub_33 (mem_commonEnvelope childrenD_33 b hb)
def required_34 : Finset Cell := ⟨(([(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_34 : Finset Cell := ⟨(([(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_34 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_6), (placedSet 6 (1, 0) required_1)]
def childrenD_34 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_6), (placedSet 6 (1, 0) envelope_1)]
theorem common_sub_34 : commonEnvelope childrenD_34 ⊆ insert (0, 0) required_34 := by decide
theorem child_required_sub_34 : ∀ j, childrenC_34 j ⊆ insert (0, 0) required_34 := by decide
theorem child_envelope_sub_34 : ∀ j, childrenD_34 j ⊆ envelope_34 := by decide
theorem pivot_mem_34 : (0, 0) ∈ envelope_34 := by decide
theorem children_work_34 : ∀ j, Template HasSnaky 2 (childrenC_34 j) (childrenD_34 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_1 6 (1, 0)).mono (by decide)
theorem row_works_34 : Template HasSnaky 3 required_34 envelope_34 := by
  refine compose HasSnaky 2 childrenC_34 childrenD_34 children_work_34 (0, 0)
    required_34 envelope_34 pivot_mem_34 child_required_sub_34 child_envelope_sub_34 ?_
  intro b hb; exact common_sub_34 (mem_commonEnvelope childrenD_34 b hb)
def required_35 : Finset Cell := ⟨(([(-1, 0), (1, 0), (1, 1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_35 : Finset Cell := ⟨(([(-2, 0), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_35 : Fin 2 → Finset Cell := ![(placedSet 0 (-2, 0) required_0), (placedSet 0 (3, 1) required_14)]
def childrenD_35 : Fin 2 → Finset Cell := ![(placedSet 0 (-2, 0) envelope_0), (placedSet 0 (3, 1) envelope_14)]
theorem common_sub_35 : commonEnvelope childrenD_35 ⊆ insert (0, 0) required_35 := by decide
theorem child_required_sub_35 : ∀ j, childrenC_35 j ⊆ insert (0, 0) required_35 := by decide
theorem child_envelope_sub_35 : ∀ j, childrenD_35 j ⊆ envelope_35 := by decide
theorem pivot_mem_35 : (0, 0) ∈ envelope_35 := by decide
theorem children_work_35 : ∀ j, Template HasSnaky 2 (childrenC_35 j) (childrenD_35 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 0 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_14 0 (3, 1)).mono (by decide)
theorem row_works_35 : Template HasSnaky 3 required_35 envelope_35 := by
  refine compose HasSnaky 2 childrenC_35 childrenD_35 children_work_35 (0, 0)
    required_35 envelope_35 pivot_mem_35 child_required_sub_35 child_envelope_sub_35 ?_
  intro b hb; exact common_sub_35 (mem_commonEnvelope childrenD_35 b hb)
end SnakyConditional

end OAI
