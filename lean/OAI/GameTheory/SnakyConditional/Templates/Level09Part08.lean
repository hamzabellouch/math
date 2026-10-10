import OAI.GameTheory.SnakyConditional.Templates.Level08Part01
import OAI.GameTheory.SnakyConditional.Templates.Level08Part02
import OAI.GameTheory.SnakyConditional.Templates.Level08Part03
import OAI.GameTheory.SnakyConditional.Templates.Level08Part07

namespace OAI

namespace SnakyConditional
def required_302 : Finset Cell := ⟨(([(-2, -2), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -2), (2, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_302 : Finset Cell := ⟨(([(-2, -2), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -2), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_302 : Fin 2 → Finset Cell := ![(placedSet 0 (1, -1) required_125), (placedSet 4 (-1, 2) required_162)]
def childrenD_302 : Fin 2 → Finset Cell := ![(placedSet 0 (1, -1) envelope_125), (placedSet 4 (-1, 2) envelope_162)]
theorem common_sub_302 : commonEnvelope childrenD_302 ⊆ insert (0, 0) required_302 := by decide
theorem child_required_sub_302 : ∀ j, childrenC_302 j ⊆ insert (0, 0) required_302 := by decide
theorem child_envelope_sub_302 : ∀ j, childrenD_302 j ⊆ envelope_302 := by decide
theorem pivot_mem_302 : (0, 0) ∈ envelope_302 := by decide
theorem children_work_302 : ∀ j, Template HasSnaky 6 (childrenC_302 j) (childrenD_302 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_125 0 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_162 4 (-1, 2)).mono (by decide)
theorem row_works_302 : Template HasSnaky 7 required_302 envelope_302 := by
  refine compose HasSnaky 6 childrenC_302 childrenD_302 children_work_302 (0, 0)
    required_302 envelope_302 pivot_mem_302 child_required_sub_302 child_envelope_sub_302 ?_
  intro b hb; exact common_sub_302 (mem_commonEnvelope childrenD_302 b hb)
def required_313 : Finset Cell := ⟨(([(-2, -1), (-1, -1), (0, -3), (0, -2), (0, -1), (1, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_313 : Finset Cell := ⟨(([(-2, -1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (3, -2), (3, -1), (4, -2), (4, -1), (5, -2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_313 : Fin 2 → Finset Cell := ![(placedSet 4 (0, 1) required_162), (placedSet 5 (2, -1) required_148)]
def childrenD_313 : Fin 2 → Finset Cell := ![(placedSet 4 (0, 1) envelope_162), (placedSet 5 (2, -1) envelope_148)]
theorem common_sub_313 : commonEnvelope childrenD_313 ⊆ insert (0, 0) required_313 := by decide
theorem child_required_sub_313 : ∀ j, childrenC_313 j ⊆ insert (0, 0) required_313 := by decide
theorem child_envelope_sub_313 : ∀ j, childrenD_313 j ⊆ envelope_313 := by decide
theorem pivot_mem_313 : (0, 0) ∈ envelope_313 := by decide
theorem children_work_313 : ∀ j, Template HasSnaky 6 (childrenC_313 j) (childrenD_313 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_162 4 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_148 5 (2, -1)).mono (by decide)
theorem row_works_313 : Template HasSnaky 7 required_313 envelope_313 := by
  refine compose HasSnaky 6 childrenC_313 childrenD_313 children_work_313 (0, 0)
    required_313 envelope_313 pivot_mem_313 child_required_sub_313 child_envelope_sub_313 ?_
  intro b hb; exact common_sub_313 (mem_commonEnvelope childrenD_313 b hb)
def required_480 : Finset Cell := ⟨(([(-1, -3), (0, -3), (0, -2), (0, -1), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_480 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_480 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_108), (placedSet 1 (1, 0) required_4)]
def childrenD_480 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_108), (placedSet 1 (1, 0) envelope_4)]
theorem common_sub_480 : commonEnvelope childrenD_480 ⊆ insert (0, 0) required_480 := by decide
theorem child_required_sub_480 : ∀ j, childrenC_480 j ⊆ insert (0, 0) required_480 := by decide
theorem child_envelope_sub_480 : ∀ j, childrenD_480 j ⊆ envelope_480 := by decide
theorem pivot_mem_480 : (0, 0) ∈ envelope_480 := by decide
theorem children_work_480 : ∀ j, Template HasSnaky 6 (childrenC_480 j) (childrenD_480 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_108 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_4 1 (1, 0)).mono (by decide)
theorem row_works_480 : Template HasSnaky 7 required_480 envelope_480 := by
  refine compose HasSnaky 6 childrenC_480 childrenD_480 children_work_480 (0, 0)
    required_480 envelope_480 pivot_mem_480 child_required_sub_480 child_envelope_sub_480 ?_
  intro b hb; exact common_sub_480 (mem_commonEnvelope childrenD_480 b hb)
def required_482 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (-1, -1), (-1, 0), (1, -3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_482 : Finset Cell := ⟨(([(-3, -1), (-2, -2), (-2, -1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_482 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_6), (placedSet 2 (0, -1) required_218)]
def childrenD_482 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_6), (placedSet 2 (0, -1) envelope_218)]
theorem common_sub_482 : commonEnvelope childrenD_482 ⊆ insert (0, 0) required_482 := by decide
theorem child_required_sub_482 : ∀ j, childrenC_482 j ⊆ insert (0, 0) required_482 := by decide
theorem child_envelope_sub_482 : ∀ j, childrenD_482 j ⊆ envelope_482 := by decide
theorem pivot_mem_482 : (0, 0) ∈ envelope_482 := by decide
theorem children_work_482 : ∀ j, Template HasSnaky 6 (childrenC_482 j) (childrenD_482 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_218 2 (0, -1)).mono (by decide)
theorem row_works_482 : Template HasSnaky 7 required_482 envelope_482 := by
  refine compose HasSnaky 6 childrenC_482 childrenD_482 children_work_482 (0, 0)
    required_482 envelope_482 pivot_mem_482 child_required_sub_482 child_envelope_sub_482 ?_
  intro b hb; exact common_sub_482 (mem_commonEnvelope childrenD_482 b hb)
end SnakyConditional

end OAI
