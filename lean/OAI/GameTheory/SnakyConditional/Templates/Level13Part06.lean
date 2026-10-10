import OAI.GameTheory.SnakyConditional.Templates.Level11Part08
import OAI.GameTheory.SnakyConditional.Templates.Level12Part01
import OAI.GameTheory.SnakyConditional.Templates.Level12Part02
import OAI.GameTheory.SnakyConditional.Templates.Level12Part03
import OAI.GameTheory.SnakyConditional.Templates.Level12Part08

namespace OAI

namespace SnakyConditional
def required_494 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0), (-1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_494 : Finset Cell := ⟨(([(-6, 2), (-5, 2), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_494 : Fin 3 → Finset Cell := ![(placedSet 4 (0, 1) required_297), (placedSet 4 (-3, 1) required_268), (placedSet 5 (1, 0) required_162)]
def childrenD_494 : Fin 3 → Finset Cell := ![(placedSet 4 (0, 1) envelope_297), (placedSet 4 (-3, 1) envelope_268), (placedSet 5 (1, 0) envelope_162)]
theorem common_sub_494 : commonEnvelope childrenD_494 ⊆ insert (0, 0) required_494 := by decide
theorem child_required_sub_494 : ∀ j, childrenC_494 j ⊆ insert (0, 0) required_494 := by decide
theorem child_envelope_sub_494 : ∀ j, childrenD_494 j ⊆ envelope_494 := by decide
theorem pivot_mem_494 : (0, 0) ∈ envelope_494 := by decide
theorem children_work_494 : ∀ j, Template HasSnaky 10 (childrenC_494 j) (childrenD_494 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_297 4 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_268 4 (-3, 1)).mono (by decide)
  · exact (placed_template_map row_works_162 5 (1, 0)).mono (by decide)
theorem row_works_494 : Template HasSnaky 11 required_494 envelope_494 := by
  refine compose HasSnaky 10 childrenC_494 childrenD_494 children_work_494 (0, 0)
    required_494 envelope_494 pivot_mem_494 child_required_sub_494 child_envelope_sub_494 ?_
  intro b hb; exact common_sub_494 (mem_commonEnvelope childrenD_494 b hb)
def required_505 : Finset Cell := ⟨(([(0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_505 : Finset Cell := ⟨(([(-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -3), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_505 : Fin 4 → Finset Cell := ![(placedSet 1 (0, 1) required_173), (placedSet 0 (1, 0) required_499), (placedSet 1 (0, 1) required_183), (placedSet 1 (0, 1) required_282)]
def childrenD_505 : Fin 4 → Finset Cell := ![(placedSet 1 (0, 1) envelope_173), (placedSet 0 (1, 0) envelope_499), (placedSet 1 (0, 1) envelope_183), (placedSet 1 (0, 1) envelope_282)]
theorem common_sub_505 : commonEnvelope childrenD_505 ⊆ insert (0, 0) required_505 := by decide
theorem child_required_sub_505 : ∀ j, childrenC_505 j ⊆ insert (0, 0) required_505 := by decide
theorem child_envelope_sub_505 : ∀ j, childrenD_505 j ⊆ envelope_505 := by decide
theorem pivot_mem_505 : (0, 0) ∈ envelope_505 := by decide
theorem children_work_505 : ∀ j, Template HasSnaky 10 (childrenC_505 j) (childrenD_505 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_173 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_499 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_183 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_282 1 (0, 1)).mono (by decide)
theorem row_works_505 : Template HasSnaky 11 required_505 envelope_505 := by
  refine compose HasSnaky 10 childrenC_505 childrenD_505 children_work_505 (0, 0)
    required_505 envelope_505 pivot_mem_505 child_required_sub_505 child_envelope_sub_505 ?_
  intro b hb; exact common_sub_505 (mem_commonEnvelope childrenD_505 b hb)
def required_506 : Finset Cell := ⟨(([(-2, -2), (-2, 0), (-1, -3), (-1, -2), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_506 : Finset Cell := ⟨(([(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 1), (4, -2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_506 : Fin 4 → Finset Cell := ![(placedSet 0 (0, 1) required_99), (placedSet 7 (-3, 0) required_200), (placedSet 5 (1, 0) required_318), (placedSet 0 (1, 0) required_173)]
def childrenD_506 : Fin 4 → Finset Cell := ![(placedSet 0 (0, 1) envelope_99), (placedSet 7 (-3, 0) envelope_200), (placedSet 5 (1, 0) envelope_318), (placedSet 0 (1, 0) envelope_173)]
theorem common_sub_506 : commonEnvelope childrenD_506 ⊆ insert (0, 0) required_506 := by decide
theorem child_required_sub_506 : ∀ j, childrenC_506 j ⊆ insert (0, 0) required_506 := by decide
theorem child_envelope_sub_506 : ∀ j, childrenD_506 j ⊆ envelope_506 := by decide
theorem pivot_mem_506 : (0, 0) ∈ envelope_506 := by decide
theorem children_work_506 : ∀ j, Template HasSnaky 10 (childrenC_506 j) (childrenD_506 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_99 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_200 7 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_318 5 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_173 0 (1, 0)).mono (by decide)
theorem row_works_506 : Template HasSnaky 11 required_506 envelope_506 := by
  refine compose HasSnaky 10 childrenC_506 childrenD_506 children_work_506 (0, 0)
    required_506 envelope_506 pivot_mem_506 child_required_sub_506 child_envelope_sub_506 ?_
  intro b hb; exact common_sub_506 (mem_commonEnvelope childrenD_506 b hb)
def required_523 : Finset Cell := ⟨(([(-3, 4), (-2, 0), (-2, 1), (-2, 2), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_523 : Finset Cell := ⟨(([(-7, 1), (-7, 3), (-6, 1), (-6, 2), (-6, 3), (-5, 1), (-5, 2), (-5, 3), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 5), (-4, 6), (-4, 7), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, 0), (-2, 1), (-2, 2), (-2, 5), (-2, 6), (-2, 7), (-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 1), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_523 : Fin 4 → Finset Cell := ![(placedSet 1 (1, 0) required_303), (placedSet 4 (-3, 1) required_25), (placedSet 2 (1, 0) required_107), (placedSet 4 (-3, 2) required_511)]
def childrenD_523 : Fin 4 → Finset Cell := ![(placedSet 1 (1, 0) envelope_303), (placedSet 4 (-3, 1) envelope_25), (placedSet 2 (1, 0) envelope_107), (placedSet 4 (-3, 2) envelope_511)]
theorem common_sub_523 : commonEnvelope childrenD_523 ⊆ insert (0, 0) required_523 := by decide
theorem child_required_sub_523 : ∀ j, childrenC_523 j ⊆ insert (0, 0) required_523 := by decide
theorem child_envelope_sub_523 : ∀ j, childrenD_523 j ⊆ envelope_523 := by decide
theorem pivot_mem_523 : (0, 0) ∈ envelope_523 := by decide
theorem children_work_523 : ∀ j, Template HasSnaky 10 (childrenC_523 j) (childrenD_523 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_303 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_25 4 (-3, 1)).mono (by decide)
  · exact (placed_template_map row_works_107 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_511 4 (-3, 2)).mono (by decide)
theorem row_works_523 : Template HasSnaky 11 required_523 envelope_523 := by
  refine compose HasSnaky 10 childrenC_523 childrenD_523 children_work_523 (0, 0)
    required_523 envelope_523 pivot_mem_523 child_required_sub_523 child_envelope_sub_523 ?_
  intro b hb; exact common_sub_523 (mem_commonEnvelope childrenD_523 b hb)
def required_525 : Finset Cell := ⟨(([(-2, 0), (-2, 1), (-2, 2), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_525 : Finset Cell := ⟨(([(-7, 1), (-7, 3), (-6, 1), (-6, 2), (-6, 3), (-5, 1), (-5, 2), (-5, 3), (-4, 1), (-4, 2), (-4, 3), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 1), (3, 2), (3, 3), (4, 1), (4, 2), (4, 3), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_525 : Fin 4 → Finset Cell := ![(placedSet 1 (1, 0) required_303), (placedSet 4 (-3, 1) required_25), (placedSet 0 (0, 2) required_430), (placedSet 2 (1, 0) required_107)]
def childrenD_525 : Fin 4 → Finset Cell := ![(placedSet 1 (1, 0) envelope_303), (placedSet 4 (-3, 1) envelope_25), (placedSet 0 (0, 2) envelope_430), (placedSet 2 (1, 0) envelope_107)]
theorem common_sub_525 : commonEnvelope childrenD_525 ⊆ insert (0, 0) required_525 := by decide
theorem child_required_sub_525 : ∀ j, childrenC_525 j ⊆ insert (0, 0) required_525 := by decide
theorem child_envelope_sub_525 : ∀ j, childrenD_525 j ⊆ envelope_525 := by decide
theorem pivot_mem_525 : (0, 0) ∈ envelope_525 := by decide
theorem children_work_525 : ∀ j, Template HasSnaky 10 (childrenC_525 j) (childrenD_525 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_303 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_25 4 (-3, 1)).mono (by decide)
  · exact (placed_template_map row_works_430 0 (0, 2)).mono (by decide)
  · exact (placed_template_map row_works_107 2 (1, 0)).mono (by decide)
theorem row_works_525 : Template HasSnaky 11 required_525 envelope_525 := by
  refine compose HasSnaky 10 childrenC_525 childrenD_525 children_work_525 (0, 0)
    required_525 envelope_525 pivot_mem_525 child_required_sub_525 child_envelope_sub_525 ?_
  intro b hb; exact common_sub_525 (mem_commonEnvelope childrenD_525 b hb)
end SnakyConditional

end OAI
