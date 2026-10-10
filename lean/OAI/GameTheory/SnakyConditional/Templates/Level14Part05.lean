import OAI.GameTheory.SnakyConditional.Templates.Level12Part07
import OAI.GameTheory.SnakyConditional.Templates.Level13Part01
import OAI.GameTheory.SnakyConditional.Templates.Level13Part03
import OAI.GameTheory.SnakyConditional.Templates.Level13Part04
import OAI.GameTheory.SnakyConditional.Templates.Level13Part05

namespace OAI

namespace SnakyConditional
def required_425 : Finset Cell := ⟨(([(-1, -2), (-1, 0), (0, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_425 : Finset Cell := ⟨(([(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_425 : Fin 5 → Finset Cell := ![(placedSet 0 (1, 0) required_386), (placedSet 1 (0, 1) required_226), (placedSet 4 (-2, 0) required_378), (placedSet 0 (1, 0) required_378), (placedSet 4 (-2, 0) required_386)]
def childrenD_425 : Fin 5 → Finset Cell := ![(placedSet 0 (1, 0) envelope_386), (placedSet 1 (0, 1) envelope_226), (placedSet 4 (-2, 0) envelope_378), (placedSet 0 (1, 0) envelope_378), (placedSet 4 (-2, 0) envelope_386)]
theorem common_sub_425 : commonEnvelope childrenD_425 ⊆ insert (0, 0) required_425 := by decide
theorem child_required_sub_425 : ∀ j, childrenC_425 j ⊆ insert (0, 0) required_425 := by decide
theorem child_envelope_sub_425 : ∀ j, childrenD_425 j ⊆ envelope_425 := by decide
theorem pivot_mem_425 : (0, 0) ∈ envelope_425 := by decide
theorem children_work_425 : ∀ j, Template HasSnaky 11 (childrenC_425 j) (childrenD_425 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_386 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_226 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_378 4 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_378 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_386 4 (-2, 0)).mono (by decide)
theorem row_works_425 : Template HasSnaky 12 required_425 envelope_425 := by
  refine compose HasSnaky 11 childrenC_425 childrenD_425 children_work_425 (0, 0)
    required_425 envelope_425 pivot_mem_425 child_required_sub_425 child_envelope_sub_425 ?_
  intro b hb; exact common_sub_425 (mem_commonEnvelope childrenD_425 b hb)
def required_426 : Finset Cell := ⟨(([(-1, -2), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_426 : Finset Cell := ⟨(([(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (4, -1), (4, 0), (4, 1), (4, 2), (5, -1), (5, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_426 : Fin 6 → Finset Cell := ![(placedSet 6 (0, -3) required_300), (placedSet 1 (0, 1) required_252), (placedSet 0 (-1, 0) required_397), (placedSet 1 (0, -3) required_291), (placedSet 0 (0, 1) required_328), (placedSet 1 (-1, 1) required_319)]
def childrenD_426 : Fin 6 → Finset Cell := ![(placedSet 6 (0, -3) envelope_300), (placedSet 1 (0, 1) envelope_252), (placedSet 0 (-1, 0) envelope_397), (placedSet 1 (0, -3) envelope_291), (placedSet 0 (0, 1) envelope_328), (placedSet 1 (-1, 1) envelope_319)]
theorem common_sub_426 : commonEnvelope childrenD_426 ⊆ insert (0, 0) required_426 := by decide
theorem child_required_sub_426 : ∀ j, childrenC_426 j ⊆ insert (0, 0) required_426 := by decide
theorem child_envelope_sub_426 : ∀ j, childrenD_426 j ⊆ envelope_426 := by decide
theorem pivot_mem_426 : (0, 0) ∈ envelope_426 := by decide
theorem children_work_426 : ∀ j, Template HasSnaky 11 (childrenC_426 j) (childrenD_426 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_300 6 (0, -3)).mono (by decide)
  · exact (placed_template_map row_works_252 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_397 0 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_291 1 (0, -3)).mono (by decide)
  · exact (placed_template_map row_works_328 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_319 1 (-1, 1)).mono (by decide)
theorem row_works_426 : Template HasSnaky 12 required_426 envelope_426 := by
  refine compose HasSnaky 11 childrenC_426 childrenD_426 children_work_426 (0, 0)
    required_426 envelope_426 pivot_mem_426 child_required_sub_426 child_envelope_sub_426 ?_
  intro b hb; exact common_sub_426 (mem_commonEnvelope childrenD_426 b hb)
def required_453 : Finset Cell := ⟨(([(-1, -2), (-1, 0), (0, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_453 : Finset Cell := ⟨(([(-6, -1), (-5, -1), (-5, 0), (-5, 1), (-4, -3), (-4, -1), (-4, 0), (-4, 1), (-3, -3), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_453 : Fin 5 → Finset Cell := ![(placedSet 0 (0, -1) required_359), (placedSet 7 (-1, -3) required_226), (placedSet 4 (-2, 0) required_386), (placedSet 1 (1, 0) required_389), (placedSet 4 (-1, -1) required_414)]
def childrenD_453 : Fin 5 → Finset Cell := ![(placedSet 0 (0, -1) envelope_359), (placedSet 7 (-1, -3) envelope_226), (placedSet 4 (-2, 0) envelope_386), (placedSet 1 (1, 0) envelope_389), (placedSet 4 (-1, -1) envelope_414)]
theorem common_sub_453 : commonEnvelope childrenD_453 ⊆ insert (0, 0) required_453 := by decide
theorem child_required_sub_453 : ∀ j, childrenC_453 j ⊆ insert (0, 0) required_453 := by decide
theorem child_envelope_sub_453 : ∀ j, childrenD_453 j ⊆ envelope_453 := by decide
theorem pivot_mem_453 : (0, 0) ∈ envelope_453 := by decide
theorem children_work_453 : ∀ j, Template HasSnaky 11 (childrenC_453 j) (childrenD_453 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_359 0 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_226 7 (-1, -3)).mono (by decide)
  · exact (placed_template_map row_works_386 4 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_389 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_414 4 (-1, -1)).mono (by decide)
theorem row_works_453 : Template HasSnaky 12 required_453 envelope_453 := by
  refine compose HasSnaky 11 childrenC_453 childrenD_453 children_work_453 (0, 0)
    required_453 envelope_453 pivot_mem_453 child_required_sub_453 child_envelope_sub_453 ?_
  intro b hb; exact common_sub_453 (mem_commonEnvelope childrenD_453 b hb)
def required_456 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_456 : Finset Cell := ⟨(([(-4, 1), (-4, 3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_456 : Fin 4 → Finset Cell := ![(placedSet 4 (0, -1) required_308), (placedSet 2 (-3, 1) required_64), (placedSet 1 (1, -1) required_63), (placedSet 0 (1, 0) required_55)]
def childrenD_456 : Fin 4 → Finset Cell := ![(placedSet 4 (0, -1) envelope_308), (placedSet 2 (-3, 1) envelope_64), (placedSet 1 (1, -1) envelope_63), (placedSet 0 (1, 0) envelope_55)]
theorem common_sub_456 : commonEnvelope childrenD_456 ⊆ insert (0, 0) required_456 := by decide
theorem child_required_sub_456 : ∀ j, childrenC_456 j ⊆ insert (0, 0) required_456 := by decide
theorem child_envelope_sub_456 : ∀ j, childrenD_456 j ⊆ envelope_456 := by decide
theorem pivot_mem_456 : (0, 0) ∈ envelope_456 := by decide
theorem children_work_456 : ∀ j, Template HasSnaky 11 (childrenC_456 j) (childrenD_456 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_308 4 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_64 2 (-3, 1)).mono (by decide)
  · exact (placed_template_map row_works_63 1 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_55 0 (1, 0)).mono (by decide)
theorem row_works_456 : Template HasSnaky 12 required_456 envelope_456 := by
  refine compose HasSnaky 11 childrenC_456 childrenD_456 children_work_456 (0, 0)
    required_456 envelope_456 pivot_mem_456 child_required_sub_456 child_envelope_sub_456 ?_
  intro b hb; exact common_sub_456 (mem_commonEnvelope childrenD_456 b hb)
end SnakyConditional

end OAI
