import OAI.GameTheory.SnakyConditional.Templates.Level12Part07
import OAI.GameTheory.SnakyConditional.Templates.Level13Part05
import OAI.GameTheory.SnakyConditional.Templates.Level13Part06

namespace OAI

namespace SnakyConditional
def required_507 : Finset Cell := ⟨(([(-2, -3), (-2, -2), (-1, 0), (-1, 1), (0, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_507 : Finset Cell := ⟨(([(-4, 0), (-3, -1), (-3, 0), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1), (4, 2), (5, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_507 : Fin 3 → Finset Cell := ![(placedSet 0 (-2, 0) required_151), (placedSet 3 (0, -1) required_33), (placedSet 0 (1, 0) required_481)]
def childrenD_507 : Fin 3 → Finset Cell := ![(placedSet 0 (-2, 0) envelope_151), (placedSet 3 (0, -1) envelope_33), (placedSet 0 (1, 0) envelope_481)]
theorem common_sub_507 : commonEnvelope childrenD_507 ⊆ insert (0, 0) required_507 := by decide
theorem child_required_sub_507 : ∀ j, childrenC_507 j ⊆ insert (0, 0) required_507 := by decide
theorem child_envelope_sub_507 : ∀ j, childrenD_507 j ⊆ envelope_507 := by decide
theorem pivot_mem_507 : (0, 0) ∈ envelope_507 := by decide
theorem children_work_507 : ∀ j, Template HasSnaky 11 (childrenC_507 j) (childrenD_507 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_151 0 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_33 3 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_481 0 (1, 0)).mono (by decide)
theorem row_works_507 : Template HasSnaky 12 required_507 envelope_507 := by
  refine compose HasSnaky 11 childrenC_507 childrenD_507 children_work_507 (0, 0)
    required_507 envelope_507 pivot_mem_507 child_required_sub_507 child_envelope_sub_507 ?_
  intro b hb; exact common_sub_507 (mem_commonEnvelope childrenD_507 b hb)
def required_516 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (-1, 0), (0, -3), (0, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_516 : Finset Cell := ⟨(([(-6, -2), (-5, -2), (-5, -1), (-5, 1), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_516 : Fin 4 → Finset Cell := ![(placedSet 0 (0, -1) required_329), (placedSet 4 (-2, 0) required_244), (placedSet 1 (0, 1) required_10), (placedSet 4 (-2, 0) required_506)]
def childrenD_516 : Fin 4 → Finset Cell := ![(placedSet 0 (0, -1) envelope_329), (placedSet 4 (-2, 0) envelope_244), (placedSet 1 (0, 1) envelope_10), (placedSet 4 (-2, 0) envelope_506)]
theorem common_sub_516 : commonEnvelope childrenD_516 ⊆ insert (0, 0) required_516 := by decide
theorem child_required_sub_516 : ∀ j, childrenC_516 j ⊆ insert (0, 0) required_516 := by decide
theorem child_envelope_sub_516 : ∀ j, childrenD_516 j ⊆ envelope_516 := by decide
theorem pivot_mem_516 : (0, 0) ∈ envelope_516 := by decide
theorem children_work_516 : ∀ j, Template HasSnaky 11 (childrenC_516 j) (childrenD_516 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_329 0 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_244 4 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_10 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_506 4 (-2, 0)).mono (by decide)
theorem row_works_516 : Template HasSnaky 12 required_516 envelope_516 := by
  refine compose HasSnaky 11 childrenC_516 childrenD_516 children_work_516 (0, 0)
    required_516 envelope_516 pivot_mem_516 child_required_sub_516 child_envelope_sub_516 ?_
  intro b hb; exact common_sub_516 (mem_commonEnvelope childrenD_516 b hb)
def required_519 : Finset Cell := ⟨(([(-2, 0), (-1, -3), (-1, -2), (-1, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_519 : Finset Cell := ⟨(([(-6, -1), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (4, -2), (4, -1), (4, 0), (5, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_519 : Fin 4 → Finset Cell := ![(placedSet 0 (0, -1) required_498), (placedSet 4 (-1, 0) required_311), (placedSet 1 (0, 1) required_38), (placedSet 0 (-1, 0) required_408)]
def childrenD_519 : Fin 4 → Finset Cell := ![(placedSet 0 (0, -1) envelope_498), (placedSet 4 (-1, 0) envelope_311), (placedSet 1 (0, 1) envelope_38), (placedSet 0 (-1, 0) envelope_408)]
theorem common_sub_519 : commonEnvelope childrenD_519 ⊆ insert (0, 0) required_519 := by decide
theorem child_required_sub_519 : ∀ j, childrenC_519 j ⊆ insert (0, 0) required_519 := by decide
theorem child_envelope_sub_519 : ∀ j, childrenD_519 j ⊆ envelope_519 := by decide
theorem pivot_mem_519 : (0, 0) ∈ envelope_519 := by decide
theorem children_work_519 : ∀ j, Template HasSnaky 11 (childrenC_519 j) (childrenD_519 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_498 0 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_311 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_38 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_408 0 (-1, 0)).mono (by decide)
theorem row_works_519 : Template HasSnaky 12 required_519 envelope_519 := by
  refine compose HasSnaky 11 childrenC_519 childrenD_519 children_work_519 (0, 0)
    required_519 envelope_519 pivot_mem_519 child_required_sub_519 child_envelope_sub_519 ?_
  intro b hb; exact common_sub_519 (mem_commonEnvelope childrenD_519 b hb)
def required_528 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-2, 1), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_528 : Finset Cell := ⟨(([(-7, 0), (-7, 2), (-6, 0), (-6, 1), (-6, 2), (-5, 0), (-5, 1), (-5, 2), (-4, 0), (-4, 1), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_528 : Fin 5 → Finset Cell := ![(placedSet 1 (-1, 1) required_414), (placedSet 1 (0, 2) required_386), (placedSet 5 (0, -1) required_502), (placedSet 4 (-3, 1) required_226), (placedSet 5 (-1, 0) required_359)]
def childrenD_528 : Fin 5 → Finset Cell := ![(placedSet 1 (-1, 1) envelope_414), (placedSet 1 (0, 2) envelope_386), (placedSet 5 (0, -1) envelope_502), (placedSet 4 (-3, 1) envelope_226), (placedSet 5 (-1, 0) envelope_359)]
theorem common_sub_528 : commonEnvelope childrenD_528 ⊆ insert (0, 0) required_528 := by decide
theorem child_required_sub_528 : ∀ j, childrenC_528 j ⊆ insert (0, 0) required_528 := by decide
theorem child_envelope_sub_528 : ∀ j, childrenD_528 j ⊆ envelope_528 := by decide
theorem pivot_mem_528 : (0, 0) ∈ envelope_528 := by decide
theorem children_work_528 : ∀ j, Template HasSnaky 11 (childrenC_528 j) (childrenD_528 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_414 1 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_386 1 (0, 2)).mono (by decide)
  · exact (placed_template_map row_works_502 5 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_226 4 (-3, 1)).mono (by decide)
  · exact (placed_template_map row_works_359 5 (-1, 0)).mono (by decide)
theorem row_works_528 : Template HasSnaky 12 required_528 envelope_528 := by
  refine compose HasSnaky 11 childrenC_528 childrenD_528 children_work_528 (0, 0)
    required_528 envelope_528 pivot_mem_528 child_required_sub_528 child_envelope_sub_528 ?_
  intro b hb; exact common_sub_528 (mem_commonEnvelope childrenD_528 b hb)
end SnakyConditional

end OAI
