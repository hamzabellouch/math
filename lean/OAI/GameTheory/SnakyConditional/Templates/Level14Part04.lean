import OAI.GameTheory.SnakyConditional.Templates.Level12Part07
import OAI.GameTheory.SnakyConditional.Templates.Level13Part03
import OAI.GameTheory.SnakyConditional.Templates.Level13Part04

namespace OAI

namespace SnakyConditional
def required_409 : Finset Cell := ⟨(([(0, -3), (0, -2), (1, -3), (2, -1), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_409 : Finset Cell := ⟨(([(-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_409 : Fin 4 → Finset Cell := ![(placedSet 6 (0, -1) required_136), (placedSet 0 (1, 0) required_384), (placedSet 4 (0, -1) required_133), (placedSet 3 (0, -1) required_110)]
def childrenD_409 : Fin 4 → Finset Cell := ![(placedSet 6 (0, -1) envelope_136), (placedSet 0 (1, 0) envelope_384), (placedSet 4 (0, -1) envelope_133), (placedSet 3 (0, -1) envelope_110)]
theorem common_sub_409 : commonEnvelope childrenD_409 ⊆ insert (0, 0) required_409 := by decide
theorem child_required_sub_409 : ∀ j, childrenC_409 j ⊆ insert (0, 0) required_409 := by decide
theorem child_envelope_sub_409 : ∀ j, childrenD_409 j ⊆ envelope_409 := by decide
theorem pivot_mem_409 : (0, 0) ∈ envelope_409 := by decide
theorem children_work_409 : ∀ j, Template HasSnaky 11 (childrenC_409 j) (childrenD_409 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_136 6 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_384 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_133 4 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_110 3 (0, -1)).mono (by decide)
theorem row_works_409 : Template HasSnaky 12 required_409 envelope_409 := by
  refine compose HasSnaky 11 childrenC_409 childrenD_409 children_work_409 (0, 0)
    required_409 envelope_409 pivot_mem_409 child_required_sub_409 child_envelope_sub_409 ?_
  intro b hb; exact common_sub_409 (mem_commonEnvelope childrenD_409 b hb)
def required_415 : Finset Cell := ⟨(([(-3, -3), (-2, -3), (-2, 0), (-1, -3), (0, -3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_415 : Finset Cell := ⟨(([(-5, 1), (-4, 0), (-4, 1), (-3, -3), (-3, 0), (-3, 1), (-2, -3), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_415 : Fin 5 → Finset Cell := ![(placedSet 1 (0, -2) required_177), (placedSet 1 (0, -2) required_164), (placedSet 1 (1, -2) required_205), (placedSet 0 (-1, 0) required_384), (placedSet 0 (1, 0) required_371)]
def childrenD_415 : Fin 5 → Finset Cell := ![(placedSet 1 (0, -2) envelope_177), (placedSet 1 (0, -2) envelope_164), (placedSet 1 (1, -2) envelope_205), (placedSet 0 (-1, 0) envelope_384), (placedSet 0 (1, 0) envelope_371)]
theorem common_sub_415 : commonEnvelope childrenD_415 ⊆ insert (0, 0) required_415 := by decide
theorem child_required_sub_415 : ∀ j, childrenC_415 j ⊆ insert (0, 0) required_415 := by decide
theorem child_envelope_sub_415 : ∀ j, childrenD_415 j ⊆ envelope_415 := by decide
theorem pivot_mem_415 : (0, 0) ∈ envelope_415 := by decide
theorem children_work_415 : ∀ j, Template HasSnaky 11 (childrenC_415 j) (childrenD_415 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_177 1 (0, -2)).mono (by decide)
  · exact (placed_template_map row_works_164 1 (0, -2)).mono (by decide)
  · exact (placed_template_map row_works_205 1 (1, -2)).mono (by decide)
  · exact (placed_template_map row_works_384 0 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_371 0 (1, 0)).mono (by decide)
theorem row_works_415 : Template HasSnaky 12 required_415 envelope_415 := by
  refine compose HasSnaky 11 childrenC_415 childrenD_415 children_work_415 (0, 0)
    required_415 envelope_415 pivot_mem_415 child_required_sub_415 child_envelope_sub_415 ?_
  intro b hb; exact common_sub_415 (mem_commonEnvelope childrenD_415 b hb)
def required_421 : Finset Cell := ⟨(([(-1, -2), (-1, -1), (-1, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_421 : Finset Cell := ⟨(([(-6, 1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 2), (2, 3), (2, 4), (3, -3), (3, -2), (3, -1), (4, -3), (4, -2), (4, -1), (5, -3), (5, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_421 : Fin 4 → Finset Cell := ![(placedSet 6 (-2, -1) required_24), (placedSet 1 (1, -1) required_397), (placedSet 6 (-2, -1) required_25), (placedSet 4 (-2, 0) required_241)]
def childrenD_421 : Fin 4 → Finset Cell := ![(placedSet 6 (-2, -1) envelope_24), (placedSet 1 (1, -1) envelope_397), (placedSet 6 (-2, -1) envelope_25), (placedSet 4 (-2, 0) envelope_241)]
theorem common_sub_421 : commonEnvelope childrenD_421 ⊆ insert (0, 0) required_421 := by decide
theorem child_required_sub_421 : ∀ j, childrenC_421 j ⊆ insert (0, 0) required_421 := by decide
theorem child_envelope_sub_421 : ∀ j, childrenD_421 j ⊆ envelope_421 := by decide
theorem pivot_mem_421 : (0, 0) ∈ envelope_421 := by decide
theorem children_work_421 : ∀ j, Template HasSnaky 11 (childrenC_421 j) (childrenD_421 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_24 6 (-2, -1)).mono (by decide)
  · exact (placed_template_map row_works_397 1 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_25 6 (-2, -1)).mono (by decide)
  · exact (placed_template_map row_works_241 4 (-2, 0)).mono (by decide)
theorem row_works_421 : Template HasSnaky 12 required_421 envelope_421 := by
  refine compose HasSnaky 11 childrenC_421 childrenD_421 children_work_421 (0, 0)
    required_421 envelope_421 pivot_mem_421 child_required_sub_421 child_envelope_sub_421 ?_
  intro b hb; exact common_sub_421 (mem_commonEnvelope childrenD_421 b hb)
def required_423 : Finset Cell := ⟨(([(-1, -2), (-1, 0), (0, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_423 : Finset Cell := ⟨(([(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_423 : Fin 5 → Finset Cell := ![(placedSet 4 (-2, 0) required_378), (placedSet 0 (1, 0) required_386), (placedSet 3 (-1, 1) required_226), (placedSet 4 (-2, 0) required_386), (placedSet 0 (1, 0) required_378)]
def childrenD_423 : Fin 5 → Finset Cell := ![(placedSet 4 (-2, 0) envelope_378), (placedSet 0 (1, 0) envelope_386), (placedSet 3 (-1, 1) envelope_226), (placedSet 4 (-2, 0) envelope_386), (placedSet 0 (1, 0) envelope_378)]
theorem common_sub_423 : commonEnvelope childrenD_423 ⊆ insert (0, 0) required_423 := by decide
theorem child_required_sub_423 : ∀ j, childrenC_423 j ⊆ insert (0, 0) required_423 := by decide
theorem child_envelope_sub_423 : ∀ j, childrenD_423 j ⊆ envelope_423 := by decide
theorem pivot_mem_423 : (0, 0) ∈ envelope_423 := by decide
theorem children_work_423 : ∀ j, Template HasSnaky 11 (childrenC_423 j) (childrenD_423 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_378 4 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_386 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_226 3 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_386 4 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_378 0 (1, 0)).mono (by decide)
theorem row_works_423 : Template HasSnaky 12 required_423 envelope_423 := by
  refine compose HasSnaky 11 childrenC_423 childrenD_423 children_work_423 (0, 0)
    required_423 envelope_423 pivot_mem_423 child_required_sub_423 child_envelope_sub_423 ?_
  intro b hb; exact common_sub_423 (mem_commonEnvelope childrenD_423 b hb)
end SnakyConditional

end OAI
