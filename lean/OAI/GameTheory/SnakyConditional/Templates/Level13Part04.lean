import OAI.GameTheory.SnakyConditional.Templates.Level12Part01
import OAI.GameTheory.SnakyConditional.Templates.Level12Part03
import OAI.GameTheory.SnakyConditional.Templates.Level12Part06

namespace OAI

namespace SnakyConditional
def required_392 : Finset Cell := ⟨(([(-1, -2), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_392 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_392 : Fin 4 → Finset Cell := ![(placedSet 7 (-1, -3) required_24), (placedSet 1 (0, 1) required_107), (placedSet 0 (1, 1) required_236), (placedSet 2 (0, -3) required_364)]
def childrenD_392 : Fin 4 → Finset Cell := ![(placedSet 7 (-1, -3) envelope_24), (placedSet 1 (0, 1) envelope_107), (placedSet 0 (1, 1) envelope_236), (placedSet 2 (0, -3) envelope_364)]
theorem common_sub_392 : commonEnvelope childrenD_392 ⊆ insert (0, 0) required_392 := by decide
theorem child_required_sub_392 : ∀ j, childrenC_392 j ⊆ insert (0, 0) required_392 := by decide
theorem child_envelope_sub_392 : ∀ j, childrenD_392 j ⊆ envelope_392 := by decide
theorem pivot_mem_392 : (0, 0) ∈ envelope_392 := by decide
theorem children_work_392 : ∀ j, Template HasSnaky 10 (childrenC_392 j) (childrenD_392 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_24 7 (-1, -3)).mono (by decide)
  · exact (placed_template_map row_works_107 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_236 0 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_364 2 (0, -3)).mono (by decide)
theorem row_works_392 : Template HasSnaky 11 required_392 envelope_392 := by
  refine compose HasSnaky 10 childrenC_392 childrenD_392 children_work_392 (0, 0)
    required_392 envelope_392 pivot_mem_392 child_required_sub_392 child_envelope_sub_392 ?_
  intro b hb; exact common_sub_392 (mem_commonEnvelope childrenD_392 b hb)
def required_395 : Finset Cell := ⟨(([(-1, 0), (1, -1), (1, 0), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_395 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-4, 2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_395 : Fin 4 → Finset Cell := ![(placedSet 4 (-2, 0) required_211), (placedSet 0 (2, 0) required_376), (placedSet 2 (2, -1) required_24), (placedSet 3 (-2, 1) required_236)]
def childrenD_395 : Fin 4 → Finset Cell := ![(placedSet 4 (-2, 0) envelope_211), (placedSet 0 (2, 0) envelope_376), (placedSet 2 (2, -1) envelope_24), (placedSet 3 (-2, 1) envelope_236)]
theorem common_sub_395 : commonEnvelope childrenD_395 ⊆ insert (0, 0) required_395 := by decide
theorem child_required_sub_395 : ∀ j, childrenC_395 j ⊆ insert (0, 0) required_395 := by decide
theorem child_envelope_sub_395 : ∀ j, childrenD_395 j ⊆ envelope_395 := by decide
theorem pivot_mem_395 : (0, 0) ∈ envelope_395 := by decide
theorem children_work_395 : ∀ j, Template HasSnaky 10 (childrenC_395 j) (childrenD_395 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_211 4 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_376 0 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_24 2 (2, -1)).mono (by decide)
  · exact (placed_template_map row_works_236 3 (-2, 1)).mono (by decide)
theorem row_works_395 : Template HasSnaky 11 required_395 envelope_395 := by
  refine compose HasSnaky 10 childrenC_395 childrenD_395 children_work_395 (0, 0)
    required_395 envelope_395 pivot_mem_395 child_required_sub_395 child_envelope_sub_395 ?_
  intro b hb; exact common_sub_395 (mem_commonEnvelope childrenD_395 b hb)
def required_397 : Finset Cell := ⟨(([(0, -2), (1, -2), (1, -1), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_397 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, -5), (2, -4), (2, -3), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_397 : Fin 3 → Finset Cell := ![(placedSet 3 (0, 1) required_24), (placedSet 0 (-1, 0) required_374), (placedSet 5 (1, -3) required_65)]
def childrenD_397 : Fin 3 → Finset Cell := ![(placedSet 3 (0, 1) envelope_24), (placedSet 0 (-1, 0) envelope_374), (placedSet 5 (1, -3) envelope_65)]
theorem common_sub_397 : commonEnvelope childrenD_397 ⊆ insert (0, 0) required_397 := by decide
theorem child_required_sub_397 : ∀ j, childrenC_397 j ⊆ insert (0, 0) required_397 := by decide
theorem child_envelope_sub_397 : ∀ j, childrenD_397 j ⊆ envelope_397 := by decide
theorem pivot_mem_397 : (0, 0) ∈ envelope_397 := by decide
theorem children_work_397 : ∀ j, Template HasSnaky 10 (childrenC_397 j) (childrenD_397 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_24 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_374 0 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_65 5 (1, -3)).mono (by decide)
theorem row_works_397 : Template HasSnaky 11 required_397 envelope_397 := by
  refine compose HasSnaky 10 childrenC_397 childrenD_397 children_work_397 (0, 0)
    required_397 envelope_397 pivot_mem_397 child_required_sub_397 child_envelope_sub_397 ?_
  intro b hb; exact common_sub_397 (mem_commonEnvelope childrenD_397 b hb)
def required_399 : Finset Cell := ⟨(([(-2, -2), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_399 : Finset Cell := ⟨(([(-5, -3), (-5, -1), (-4, -3), (-4, -2), (-4, -1), (-3, -3), (-3, -2), (-3, -1), (-2, -2), (-2, 1), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_399 : Fin 5 → Finset Cell := ![(placedSet 6 (0, -3) required_192), (placedSet 3 (-1, -2) required_271), (placedSet 1 (0, 1) required_173), (placedSet 1 (-1, 1) required_319), (placedSet 7 (-1, -2) required_215)]
def childrenD_399 : Fin 5 → Finset Cell := ![(placedSet 6 (0, -3) envelope_192), (placedSet 3 (-1, -2) envelope_271), (placedSet 1 (0, 1) envelope_173), (placedSet 1 (-1, 1) envelope_319), (placedSet 7 (-1, -2) envelope_215)]
theorem common_sub_399 : commonEnvelope childrenD_399 ⊆ insert (0, 0) required_399 := by decide
theorem child_required_sub_399 : ∀ j, childrenC_399 j ⊆ insert (0, 0) required_399 := by decide
theorem child_envelope_sub_399 : ∀ j, childrenD_399 j ⊆ envelope_399 := by decide
theorem pivot_mem_399 : (0, 0) ∈ envelope_399 := by decide
theorem children_work_399 : ∀ j, Template HasSnaky 10 (childrenC_399 j) (childrenD_399 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_192 6 (0, -3)).mono (by decide)
  · exact (placed_template_map row_works_271 3 (-1, -2)).mono (by decide)
  · exact (placed_template_map row_works_173 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_319 1 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_215 7 (-1, -2)).mono (by decide)
theorem row_works_399 : Template HasSnaky 11 required_399 envelope_399 := by
  refine compose HasSnaky 10 childrenC_399 childrenD_399 children_work_399 (0, 0)
    required_399 envelope_399 pivot_mem_399 child_required_sub_399 child_envelope_sub_399 ?_
  intro b hb; exact common_sub_399 (mem_commonEnvelope childrenD_399 b hb)
def required_401 : Finset Cell := ⟨(([(-1, -1), (0, -1), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_401 : Finset Cell := ⟨(([(-4, 0), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_401 : Fin 4 → Finset Cell := ![(placedSet 7 (-1, -2) required_24), (placedSet 0 (0, 2) required_286), (placedSet 2 (0, -2) required_364), (placedSet 1 (-1, 2) required_319)]
def childrenD_401 : Fin 4 → Finset Cell := ![(placedSet 7 (-1, -2) envelope_24), (placedSet 0 (0, 2) envelope_286), (placedSet 2 (0, -2) envelope_364), (placedSet 1 (-1, 2) envelope_319)]
theorem common_sub_401 : commonEnvelope childrenD_401 ⊆ insert (0, 0) required_401 := by decide
theorem child_required_sub_401 : ∀ j, childrenC_401 j ⊆ insert (0, 0) required_401 := by decide
theorem child_envelope_sub_401 : ∀ j, childrenD_401 j ⊆ envelope_401 := by decide
theorem pivot_mem_401 : (0, 0) ∈ envelope_401 := by decide
theorem children_work_401 : ∀ j, Template HasSnaky 10 (childrenC_401 j) (childrenD_401 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_24 7 (-1, -2)).mono (by decide)
  · exact (placed_template_map row_works_286 0 (0, 2)).mono (by decide)
  · exact (placed_template_map row_works_364 2 (0, -2)).mono (by decide)
  · exact (placed_template_map row_works_319 1 (-1, 2)).mono (by decide)
theorem row_works_401 : Template HasSnaky 11 required_401 envelope_401 := by
  refine compose HasSnaky 10 childrenC_401 childrenD_401 children_work_401 (0, 0)
    required_401 envelope_401 pivot_mem_401 child_required_sub_401 child_envelope_sub_401 ?_
  intro b hb; exact common_sub_401 (mem_commonEnvelope childrenD_401 b hb)
end SnakyConditional

end OAI
