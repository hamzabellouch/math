import OAI.GameTheory.SnakyConditional.Templates.Level07Part08
import OAI.GameTheory.SnakyConditional.Templates.Level09Part01
import OAI.GameTheory.SnakyConditional.Templates.Level09Part02
import OAI.GameTheory.SnakyConditional.Templates.Level09Part03
import OAI.GameTheory.SnakyConditional.Templates.Level09Part04
import OAI.GameTheory.SnakyConditional.Templates.Level09Part06

namespace OAI

namespace SnakyConditional
def required_356 : Finset Cell := ⟨(([(-1, -1), (-1, 0), (1, -1), (1, 0), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_356 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1), (4, 0), (5, -1), (5, 0), (6, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_356 : Fin 4 → Finset Cell := ![(placedSet 2 (2, -1) required_24), (placedSet 6 (-2, -1) required_24), (placedSet 4 (-2, 0) required_211), (placedSet 0 (2, 0) required_179)]
def childrenD_356 : Fin 4 → Finset Cell := ![(placedSet 2 (2, -1) envelope_24), (placedSet 6 (-2, -1) envelope_24), (placedSet 4 (-2, 0) envelope_211), (placedSet 0 (2, 0) envelope_179)]
theorem common_sub_356 : commonEnvelope childrenD_356 ⊆ insert (0, 0) required_356 := by decide
theorem child_required_sub_356 : ∀ j, childrenC_356 j ⊆ insert (0, 0) required_356 := by decide
theorem child_envelope_sub_356 : ∀ j, childrenD_356 j ⊆ envelope_356 := by decide
theorem pivot_mem_356 : (0, 0) ∈ envelope_356 := by decide
theorem children_work_356 : ∀ j, Template HasSnaky 7 (childrenC_356 j) (childrenD_356 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_24 2 (2, -1)).mono (by decide)
  · exact (placed_template_map row_works_24 6 (-2, -1)).mono (by decide)
  · exact (placed_template_map row_works_211 4 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_179 0 (2, 0)).mono (by decide)
theorem row_works_356 : Template HasSnaky 8 required_356 envelope_356 := by
  refine compose HasSnaky 7 childrenC_356 childrenD_356 children_work_356 (0, 0)
    required_356 envelope_356 pivot_mem_356 child_required_sub_356 child_envelope_sub_356 ?_
  intro b hb; exact common_sub_356 (mem_commonEnvelope childrenD_356 b hb)
def required_380 : Finset Cell := ⟨(([(-2, 0), (-2, 2), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_380 : Finset Cell := ⟨(([(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 3), (-3, 4), (-3, 5), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 3), (-1, 4), (-1, 5), (0, -2), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_380 : Fin 4 → Finset Cell := ![(placedSet 4 (-2, 1) required_101), (placedSet 0 (-2, 1) required_271), (placedSet 0 (1, 0) required_223), (placedSet 3 (-3, 0) required_192)]
def childrenD_380 : Fin 4 → Finset Cell := ![(placedSet 4 (-2, 1) envelope_101), (placedSet 0 (-2, 1) envelope_271), (placedSet 0 (1, 0) envelope_223), (placedSet 3 (-3, 0) envelope_192)]
theorem common_sub_380 : commonEnvelope childrenD_380 ⊆ insert (0, 0) required_380 := by decide
theorem child_required_sub_380 : ∀ j, childrenC_380 j ⊆ insert (0, 0) required_380 := by decide
theorem child_envelope_sub_380 : ∀ j, childrenD_380 j ⊆ envelope_380 := by decide
theorem pivot_mem_380 : (0, 0) ∈ envelope_380 := by decide
theorem children_work_380 : ∀ j, Template HasSnaky 7 (childrenC_380 j) (childrenD_380 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_101 4 (-2, 1)).mono (by decide)
  · exact (placed_template_map row_works_271 0 (-2, 1)).mono (by decide)
  · exact (placed_template_map row_works_223 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_192 3 (-3, 0)).mono (by decide)
theorem row_works_380 : Template HasSnaky 8 required_380 envelope_380 := by
  refine compose HasSnaky 7 childrenC_380 childrenD_380 children_work_380 (0, 0)
    required_380 envelope_380 pivot_mem_380 child_required_sub_380 child_envelope_sub_380 ?_
  intro b hb; exact common_sub_380 (mem_commonEnvelope childrenD_380 b hb)
def required_383 : Finset Cell := ⟨(([(-1, 0), (-1, 2), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_383 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 3), (-2, 4), (-2, 5), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_383 : Fin 5 → Finset Cell := ![(placedSet 3 (-2, 0) required_192), (placedSet 0 (-1, 1) required_271), (placedSet 0 (2, 0) required_197), (placedSet 0 (2, 0) required_172), (placedSet 4 (-1, 1) required_215)]
def childrenD_383 : Fin 5 → Finset Cell := ![(placedSet 3 (-2, 0) envelope_192), (placedSet 0 (-1, 1) envelope_271), (placedSet 0 (2, 0) envelope_197), (placedSet 0 (2, 0) envelope_172), (placedSet 4 (-1, 1) envelope_215)]
theorem common_sub_383 : commonEnvelope childrenD_383 ⊆ insert (0, 0) required_383 := by decide
theorem child_required_sub_383 : ∀ j, childrenC_383 j ⊆ insert (0, 0) required_383 := by decide
theorem child_envelope_sub_383 : ∀ j, childrenD_383 j ⊆ envelope_383 := by decide
theorem pivot_mem_383 : (0, 0) ∈ envelope_383 := by decide
theorem children_work_383 : ∀ j, Template HasSnaky 7 (childrenC_383 j) (childrenD_383 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_192 3 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_271 0 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_197 0 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_172 0 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_215 4 (-1, 1)).mono (by decide)
theorem row_works_383 : Template HasSnaky 8 required_383 envelope_383 := by
  refine compose HasSnaky 7 childrenC_383 childrenD_383 children_work_383 (0, 0)
    required_383 envelope_383 pivot_mem_383 child_required_sub_383 child_envelope_sub_383 ?_
  intro b hb; exact common_sub_383 (mem_commonEnvelope childrenD_383 b hb)
def required_389 : Finset Cell := ⟨(([(-2, -2), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_389 : Finset Cell := ⟨(([(-5, -3), (-5, -1), (-4, -3), (-4, -2), (-4, -1), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-2, -2), (-2, 0), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -3), (2, 0), (2, 1), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_389 : Fin 5 → Finset Cell := ![(placedSet 5 (0, -3) required_197), (placedSet 7 (-1, -2) required_215), (placedSet 3 (-1, -2) required_271), (placedSet 0 (1, 1) required_236), (placedSet 6 (0, -3) required_192)]
def childrenD_389 : Fin 5 → Finset Cell := ![(placedSet 5 (0, -3) envelope_197), (placedSet 7 (-1, -2) envelope_215), (placedSet 3 (-1, -2) envelope_271), (placedSet 0 (1, 1) envelope_236), (placedSet 6 (0, -3) envelope_192)]
theorem common_sub_389 : commonEnvelope childrenD_389 ⊆ insert (0, 0) required_389 := by decide
theorem child_required_sub_389 : ∀ j, childrenC_389 j ⊆ insert (0, 0) required_389 := by decide
theorem child_envelope_sub_389 : ∀ j, childrenD_389 j ⊆ envelope_389 := by decide
theorem pivot_mem_389 : (0, 0) ∈ envelope_389 := by decide
theorem children_work_389 : ∀ j, Template HasSnaky 7 (childrenC_389 j) (childrenD_389 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_197 5 (0, -3)).mono (by decide)
  · exact (placed_template_map row_works_215 7 (-1, -2)).mono (by decide)
  · exact (placed_template_map row_works_271 3 (-1, -2)).mono (by decide)
  · exact (placed_template_map row_works_236 0 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_192 6 (0, -3)).mono (by decide)
theorem row_works_389 : Template HasSnaky 8 required_389 envelope_389 := by
  refine compose HasSnaky 7 childrenC_389 childrenD_389 children_work_389 (0, 0)
    required_389 envelope_389 pivot_mem_389 child_required_sub_389 child_envelope_sub_389 ?_
  intro b hb; exact common_sub_389 (mem_commonEnvelope childrenD_389 b hb)
def required_478 : Finset Cell := ⟨(([(1, -2), (1, -1), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_478 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_478 : Fin 3 → Finset Cell := ![(placedSet 3 (0, 1) required_25), (placedSet 2 (0, 1) required_165), (placedSet 0 (3, 0) required_190)]
def childrenD_478 : Fin 3 → Finset Cell := ![(placedSet 3 (0, 1) envelope_25), (placedSet 2 (0, 1) envelope_165), (placedSet 0 (3, 0) envelope_190)]
theorem common_sub_478 : commonEnvelope childrenD_478 ⊆ insert (0, 0) required_478 := by decide
theorem child_required_sub_478 : ∀ j, childrenC_478 j ⊆ insert (0, 0) required_478 := by decide
theorem child_envelope_sub_478 : ∀ j, childrenD_478 j ⊆ envelope_478 := by decide
theorem pivot_mem_478 : (0, 0) ∈ envelope_478 := by decide
theorem children_work_478 : ∀ j, Template HasSnaky 7 (childrenC_478 j) (childrenD_478 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_25 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_165 2 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_190 0 (3, 0)).mono (by decide)
theorem row_works_478 : Template HasSnaky 8 required_478 envelope_478 := by
  refine compose HasSnaky 7 childrenC_478 childrenD_478 children_work_478 (0, 0)
    required_478 envelope_478 pivot_mem_478 child_required_sub_478 child_envelope_sub_478 ?_
  intro b hb; exact common_sub_478 (mem_commonEnvelope childrenD_478 b hb)
def required_493 : Finset Cell := ⟨(([(-2, -2), (-2, -1), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_493 : Finset Cell := ⟨(([(-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_493 : Fin 4 → Finset Cell := ![(placedSet 0 (-3, 0) required_225), (placedSet 0 (1, -1) required_455), (placedSet 1 (1, 1) required_236), (placedSet 0 (1, 0) required_221)]
def childrenD_493 : Fin 4 → Finset Cell := ![(placedSet 0 (-3, 0) envelope_225), (placedSet 0 (1, -1) envelope_455), (placedSet 1 (1, 1) envelope_236), (placedSet 0 (1, 0) envelope_221)]
theorem common_sub_493 : commonEnvelope childrenD_493 ⊆ insert (0, 0) required_493 := by decide
theorem child_required_sub_493 : ∀ j, childrenC_493 j ⊆ insert (0, 0) required_493 := by decide
theorem child_envelope_sub_493 : ∀ j, childrenD_493 j ⊆ envelope_493 := by decide
theorem pivot_mem_493 : (0, 0) ∈ envelope_493 := by decide
theorem children_work_493 : ∀ j, Template HasSnaky 7 (childrenC_493 j) (childrenD_493 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_225 0 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_455 0 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_236 1 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_221 0 (1, 0)).mono (by decide)
theorem row_works_493 : Template HasSnaky 8 required_493 envelope_493 := by
  refine compose HasSnaky 7 childrenC_493 childrenD_493 children_work_493 (0, 0)
    required_493 envelope_493 pivot_mem_493 child_required_sub_493 child_envelope_sub_493 ?_
  intro b hb; exact common_sub_493 (mem_commonEnvelope childrenD_493 b hb)
def required_502 : Finset Cell := ⟨(([(-2, -2), (-2, 0), (-1, -2), (-1, 0), (0, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_502 : Finset Cell := ⟨(([(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -5), (-3, -4), (-3, -3), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_502 : Fin 5 → Finset Cell := ![(placedSet 6 (-2, -1) required_215), (placedSet 0 (0, -1) required_232), (placedSet 7 (-3, 0) required_192), (placedSet 0 (1, 0) required_173), (placedSet 2 (-2, -1) required_271)]
def childrenD_502 : Fin 5 → Finset Cell := ![(placedSet 6 (-2, -1) envelope_215), (placedSet 0 (0, -1) envelope_232), (placedSet 7 (-3, 0) envelope_192), (placedSet 0 (1, 0) envelope_173), (placedSet 2 (-2, -1) envelope_271)]
theorem common_sub_502 : commonEnvelope childrenD_502 ⊆ insert (0, 0) required_502 := by decide
theorem child_required_sub_502 : ∀ j, childrenC_502 j ⊆ insert (0, 0) required_502 := by decide
theorem child_envelope_sub_502 : ∀ j, childrenD_502 j ⊆ envelope_502 := by decide
theorem pivot_mem_502 : (0, 0) ∈ envelope_502 := by decide
theorem children_work_502 : ∀ j, Template HasSnaky 7 (childrenC_502 j) (childrenD_502 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_215 6 (-2, -1)).mono (by decide)
  · exact (placed_template_map row_works_232 0 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_192 7 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_173 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_271 2 (-2, -1)).mono (by decide)
theorem row_works_502 : Template HasSnaky 8 required_502 envelope_502 := by
  refine compose HasSnaky 7 childrenC_502 childrenD_502 children_work_502 (0, 0)
    required_502 envelope_502 pivot_mem_502 child_required_sub_502 child_envelope_sub_502 ?_
  intro b hb; exact common_sub_502 (mem_commonEnvelope childrenD_502 b hb)
end SnakyConditional

end OAI
