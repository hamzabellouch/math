import OAI.GameTheory.SnakyConditional.Templates.Level10Part03
import OAI.GameTheory.SnakyConditional.Templates.Level10Part04
import OAI.GameTheory.SnakyConditional.Templates.Level10Part06

namespace OAI

namespace SnakyConditional
def required_341 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0), (-1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_341 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 1), (-1, 2), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_341 : Fin 4 → Finset Cell := ![(placedSet 5 (1, 0) required_162), (placedSet 4 (0, 1) required_259), (placedSet 2 (1, 0) required_208), (placedSet 0 (-3, -1) required_143)]
def childrenD_341 : Fin 4 → Finset Cell := ![(placedSet 5 (1, 0) envelope_162), (placedSet 4 (0, 1) envelope_259), (placedSet 2 (1, 0) envelope_208), (placedSet 0 (-3, -1) envelope_143)]
theorem common_sub_341 : commonEnvelope childrenD_341 ⊆ insert (0, 0) required_341 := by decide
theorem child_required_sub_341 : ∀ j, childrenC_341 j ⊆ insert (0, 0) required_341 := by decide
theorem child_envelope_sub_341 : ∀ j, childrenD_341 j ⊆ envelope_341 := by decide
theorem pivot_mem_341 : (0, 0) ∈ envelope_341 := by decide
theorem children_work_341 : ∀ j, Template HasSnaky 8 (childrenC_341 j) (childrenD_341 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_162 5 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_259 4 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_208 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_143 0 (-3, -1)).mono (by decide)
theorem row_works_341 : Template HasSnaky 9 required_341 envelope_341 := by
  refine compose HasSnaky 8 childrenC_341 childrenD_341 children_work_341 (0, 0)
    required_341 envelope_341 pivot_mem_341 child_required_sub_341 child_envelope_sub_341 ?_
  intro b hb; exact common_sub_341 (mem_commonEnvelope childrenD_341 b hb)
def required_342 : Finset Cell := ⟨(([(-2, -2), (-1, -3), (-1, -2), (0, -3), (0, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_342 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, -3), (2, -2), (2, -1), (3, -3), (3, -2), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_342 : Fin 4 → Finset Cell := ![(placedSet 0 (1, -2) required_210), (placedSet 1 (0, -1) required_88), (placedSet 4 (0, -1) required_260), (placedSet 0 (0, -1) required_290)]
def childrenD_342 : Fin 4 → Finset Cell := ![(placedSet 0 (1, -2) envelope_210), (placedSet 1 (0, -1) envelope_88), (placedSet 4 (0, -1) envelope_260), (placedSet 0 (0, -1) envelope_290)]
theorem common_sub_342 : commonEnvelope childrenD_342 ⊆ insert (0, 0) required_342 := by decide
theorem child_required_sub_342 : ∀ j, childrenC_342 j ⊆ insert (0, 0) required_342 := by decide
theorem child_envelope_sub_342 : ∀ j, childrenD_342 j ⊆ envelope_342 := by decide
theorem pivot_mem_342 : (0, 0) ∈ envelope_342 := by decide
theorem children_work_342 : ∀ j, Template HasSnaky 8 (childrenC_342 j) (childrenD_342 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_210 0 (1, -2)).mono (by decide)
  · exact (placed_template_map row_works_88 1 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_260 4 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_290 0 (0, -1)).mono (by decide)
theorem row_works_342 : Template HasSnaky 9 required_342 envelope_342 := by
  refine compose HasSnaky 8 childrenC_342 childrenD_342 children_work_342 (0, 0)
    required_342 envelope_342 pivot_mem_342 child_required_sub_342 child_envelope_sub_342 ?_
  intro b hb; exact common_sub_342 (mem_commonEnvelope childrenD_342 b hb)
def required_343 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (1, -3), (1, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_343 : Finset Cell := ⟨(([(-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_343 : Fin 2 → Finset Cell := ![(placedSet 5 (0, 1) required_0), (placedSet 0 (1, 0) required_250)]
def childrenD_343 : Fin 2 → Finset Cell := ![(placedSet 5 (0, 1) envelope_0), (placedSet 0 (1, 0) envelope_250)]
theorem common_sub_343 : commonEnvelope childrenD_343 ⊆ insert (0, 0) required_343 := by decide
theorem child_required_sub_343 : ∀ j, childrenC_343 j ⊆ insert (0, 0) required_343 := by decide
theorem child_envelope_sub_343 : ∀ j, childrenD_343 j ⊆ envelope_343 := by decide
theorem pivot_mem_343 : (0, 0) ∈ envelope_343 := by decide
theorem children_work_343 : ∀ j, Template HasSnaky 8 (childrenC_343 j) (childrenD_343 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 5 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_250 0 (1, 0)).mono (by decide)
theorem row_works_343 : Template HasSnaky 9 required_343 envelope_343 := by
  refine compose HasSnaky 8 childrenC_343 childrenD_343 children_work_343 (0, 0)
    required_343 envelope_343 pivot_mem_343 child_required_sub_343 child_envelope_sub_343 ?_
  intro b hb; exact common_sub_343 (mem_commonEnvelope childrenD_343 b hb)
def required_359 : Finset Cell := ⟨(([(-1, -1), (-1, 1), (0, -1), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_359 : Finset Cell := ⟨(([(-4, 0), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_359 : Fin 3 → Finset Cell := ![(placedSet 0 (0, 2) required_134), (placedSet 7 (-1, -2) required_24), (placedSet 0 (1, 1) required_323)]
def childrenD_359 : Fin 3 → Finset Cell := ![(placedSet 0 (0, 2) envelope_134), (placedSet 7 (-1, -2) envelope_24), (placedSet 0 (1, 1) envelope_323)]
theorem common_sub_359 : commonEnvelope childrenD_359 ⊆ insert (0, 0) required_359 := by decide
theorem child_required_sub_359 : ∀ j, childrenC_359 j ⊆ insert (0, 0) required_359 := by decide
theorem child_envelope_sub_359 : ∀ j, childrenD_359 j ⊆ envelope_359 := by decide
theorem pivot_mem_359 : (0, 0) ∈ envelope_359 := by decide
theorem children_work_359 : ∀ j, Template HasSnaky 8 (childrenC_359 j) (childrenD_359 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_134 0 (0, 2)).mono (by decide)
  · exact (placed_template_map row_works_24 7 (-1, -2)).mono (by decide)
  · exact (placed_template_map row_works_323 0 (1, 1)).mono (by decide)
theorem row_works_359 : Template HasSnaky 9 required_359 envelope_359 := by
  refine compose HasSnaky 8 childrenC_359 childrenD_359 children_work_359 (0, 0)
    required_359 envelope_359 pivot_mem_359 child_required_sub_359 child_envelope_sub_359 ?_
  intro b hb; exact common_sub_359 (mem_commonEnvelope childrenD_359 b hb)
def required_363 : Finset Cell := ⟨(([(-4, -3), (-3, -3), (-3, 0), (-2, -3), (-1, -3), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_363 : Finset Cell := ⟨(([(-5, -1), (-4, -3), (-4, -1), (-4, 0), (-3, -3), (-3, -1), (-3, 0), (-2, -3), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, -4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_363 : Fin 2 → Finset Cell := ![(placedSet 1 (0, -2) required_137), (placedSet 0 (-2, 0) required_248)]
def childrenD_363 : Fin 2 → Finset Cell := ![(placedSet 1 (0, -2) envelope_137), (placedSet 0 (-2, 0) envelope_248)]
theorem common_sub_363 : commonEnvelope childrenD_363 ⊆ insert (0, 0) required_363 := by decide
theorem child_required_sub_363 : ∀ j, childrenC_363 j ⊆ insert (0, 0) required_363 := by decide
theorem child_envelope_sub_363 : ∀ j, childrenD_363 j ⊆ envelope_363 := by decide
theorem pivot_mem_363 : (0, 0) ∈ envelope_363 := by decide
theorem children_work_363 : ∀ j, Template HasSnaky 8 (childrenC_363 j) (childrenD_363 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_137 1 (0, -2)).mono (by decide)
  · exact (placed_template_map row_works_248 0 (-2, 0)).mono (by decide)
theorem row_works_363 : Template HasSnaky 9 required_363 envelope_363 := by
  refine compose HasSnaky 8 childrenC_363 childrenD_363 children_work_363 (0, 0)
    required_363 envelope_363 pivot_mem_363 child_required_sub_363 child_envelope_sub_363 ?_
  intro b hb; exact common_sub_363 (mem_commonEnvelope childrenD_363 b hb)
def required_371 : Finset Cell := ⟨(([(-4, -3), (-3, -3), (-3, 0), (-2, -3), (-1, -3), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_371 : Finset Cell := ⟨(([(-6, 1), (-5, 0), (-5, 1), (-4, -3), (-4, 0), (-4, 1), (-3, -3), (-3, 0), (-3, 1), (-2, -3), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, -4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_371 : Fin 2 → Finset Cell := ![(placedSet 6 (-2, 0) required_267), (placedSet 1 (0, -2) required_137)]
def childrenD_371 : Fin 2 → Finset Cell := ![(placedSet 6 (-2, 0) envelope_267), (placedSet 1 (0, -2) envelope_137)]
theorem common_sub_371 : commonEnvelope childrenD_371 ⊆ insert (0, 0) required_371 := by decide
theorem child_required_sub_371 : ∀ j, childrenC_371 j ⊆ insert (0, 0) required_371 := by decide
theorem child_envelope_sub_371 : ∀ j, childrenD_371 j ⊆ envelope_371 := by decide
theorem pivot_mem_371 : (0, 0) ∈ envelope_371 := by decide
theorem children_work_371 : ∀ j, Template HasSnaky 8 (childrenC_371 j) (childrenD_371 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_267 6 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_137 1 (0, -2)).mono (by decide)
theorem row_works_371 : Template HasSnaky 9 required_371 envelope_371 := by
  refine compose HasSnaky 8 childrenC_371 childrenD_371 children_work_371 (0, 0)
    required_371 envelope_371 pivot_mem_371 child_required_sub_371 child_envelope_sub_371 ?_
  intro b hb; exact common_sub_371 (mem_commonEnvelope childrenD_371 b hb)
end SnakyConditional

end OAI
