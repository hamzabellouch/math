import OAI.GameTheory.SnakyConditional.Templates.Level08Part08
import OAI.GameTheory.SnakyConditional.Templates.Level12Part01
import OAI.GameTheory.SnakyConditional.Templates.Level12Part02
import OAI.GameTheory.SnakyConditional.Templates.Level12Part05
import OAI.GameTheory.SnakyConditional.Templates.Level12Part06

namespace OAI

namespace SnakyConditional
def required_406 : Finset Cell := ⟨(([(0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_406 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -5), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (2, 2), (3, -1), (3, 0), (3, 1), (3, 2), (4, -1), (4, 0), (4, 1), (4, 2), (5, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_406 : Fin 7 → Finset Cell := ![(placedSet 1 (0, 1) required_295), (placedSet 7 (0, -3) required_172), (placedSet 3 (0, 1) required_245), (placedSet 5 (0, -3) required_197), (placedSet 0 (1, 1) required_236), (placedSet 3 (0, 1) required_176), (placedSet 2 (0, -3) required_364)]
def childrenD_406 : Fin 7 → Finset Cell := ![(placedSet 1 (0, 1) envelope_295), (placedSet 7 (0, -3) envelope_172), (placedSet 3 (0, 1) envelope_245), (placedSet 5 (0, -3) envelope_197), (placedSet 0 (1, 1) envelope_236), (placedSet 3 (0, 1) envelope_176), (placedSet 2 (0, -3) envelope_364)]
theorem common_sub_406 : commonEnvelope childrenD_406 ⊆ insert (0, 0) required_406 := by decide
theorem child_required_sub_406 : ∀ j, childrenC_406 j ⊆ insert (0, 0) required_406 := by decide
theorem child_envelope_sub_406 : ∀ j, childrenD_406 j ⊆ envelope_406 := by decide
theorem pivot_mem_406 : (0, 0) ∈ envelope_406 := by decide
theorem children_work_406 : ∀ j, Template HasSnaky 10 (childrenC_406 j) (childrenD_406 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_295 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_172 7 (0, -3)).mono (by decide)
  · exact (placed_template_map row_works_245 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_197 5 (0, -3)).mono (by decide)
  · exact (placed_template_map row_works_236 0 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_176 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_364 2 (0, -3)).mono (by decide)
theorem row_works_406 : Template HasSnaky 11 required_406 envelope_406 := by
  refine compose HasSnaky 10 childrenC_406 childrenD_406 children_work_406 (0, 0)
    required_406 envelope_406 pivot_mem_406 child_required_sub_406 child_envelope_sub_406 ?_
  intro b hb; exact common_sub_406 (mem_commonEnvelope childrenD_406 b hb)
def required_408 : Finset Cell := ⟨(([(-1, 0), (0, -3), (0, -2), (0, -1), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_408 : Finset Cell := ⟨(([(-5, -1), (-4, -1), (-4, 0), (-4, 1), (-3, -3), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (5, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_408 : Fin 4 → Finset Cell := ![(placedSet 0 (1, -2) required_357), (placedSet 7 (-2, 0) required_229), (placedSet 4 (-2, 0) required_223), (placedSet 0 (2, 0) required_223)]
def childrenD_408 : Fin 4 → Finset Cell := ![(placedSet 0 (1, -2) envelope_357), (placedSet 7 (-2, 0) envelope_229), (placedSet 4 (-2, 0) envelope_223), (placedSet 0 (2, 0) envelope_223)]
theorem common_sub_408 : commonEnvelope childrenD_408 ⊆ insert (0, 0) required_408 := by decide
theorem child_required_sub_408 : ∀ j, childrenC_408 j ⊆ insert (0, 0) required_408 := by decide
theorem child_envelope_sub_408 : ∀ j, childrenD_408 j ⊆ envelope_408 := by decide
theorem pivot_mem_408 : (0, 0) ∈ envelope_408 := by decide
theorem children_work_408 : ∀ j, Template HasSnaky 10 (childrenC_408 j) (childrenD_408 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_357 0 (1, -2)).mono (by decide)
  · exact (placed_template_map row_works_229 7 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_223 4 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_223 0 (2, 0)).mono (by decide)
theorem row_works_408 : Template HasSnaky 11 required_408 envelope_408 := by
  refine compose HasSnaky 10 childrenC_408 childrenD_408 children_work_408 (0, 0)
    required_408 envelope_408 pivot_mem_408 child_required_sub_408 child_envelope_sub_408 ?_
  intro b hb; exact common_sub_408 (mem_commonEnvelope childrenD_408 b hb)
def required_414 : Finset Cell := ⟨(([(-1, -1), (-1, 1), (0, -1), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_414 : Finset Cell := ⟨(([(-5, 0), (-5, 2), (-4, 0), (-4, 1), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -2), (2, 0), (2, 1), (2, 2), (3, -2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_414 : Fin 3 → Finset Cell := ![(placedSet 0 (-2, 1) required_374), (placedSet 2 (0, -2) required_199), (placedSet 2 (0, -2) required_185)]
def childrenD_414 : Fin 3 → Finset Cell := ![(placedSet 0 (-2, 1) envelope_374), (placedSet 2 (0, -2) envelope_199), (placedSet 2 (0, -2) envelope_185)]
theorem common_sub_414 : commonEnvelope childrenD_414 ⊆ insert (0, 0) required_414 := by decide
theorem child_required_sub_414 : ∀ j, childrenC_414 j ⊆ insert (0, 0) required_414 := by decide
theorem child_envelope_sub_414 : ∀ j, childrenD_414 j ⊆ envelope_414 := by decide
theorem pivot_mem_414 : (0, 0) ∈ envelope_414 := by decide
theorem children_work_414 : ∀ j, Template HasSnaky 10 (childrenC_414 j) (childrenD_414 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_374 0 (-2, 1)).mono (by decide)
  · exact (placed_template_map row_works_199 2 (0, -2)).mono (by decide)
  · exact (placed_template_map row_works_185 2 (0, -2)).mono (by decide)
theorem row_works_414 : Template HasSnaky 11 required_414 envelope_414 := by
  refine compose HasSnaky 10 childrenC_414 childrenD_414 children_work_414 (0, 0)
    required_414 envelope_414 pivot_mem_414 child_required_sub_414 child_envelope_sub_414 ?_
  intro b hb; exact common_sub_414 (mem_commonEnvelope childrenD_414 b hb)
def required_460 : Finset Cell := ⟨(([(-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_460 : Finset Cell := ⟨(([(-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_460 : Fin 7 → Finset Cell := ![(placedSet 6 (-3, 0) required_183), (placedSet 2 (1, 0) required_173), (placedSet 0 (1, 0) required_295), (placedSet 4 (-3, 0) required_282), (placedSet 2 (1, 0) required_246), (placedSet 2 (1, 0) required_263), (placedSet 2 (1, 0) required_220)]
def childrenD_460 : Fin 7 → Finset Cell := ![(placedSet 6 (-3, 0) envelope_183), (placedSet 2 (1, 0) envelope_173), (placedSet 0 (1, 0) envelope_295), (placedSet 4 (-3, 0) envelope_282), (placedSet 2 (1, 0) envelope_246), (placedSet 2 (1, 0) envelope_263), (placedSet 2 (1, 0) envelope_220)]
theorem common_sub_460 : commonEnvelope childrenD_460 ⊆ insert (0, 0) required_460 := by decide
theorem child_required_sub_460 : ∀ j, childrenC_460 j ⊆ insert (0, 0) required_460 := by decide
theorem child_envelope_sub_460 : ∀ j, childrenD_460 j ⊆ envelope_460 := by decide
theorem pivot_mem_460 : (0, 0) ∈ envelope_460 := by decide
theorem children_work_460 : ∀ j, Template HasSnaky 10 (childrenC_460 j) (childrenD_460 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_183 6 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_173 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_295 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_282 4 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_246 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_263 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_220 2 (1, 0)).mono (by decide)
theorem row_works_460 : Template HasSnaky 11 required_460 envelope_460 := by
  refine compose HasSnaky 10 childrenC_460 childrenD_460 children_work_460 (0, 0)
    required_460 envelope_460 pivot_mem_460 child_required_sub_460 child_envelope_sub_460 ?_
  intro b hb; exact common_sub_460 (mem_commonEnvelope childrenD_460 b hb)
def required_481 : Finset Cell := ⟨(([(-3, -2), (-2, 0), (-2, 1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_481 : Finset Cell := ⟨(([(-5, 0), (-4, -1), (-4, 0), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 1), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_481 : Fin 6 → Finset Cell := ![(placedSet 1 (1, 0) required_303), (placedSet 2 (-3, 0) required_429), (placedSet 1 (-3, 0) required_309), (placedSet 2 (-3, 0) required_206), (placedSet 2 (-3, 0) required_169), (placedSet 2 (-3, 0) required_207)]
def childrenD_481 : Fin 6 → Finset Cell := ![(placedSet 1 (1, 0) envelope_303), (placedSet 2 (-3, 0) envelope_429), (placedSet 1 (-3, 0) envelope_309), (placedSet 2 (-3, 0) envelope_206), (placedSet 2 (-3, 0) envelope_169), (placedSet 2 (-3, 0) envelope_207)]
theorem common_sub_481 : commonEnvelope childrenD_481 ⊆ insert (0, 0) required_481 := by decide
theorem child_required_sub_481 : ∀ j, childrenC_481 j ⊆ insert (0, 0) required_481 := by decide
theorem child_envelope_sub_481 : ∀ j, childrenD_481 j ⊆ envelope_481 := by decide
theorem pivot_mem_481 : (0, 0) ∈ envelope_481 := by decide
theorem children_work_481 : ∀ j, Template HasSnaky 10 (childrenC_481 j) (childrenD_481 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_303 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_429 2 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_309 1 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_206 2 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_169 2 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_207 2 (-3, 0)).mono (by decide)
theorem row_works_481 : Template HasSnaky 11 required_481 envelope_481 := by
  refine compose HasSnaky 10 childrenC_481 childrenD_481 children_work_481 (0, 0)
    required_481 envelope_481 pivot_mem_481 child_required_sub_481 child_envelope_sub_481 ?_
  intro b hb; exact common_sub_481 (mem_commonEnvelope childrenD_481 b hb)
end SnakyConditional

end OAI
