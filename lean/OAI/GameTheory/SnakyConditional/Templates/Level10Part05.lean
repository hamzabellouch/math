import OAI.GameTheory.SnakyConditional.Templates.Level09Part02
import OAI.GameTheory.SnakyConditional.Templates.Level09Part07

namespace OAI

namespace SnakyConditional
def required_291 : Finset Cell := ⟨(([(1, -1), (1, 0), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_291 : Finset Cell := ⟨(([(-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, -1), (7, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_291 : Fin 3 → Finset Cell := ![(placedSet 3 (-1, 0) required_89), (placedSet 0 (4, 0) required_202), (placedSet 4 (-1, 0) required_55)]
def childrenD_291 : Fin 3 → Finset Cell := ![(placedSet 3 (-1, 0) envelope_89), (placedSet 0 (4, 0) envelope_202), (placedSet 4 (-1, 0) envelope_55)]
theorem common_sub_291 : commonEnvelope childrenD_291 ⊆ insert (0, 0) required_291 := by decide
theorem child_required_sub_291 : ∀ j, childrenC_291 j ⊆ insert (0, 0) required_291 := by decide
theorem child_envelope_sub_291 : ∀ j, childrenD_291 j ⊆ envelope_291 := by decide
theorem pivot_mem_291 : (0, 0) ∈ envelope_291 := by decide
theorem children_work_291 : ∀ j, Template HasSnaky 7 (childrenC_291 j) (childrenD_291 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_89 3 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_202 0 (4, 0)).mono (by decide)
  · exact (placed_template_map row_works_55 4 (-1, 0)).mono (by decide)
theorem row_works_291 : Template HasSnaky 8 required_291 envelope_291 := by
  refine compose HasSnaky 7 childrenC_291 childrenD_291 children_work_291 (0, 0)
    required_291 envelope_291 pivot_mem_291 child_required_sub_291 child_envelope_sub_291 ?_
  intro b hb; exact common_sub_291 (mem_commonEnvelope childrenD_291 b hb)
def required_298 : Finset Cell := ⟨(([(0, -1), (1, 0), (2, -1), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_298 : Finset Cell := ⟨(([(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_298 : Fin 4 → Finset Cell := ![(placedSet 2 (3, -1) required_24), (placedSet 6 (-1, -1) required_24), (placedSet 4 (-1, 0) required_107), (placedSet 0 (3, 0) required_195)]
def childrenD_298 : Fin 4 → Finset Cell := ![(placedSet 2 (3, -1) envelope_24), (placedSet 6 (-1, -1) envelope_24), (placedSet 4 (-1, 0) envelope_107), (placedSet 0 (3, 0) envelope_195)]
theorem common_sub_298 : commonEnvelope childrenD_298 ⊆ insert (0, 0) required_298 := by decide
theorem child_required_sub_298 : ∀ j, childrenC_298 j ⊆ insert (0, 0) required_298 := by decide
theorem child_envelope_sub_298 : ∀ j, childrenD_298 j ⊆ envelope_298 := by decide
theorem pivot_mem_298 : (0, 0) ∈ envelope_298 := by decide
theorem children_work_298 : ∀ j, Template HasSnaky 7 (childrenC_298 j) (childrenD_298 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_24 2 (3, -1)).mono (by decide)
  · exact (placed_template_map row_works_24 6 (-1, -1)).mono (by decide)
  · exact (placed_template_map row_works_107 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_195 0 (3, 0)).mono (by decide)
theorem row_works_298 : Template HasSnaky 8 required_298 envelope_298 := by
  refine compose HasSnaky 7 childrenC_298 childrenD_298 children_work_298 (0, 0)
    required_298 envelope_298 pivot_mem_298 child_required_sub_298 child_envelope_sub_298 ?_
  intro b hb; exact common_sub_298 (mem_commonEnvelope childrenD_298 b hb)
def required_304 : Finset Cell := ⟨(([(1, -1), (1, 0), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_304 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, -1), (7, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_304 : Fin 3 → Finset Cell := ![(placedSet 4 (-1, 0) required_55), (placedSet 0 (4, 0) required_202), (placedSet 3 (-1, 0) required_131)]
def childrenD_304 : Fin 3 → Finset Cell := ![(placedSet 4 (-1, 0) envelope_55), (placedSet 0 (4, 0) envelope_202), (placedSet 3 (-1, 0) envelope_131)]
theorem common_sub_304 : commonEnvelope childrenD_304 ⊆ insert (0, 0) required_304 := by decide
theorem child_required_sub_304 : ∀ j, childrenC_304 j ⊆ insert (0, 0) required_304 := by decide
theorem child_envelope_sub_304 : ∀ j, childrenD_304 j ⊆ envelope_304 := by decide
theorem pivot_mem_304 : (0, 0) ∈ envelope_304 := by decide
theorem children_work_304 : ∀ j, Template HasSnaky 7 (childrenC_304 j) (childrenD_304 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_55 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_202 0 (4, 0)).mono (by decide)
  · exact (placed_template_map row_works_131 3 (-1, 0)).mono (by decide)
theorem row_works_304 : Template HasSnaky 8 required_304 envelope_304 := by
  refine compose HasSnaky 7 childrenC_304 childrenD_304 children_work_304 (0, 0)
    required_304 envelope_304 pivot_mem_304 child_required_sub_304 child_envelope_sub_304 ?_
  intro b hb; exact common_sub_304 (mem_commonEnvelope childrenD_304 b hb)
def required_305 : Finset Cell := ⟨(([(-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_305 : Finset Cell := ⟨(([(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_305 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_6), (placedSet 0 (-3, 0) required_278)]
def childrenD_305 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_6), (placedSet 0 (-3, 0) envelope_278)]
theorem common_sub_305 : commonEnvelope childrenD_305 ⊆ insert (0, 0) required_305 := by decide
theorem child_required_sub_305 : ∀ j, childrenC_305 j ⊆ insert (0, 0) required_305 := by decide
theorem child_envelope_sub_305 : ∀ j, childrenD_305 j ⊆ envelope_305 := by decide
theorem pivot_mem_305 : (0, 0) ∈ envelope_305 := by decide
theorem children_work_305 : ∀ j, Template HasSnaky 7 (childrenC_305 j) (childrenD_305 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_278 0 (-3, 0)).mono (by decide)
theorem row_works_305 : Template HasSnaky 8 required_305 envelope_305 := by
  refine compose HasSnaky 7 childrenC_305 childrenD_305 children_work_305 (0, 0)
    required_305 envelope_305 pivot_mem_305 child_required_sub_305 child_envelope_sub_305 ?_
  intro b hb; exact common_sub_305 (mem_commonEnvelope childrenD_305 b hb)
def required_306 : Finset Cell := ⟨(([(-1, -4), (-1, -3), (-1, -2), (-1, -1), (0, -3), (1, -3), (2, -3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_306 : Finset Cell := ⟨(([(-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, 0), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, 0), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_306 : Fin 2 → Finset Cell := ![(placedSet 1 (0, -1) required_4), (placedSet 0 (2, 0) required_288)]
def childrenD_306 : Fin 2 → Finset Cell := ![(placedSet 1 (0, -1) envelope_4), (placedSet 0 (2, 0) envelope_288)]
theorem common_sub_306 : commonEnvelope childrenD_306 ⊆ insert (0, 0) required_306 := by decide
theorem child_required_sub_306 : ∀ j, childrenC_306 j ⊆ insert (0, 0) required_306 := by decide
theorem child_envelope_sub_306 : ∀ j, childrenD_306 j ⊆ envelope_306 := by decide
theorem pivot_mem_306 : (0, 0) ∈ envelope_306 := by decide
theorem children_work_306 : ∀ j, Template HasSnaky 7 (childrenC_306 j) (childrenD_306 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_4 1 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_288 0 (2, 0)).mono (by decide)
theorem row_works_306 : Template HasSnaky 8 required_306 envelope_306 := by
  refine compose HasSnaky 7 childrenC_306 childrenD_306 children_work_306 (0, 0)
    required_306 envelope_306 pivot_mem_306 child_required_sub_306 child_envelope_sub_306 ?_
  intro b hb; exact common_sub_306 (mem_commonEnvelope childrenD_306 b hb)
def required_310 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_310 : Finset Cell := ⟨(([(-3, 0), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 0), (4, -2), (4, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_310 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_6), (placedSet 0 (1, -1) required_281)]
def childrenD_310 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_6), (placedSet 0 (1, -1) envelope_281)]
theorem common_sub_310 : commonEnvelope childrenD_310 ⊆ insert (0, 0) required_310 := by decide
theorem child_required_sub_310 : ∀ j, childrenC_310 j ⊆ insert (0, 0) required_310 := by decide
theorem child_envelope_sub_310 : ∀ j, childrenD_310 j ⊆ envelope_310 := by decide
theorem pivot_mem_310 : (0, 0) ∈ envelope_310 := by decide
theorem children_work_310 : ∀ j, Template HasSnaky 7 (childrenC_310 j) (childrenD_310 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_281 0 (1, -1)).mono (by decide)
theorem row_works_310 : Template HasSnaky 8 required_310 envelope_310 := by
  refine compose HasSnaky 7 childrenC_310 childrenD_310 children_work_310 (0, 0)
    required_310 envelope_310 pivot_mem_310 child_required_sub_310 child_envelope_sub_310 ?_
  intro b hb; exact common_sub_310 (mem_commonEnvelope childrenD_310 b hb)
def required_311 : Finset Cell := ⟨(([(-1, 0), (0, -3), (0, -2), (0, -1), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_311 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_311 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, 1) required_6), (placedSet 0 (-2, 0) required_278)]
def childrenD_311 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, 1) envelope_6), (placedSet 0 (-2, 0) envelope_278)]
theorem common_sub_311 : commonEnvelope childrenD_311 ⊆ insert (0, 0) required_311 := by decide
theorem child_required_sub_311 : ∀ j, childrenC_311 j ⊆ insert (0, 0) required_311 := by decide
theorem child_envelope_sub_311 : ∀ j, childrenD_311 j ⊆ envelope_311 := by decide
theorem pivot_mem_311 : (0, 0) ∈ envelope_311 := by decide
theorem children_work_311 : ∀ j, Template HasSnaky 7 (childrenC_311 j) (childrenD_311 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_278 0 (-2, 0)).mono (by decide)
theorem row_works_311 : Template HasSnaky 8 required_311 envelope_311 := by
  refine compose HasSnaky 7 childrenC_311 childrenD_311 children_work_311 (0, 0)
    required_311 envelope_311 pivot_mem_311 child_required_sub_311 child_envelope_sub_311 ?_
  intro b hb; exact common_sub_311 (mem_commonEnvelope childrenD_311 b hb)
end SnakyConditional

end OAI
