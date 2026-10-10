import OAI.GameTheory.SnakyConditional.Templates.Level09Part01
import OAI.GameTheory.SnakyConditional.Templates.Level09Part02
import OAI.GameTheory.SnakyConditional.Templates.Level09Part04
import OAI.GameTheory.SnakyConditional.Templates.Level09Part05

namespace OAI

namespace SnakyConditional
def required_260 : Finset Cell := ⟨(([(0, -2), (0, -1), (0, 1), (1, -2), (1, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_260 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_260 : Fin 2 → Finset Cell := ![(placedSet 5 (0, 2) required_0), (placedSet 0 (-1, 1) required_231)]
def childrenD_260 : Fin 2 → Finset Cell := ![(placedSet 5 (0, 2) envelope_0), (placedSet 0 (-1, 1) envelope_231)]
theorem common_sub_260 : commonEnvelope childrenD_260 ⊆ insert (0, 0) required_260 := by decide
theorem child_required_sub_260 : ∀ j, childrenC_260 j ⊆ insert (0, 0) required_260 := by decide
theorem child_envelope_sub_260 : ∀ j, childrenD_260 j ⊆ envelope_260 := by decide
theorem pivot_mem_260 : (0, 0) ∈ envelope_260 := by decide
theorem children_work_260 : ∀ j, Template HasSnaky 7 (childrenC_260 j) (childrenD_260 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 5 (0, 2)).mono (by decide)
  · exact (placed_template_map row_works_231 0 (-1, 1)).mono (by decide)
theorem row_works_260 : Template HasSnaky 8 required_260 envelope_260 := by
  refine compose HasSnaky 7 childrenC_260 childrenD_260 children_work_260 (0, 0)
    required_260 envelope_260 pivot_mem_260 child_required_sub_260 child_envelope_sub_260 ?_
  intro b hb; exact common_sub_260 (mem_commonEnvelope childrenD_260 b hb)
def required_263 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_263 : Finset Cell := ⟨(([(-6, -1), (-5, -1), (-5, 0), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_263 : Fin 4 → Finset Cell := ![(placedSet 6 (-4, 0) required_144), (placedSet 0 (-3, -1) required_143), (placedSet 0 (1, 0) required_175), (placedSet 6 (-4, 0) required_55)]
def childrenD_263 : Fin 4 → Finset Cell := ![(placedSet 6 (-4, 0) envelope_144), (placedSet 0 (-3, -1) envelope_143), (placedSet 0 (1, 0) envelope_175), (placedSet 6 (-4, 0) envelope_55)]
theorem common_sub_263 : commonEnvelope childrenD_263 ⊆ insert (0, 0) required_263 := by decide
theorem child_required_sub_263 : ∀ j, childrenC_263 j ⊆ insert (0, 0) required_263 := by decide
theorem child_envelope_sub_263 : ∀ j, childrenD_263 j ⊆ envelope_263 := by decide
theorem pivot_mem_263 : (0, 0) ∈ envelope_263 := by decide
theorem children_work_263 : ∀ j, Template HasSnaky 7 (childrenC_263 j) (childrenD_263 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_144 6 (-4, 0)).mono (by decide)
  · exact (placed_template_map row_works_143 0 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_175 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_55 6 (-4, 0)).mono (by decide)
theorem row_works_263 : Template HasSnaky 8 required_263 envelope_263 := by
  refine compose HasSnaky 7 childrenC_263 childrenD_263 children_work_263 (0, 0)
    required_263 envelope_263 pivot_mem_263 child_required_sub_263 child_envelope_sub_263 ?_
  intro b hb; exact common_sub_263 (mem_commonEnvelope childrenD_263 b hb)
def required_267 : Finset Cell := ⟨(([(-2, 0), (-1, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_267 : Finset Cell := ⟨(([(-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_267 : Fin 4 → Finset Cell := ![(placedSet 4 (-3, 0) required_175), (placedSet 2 (2, 0) required_144), (placedSet 2 (2, 0) required_55), (placedSet 4 (1, -1) required_143)]
def childrenD_267 : Fin 4 → Finset Cell := ![(placedSet 4 (-3, 0) envelope_175), (placedSet 2 (2, 0) envelope_144), (placedSet 2 (2, 0) envelope_55), (placedSet 4 (1, -1) envelope_143)]
theorem common_sub_267 : commonEnvelope childrenD_267 ⊆ insert (0, 0) required_267 := by decide
theorem child_required_sub_267 : ∀ j, childrenC_267 j ⊆ insert (0, 0) required_267 := by decide
theorem child_envelope_sub_267 : ∀ j, childrenD_267 j ⊆ envelope_267 := by decide
theorem pivot_mem_267 : (0, 0) ∈ envelope_267 := by decide
theorem children_work_267 : ∀ j, Template HasSnaky 7 (childrenC_267 j) (childrenD_267 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_175 4 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_144 2 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_55 2 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_143 4 (1, -1)).mono (by decide)
theorem row_works_267 : Template HasSnaky 8 required_267 envelope_267 := by
  refine compose HasSnaky 7 childrenC_267 childrenD_267 children_work_267 (0, 0)
    required_267 envelope_267 pivot_mem_267 child_required_sub_267 child_envelope_sub_267 ?_
  intro b hb; exact common_sub_267 (mem_commonEnvelope childrenD_267 b hb)
def required_269 : Finset Cell := ⟨(([(-1, 1), (-1, 3), (0, 1), (1, 1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_269 : Finset Cell := ⟨(([(-2, 2), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 1), (2, 2), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_269 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, 2) required_28), (placedSet 0 (3, 1) required_202)]
def childrenD_269 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, 2) envelope_28), (placedSet 0 (3, 1) envelope_202)]
theorem common_sub_269 : commonEnvelope childrenD_269 ⊆ insert (0, 0) required_269 := by decide
theorem child_required_sub_269 : ∀ j, childrenC_269 j ⊆ insert (0, 0) required_269 := by decide
theorem child_envelope_sub_269 : ∀ j, childrenD_269 j ⊆ envelope_269 := by decide
theorem pivot_mem_269 : (0, 0) ∈ envelope_269 := by decide
theorem children_work_269 : ∀ j, Template HasSnaky 7 (childrenC_269 j) (childrenD_269 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_28 3 (-1, 2)).mono (by decide)
  · exact (placed_template_map row_works_202 0 (3, 1)).mono (by decide)
theorem row_works_269 : Template HasSnaky 8 required_269 envelope_269 := by
  refine compose HasSnaky 7 childrenC_269 childrenD_269 children_work_269 (0, 0)
    required_269 envelope_269 pivot_mem_269 child_required_sub_269 child_envelope_sub_269 ?_
  intro b hb; exact common_sub_269 (mem_commonEnvelope childrenD_269 b hb)
def required_273 : Finset Cell := ⟨(([(-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_273 : Finset Cell := ⟨(([(-4, 0), (-3, 0), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_273 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_6), (placedSet 0 (1, 0) required_223)]
def childrenD_273 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_6), (placedSet 0 (1, 0) envelope_223)]
theorem common_sub_273 : commonEnvelope childrenD_273 ⊆ insert (0, 0) required_273 := by decide
theorem child_required_sub_273 : ∀ j, childrenC_273 j ⊆ insert (0, 0) required_273 := by decide
theorem child_envelope_sub_273 : ∀ j, childrenD_273 j ⊆ envelope_273 := by decide
theorem pivot_mem_273 : (0, 0) ∈ envelope_273 := by decide
theorem children_work_273 : ∀ j, Template HasSnaky 7 (childrenC_273 j) (childrenD_273 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_223 0 (1, 0)).mono (by decide)
theorem row_works_273 : Template HasSnaky 8 required_273 envelope_273 := by
  refine compose HasSnaky 7 childrenC_273 childrenD_273 children_work_273 (0, 0)
    required_273 envelope_273 pivot_mem_273 child_required_sub_273 child_envelope_sub_273 ?_
  intro b hb; exact common_sub_273 (mem_commonEnvelope childrenD_273 b hb)
def required_279 : Finset Cell := ⟨(([(1, -3), (1, -2), (1, -1), (1, 0), (2, -3), (2, -2), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_279 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -3), (2, -2), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_279 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_6), (placedSet 5 (3, 0) required_234)]
def childrenD_279 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_6), (placedSet 5 (3, 0) envelope_234)]
theorem common_sub_279 : commonEnvelope childrenD_279 ⊆ insert (0, 0) required_279 := by decide
theorem child_required_sub_279 : ∀ j, childrenC_279 j ⊆ insert (0, 0) required_279 := by decide
theorem child_envelope_sub_279 : ∀ j, childrenD_279 j ⊆ envelope_279 := by decide
theorem pivot_mem_279 : (0, 0) ∈ envelope_279 := by decide
theorem children_work_279 : ∀ j, Template HasSnaky 7 (childrenC_279 j) (childrenD_279 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_234 5 (3, 0)).mono (by decide)
theorem row_works_279 : Template HasSnaky 8 required_279 envelope_279 := by
  refine compose HasSnaky 7 childrenC_279 childrenD_279 children_work_279 (0, 0)
    required_279 envelope_279 pivot_mem_279 child_required_sub_279 child_envelope_sub_279 ?_
  intro b hb; exact common_sub_279 (mem_commonEnvelope childrenD_279 b hb)
def required_290 : Finset Cell := ⟨(([(-2, -1), (-1, -2), (-1, -1), (0, -2), (0, -1), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_290 : Finset Cell := ⟨(([(-4, 0), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -2), (3, -2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_290 : Fin 2 → Finset Cell := ![(placedSet 2 (1, -2) required_67), (placedSet 4 (1, 1) required_231)]
def childrenD_290 : Fin 2 → Finset Cell := ![(placedSet 2 (1, -2) envelope_67), (placedSet 4 (1, 1) envelope_231)]
theorem common_sub_290 : commonEnvelope childrenD_290 ⊆ insert (0, 0) required_290 := by decide
theorem child_required_sub_290 : ∀ j, childrenC_290 j ⊆ insert (0, 0) required_290 := by decide
theorem child_envelope_sub_290 : ∀ j, childrenD_290 j ⊆ envelope_290 := by decide
theorem pivot_mem_290 : (0, 0) ∈ envelope_290 := by decide
theorem children_work_290 : ∀ j, Template HasSnaky 7 (childrenC_290 j) (childrenD_290 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_67 2 (1, -2)).mono (by decide)
  · exact (placed_template_map row_works_231 4 (1, 1)).mono (by decide)
theorem row_works_290 : Template HasSnaky 8 required_290 envelope_290 := by
  refine compose HasSnaky 7 childrenC_290 childrenD_290 children_work_290 (0, 0)
    required_290 envelope_290 pivot_mem_290 child_required_sub_290 child_envelope_sub_290 ?_
  intro b hb; exact common_sub_290 (mem_commonEnvelope childrenD_290 b hb)
end SnakyConditional

end OAI
