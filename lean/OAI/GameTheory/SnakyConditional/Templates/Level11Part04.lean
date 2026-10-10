import OAI.GameTheory.SnakyConditional.Templates.Level10Part01
import OAI.GameTheory.SnakyConditional.Templates.Level10Part04
import OAI.GameTheory.SnakyConditional.Templates.Level10Part05

namespace OAI

namespace SnakyConditional
def required_307 : Finset Cell := ⟨(([(-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_307 : Finset Cell := ⟨(([(-3, 1), (-2, 1), (-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_307 : Fin 2 → Finset Cell := ![(placedSet 7 (0, 2) required_0), (placedSet 0 (1, 1) required_273)]
def childrenD_307 : Fin 2 → Finset Cell := ![(placedSet 7 (0, 2) envelope_0), (placedSet 0 (1, 1) envelope_273)]
theorem common_sub_307 : commonEnvelope childrenD_307 ⊆ insert (0, 0) required_307 := by decide
theorem child_required_sub_307 : ∀ j, childrenC_307 j ⊆ insert (0, 0) required_307 := by decide
theorem child_envelope_sub_307 : ∀ j, childrenD_307 j ⊆ envelope_307 := by decide
theorem pivot_mem_307 : (0, 0) ∈ envelope_307 := by decide
theorem children_work_307 : ∀ j, Template HasSnaky 8 (childrenC_307 j) (childrenD_307 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 7 (0, 2)).mono (by decide)
  · exact (placed_template_map row_works_273 0 (1, 1)).mono (by decide)
theorem row_works_307 : Template HasSnaky 9 required_307 envelope_307 := by
  refine compose HasSnaky 8 childrenC_307 childrenD_307 children_work_307 (0, 0)
    required_307 envelope_307 pivot_mem_307 child_required_sub_307 child_envelope_sub_307 ?_
  intro b hb; exact common_sub_307 (mem_commonEnvelope childrenD_307 b hb)
def required_314 : Finset Cell := ⟨(([(1, -3), (1, -2), (1, -1), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_314 : Finset Cell := ⟨(([(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_314 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_6), (placedSet 0 (2, 0) required_305)]
def childrenD_314 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_6), (placedSet 0 (2, 0) envelope_305)]
theorem common_sub_314 : commonEnvelope childrenD_314 ⊆ insert (0, 0) required_314 := by decide
theorem child_required_sub_314 : ∀ j, childrenC_314 j ⊆ insert (0, 0) required_314 := by decide
theorem child_envelope_sub_314 : ∀ j, childrenD_314 j ⊆ envelope_314 := by decide
theorem pivot_mem_314 : (0, 0) ∈ envelope_314 := by decide
theorem children_work_314 : ∀ j, Template HasSnaky 8 (childrenC_314 j) (childrenD_314 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_305 0 (2, 0)).mono (by decide)
theorem row_works_314 : Template HasSnaky 9 required_314 envelope_314 := by
  refine compose HasSnaky 8 childrenC_314 childrenD_314 children_work_314 (0, 0)
    required_314 envelope_314 pivot_mem_314 child_required_sub_314 child_envelope_sub_314 ?_
  intro b hb; exact common_sub_314 (mem_commonEnvelope childrenD_314 b hb)
def required_316 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (1, 1), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_316 : Finset Cell := ⟨(([(-1, 0), (-1, 4), (-1, 5), (-1, 6), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 2), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_316 : Fin 2 → Finset Cell := ![(placedSet 6 (-1, 0) required_6), (placedSet 0 (1, 4) required_306)]
def childrenD_316 : Fin 2 → Finset Cell := ![(placedSet 6 (-1, 0) envelope_6), (placedSet 0 (1, 4) envelope_306)]
theorem common_sub_316 : commonEnvelope childrenD_316 ⊆ insert (0, 0) required_316 := by decide
theorem child_required_sub_316 : ∀ j, childrenC_316 j ⊆ insert (0, 0) required_316 := by decide
theorem child_envelope_sub_316 : ∀ j, childrenD_316 j ⊆ envelope_316 := by decide
theorem pivot_mem_316 : (0, 0) ∈ envelope_316 := by decide
theorem children_work_316 : ∀ j, Template HasSnaky 8 (childrenC_316 j) (childrenD_316 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 6 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_306 0 (1, 4)).mono (by decide)
theorem row_works_316 : Template HasSnaky 9 required_316 envelope_316 := by
  refine compose HasSnaky 8 childrenC_316 childrenD_316 children_work_316 (0, 0)
    required_316 envelope_316 pivot_mem_316 child_required_sub_316 child_envelope_sub_316 ?_
  intro b hb; exact common_sub_316 (mem_commonEnvelope childrenD_316 b hb)
def required_317 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (-1, 0), (0, -3), (0, -2), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_317 : Finset Cell := ⟨(([(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_317 : Fin 3 → Finset Cell := ![(placedSet 2 (2, 0) required_263), (placedSet 3 (0, -1) required_26), (placedSet 0 (1, 1) required_99)]
def childrenD_317 : Fin 3 → Finset Cell := ![(placedSet 2 (2, 0) envelope_263), (placedSet 3 (0, -1) envelope_26), (placedSet 0 (1, 1) envelope_99)]
theorem common_sub_317 : commonEnvelope childrenD_317 ⊆ insert (0, 0) required_317 := by decide
theorem child_required_sub_317 : ∀ j, childrenC_317 j ⊆ insert (0, 0) required_317 := by decide
theorem child_envelope_sub_317 : ∀ j, childrenD_317 j ⊆ envelope_317 := by decide
theorem pivot_mem_317 : (0, 0) ∈ envelope_317 := by decide
theorem children_work_317 : ∀ j, Template HasSnaky 8 (childrenC_317 j) (childrenD_317 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_263 2 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_26 3 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_99 0 (1, 1)).mono (by decide)
theorem row_works_317 : Template HasSnaky 9 required_317 envelope_317 := by
  refine compose HasSnaky 8 childrenC_317 childrenD_317 children_work_317 (0, 0)
    required_317 envelope_317 pivot_mem_317 child_required_sub_317 child_envelope_sub_317 ?_
  intro b hb; exact common_sub_317 (mem_commonEnvelope childrenD_317 b hb)
def required_320 : Finset Cell := ⟨(([(0, -3), (0, -2), (1, -3), (1, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_320 : Finset Cell := ⟨(([(-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (5, 0), (5, 1), (6, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_320 : Fin 3 → Finset Cell := ![(placedSet 1 (0, -1) required_19), (placedSet 2 (2, 0) required_267), (placedSet 7 (0, -1) required_115)]
def childrenD_320 : Fin 3 → Finset Cell := ![(placedSet 1 (0, -1) envelope_19), (placedSet 2 (2, 0) envelope_267), (placedSet 7 (0, -1) envelope_115)]
theorem common_sub_320 : commonEnvelope childrenD_320 ⊆ insert (0, 0) required_320 := by decide
theorem child_required_sub_320 : ∀ j, childrenC_320 j ⊆ insert (0, 0) required_320 := by decide
theorem child_envelope_sub_320 : ∀ j, childrenD_320 j ⊆ envelope_320 := by decide
theorem pivot_mem_320 : (0, 0) ∈ envelope_320 := by decide
theorem children_work_320 : ∀ j, Template HasSnaky 8 (childrenC_320 j) (childrenD_320 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_19 1 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_267 2 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_115 7 (0, -1)).mono (by decide)
theorem row_works_320 : Template HasSnaky 9 required_320 envelope_320 := by
  refine compose HasSnaky 8 childrenC_320 childrenD_320 children_work_320 (0, 0)
    required_320 envelope_320 pivot_mem_320 child_required_sub_320 child_envelope_sub_320 ?_
  intro b hb; exact common_sub_320 (mem_commonEnvelope childrenD_320 b hb)
def required_322 : Finset Cell := ⟨(([(-3, -3), (-3, -2), (-3, -1), (-2, -3), (-2, 0), (-1, -3), (0, -3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_322 : Finset Cell := ⟨(([(-4, 0), (-4, 1), (-4, 2), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, 0), (-2, 1), (-1, -3), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -4), (2, -2), (2, -1), (2, 0), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_322 : Fin 2 → Finset Cell := ![(placedSet 0 (-3, 0) required_96), (placedSet 1 (1, -2) required_205)]
def childrenD_322 : Fin 2 → Finset Cell := ![(placedSet 0 (-3, 0) envelope_96), (placedSet 1 (1, -2) envelope_205)]
theorem common_sub_322 : commonEnvelope childrenD_322 ⊆ insert (0, 0) required_322 := by decide
theorem child_required_sub_322 : ∀ j, childrenC_322 j ⊆ insert (0, 0) required_322 := by decide
theorem child_envelope_sub_322 : ∀ j, childrenD_322 j ⊆ envelope_322 := by decide
theorem pivot_mem_322 : (0, 0) ∈ envelope_322 := by decide
theorem children_work_322 : ∀ j, Template HasSnaky 8 (childrenC_322 j) (childrenD_322 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_96 0 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_205 1 (1, -2)).mono (by decide)
theorem row_works_322 : Template HasSnaky 9 required_322 envelope_322 := by
  refine compose HasSnaky 8 childrenC_322 childrenD_322 children_work_322 (0, 0)
    required_322 envelope_322 pivot_mem_322 child_required_sub_322 child_envelope_sub_322 ?_
  intro b hb; exact common_sub_322 (mem_commonEnvelope childrenD_322 b hb)
end SnakyConditional

end OAI
