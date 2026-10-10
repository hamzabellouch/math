import OAI.GameTheory.SnakyConditional.Templates.Level11Part02
import OAI.GameTheory.SnakyConditional.Templates.Level11Part03
import OAI.GameTheory.SnakyConditional.Templates.Level11Part04
import OAI.GameTheory.SnakyConditional.Templates.Level11Part05
import OAI.GameTheory.SnakyConditional.Templates.Level11Part07

namespace OAI

namespace SnakyConditional
def required_430 : Finset Cell := ⟨(([(-2, -2), (-2, -1), (-2, 0), (-1, -2), (0, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_430 : Finset Cell := ⟨(([(-7, -1), (-7, 1), (-6, -1), (-6, 0), (-6, 1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -3), (2, -1), (2, 0), (2, 1), (3, -3), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_430 : Fin 5 → Finset Cell := ![(placedSet 7 (-3, -1) required_277), (placedSet 4 (-1, 0) required_338), (placedSet 1 (0, -1) required_336), (placedSet 2 (0, -1) required_375), (placedSet 6 (-1, -3) required_277)]
def childrenD_430 : Fin 5 → Finset Cell := ![(placedSet 7 (-3, -1) envelope_277), (placedSet 4 (-1, 0) envelope_338), (placedSet 1 (0, -1) envelope_336), (placedSet 2 (0, -1) envelope_375), (placedSet 6 (-1, -3) envelope_277)]
theorem common_sub_430 : commonEnvelope childrenD_430 ⊆ insert (0, 0) required_430 := by decide
theorem child_required_sub_430 : ∀ j, childrenC_430 j ⊆ insert (0, 0) required_430 := by decide
theorem child_envelope_sub_430 : ∀ j, childrenD_430 j ⊆ envelope_430 := by decide
theorem pivot_mem_430 : (0, 0) ∈ envelope_430 := by decide
theorem children_work_430 : ∀ j, Template HasSnaky 9 (childrenC_430 j) (childrenD_430 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_277 7 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_338 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_336 1 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_375 2 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_277 6 (-1, -3)).mono (by decide)
theorem row_works_430 : Template HasSnaky 10 required_430 envelope_430 := by
  refine compose HasSnaky 9 childrenC_430 childrenD_430 children_work_430 (0, 0)
    required_430 envelope_430 pivot_mem_430 child_required_sub_430 child_envelope_sub_430 ?_
  intro b hb; exact common_sub_430 (mem_commonEnvelope childrenD_430 b hb)
def required_465 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_465 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_465 : Fin 3 → Finset Cell := ![(placedSet 3 (0, 1) required_55), (placedSet 0 (-1, 0) required_285), (placedSet 1 (-1, -3) required_64)]
def childrenD_465 : Fin 3 → Finset Cell := ![(placedSet 3 (0, 1) envelope_55), (placedSet 0 (-1, 0) envelope_285), (placedSet 1 (-1, -3) envelope_64)]
theorem common_sub_465 : commonEnvelope childrenD_465 ⊆ insert (0, 0) required_465 := by decide
theorem child_required_sub_465 : ∀ j, childrenC_465 j ⊆ insert (0, 0) required_465 := by decide
theorem child_envelope_sub_465 : ∀ j, childrenD_465 j ⊆ envelope_465 := by decide
theorem pivot_mem_465 : (0, 0) ∈ envelope_465 := by decide
theorem children_work_465 : ∀ j, Template HasSnaky 9 (childrenC_465 j) (childrenD_465 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_55 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_285 0 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_64 1 (-1, -3)).mono (by decide)
theorem row_works_465 : Template HasSnaky 10 required_465 envelope_465 := by
  refine compose HasSnaky 9 childrenC_465 childrenD_465 children_work_465 (0, 0)
    required_465 envelope_465 pivot_mem_465 child_required_sub_465 child_envelope_sub_465 ?_
  intro b hb; exact common_sub_465 (mem_commonEnvelope childrenD_465 b hb)
def required_501 : Finset Cell := ⟨(([(-3, 0), (-3, 1), (-3, 2), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_501 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-4, 3), (-4, 4), (-4, 5), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 3), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 1), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_501 : Fin 2 → Finset Cell := ![(placedSet 4 (-4, 1) required_6), (placedSet 0 (-3, -1) required_316)]
def childrenD_501 : Fin 2 → Finset Cell := ![(placedSet 4 (-4, 1) envelope_6), (placedSet 0 (-3, -1) envelope_316)]
theorem common_sub_501 : commonEnvelope childrenD_501 ⊆ insert (0, 0) required_501 := by decide
theorem child_required_sub_501 : ∀ j, childrenC_501 j ⊆ insert (0, 0) required_501 := by decide
theorem child_envelope_sub_501 : ∀ j, childrenD_501 j ⊆ envelope_501 := by decide
theorem pivot_mem_501 : (0, 0) ∈ envelope_501 := by decide
theorem children_work_501 : ∀ j, Template HasSnaky 9 (childrenC_501 j) (childrenD_501 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 4 (-4, 1)).mono (by decide)
  · exact (placed_template_map row_works_316 0 (-3, -1)).mono (by decide)
theorem row_works_501 : Template HasSnaky 10 required_501 envelope_501 := by
  refine compose HasSnaky 9 childrenC_501 childrenD_501 children_work_501 (0, 0)
    required_501 envelope_501 pivot_mem_501 child_required_sub_501 child_envelope_sub_501 ?_
  intro b hb; exact common_sub_501 (mem_commonEnvelope childrenD_501 b hb)
def required_511 : Finset Cell := ⟨(([(-3, -2), (-2, -2), (-1, -2), (-1, -1), (-1, 0), (0, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_511 : Finset Cell := ⟨(([(-6, -1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, -1), (1, 0), (1, 1), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_511 : Fin 3 → Finset Cell := ![(placedSet 1 (0, 1) required_15), (placedSet 0 (1, -1) required_331), (placedSet 4 (-2, 0) required_380)]
def childrenD_511 : Fin 3 → Finset Cell := ![(placedSet 1 (0, 1) envelope_15), (placedSet 0 (1, -1) envelope_331), (placedSet 4 (-2, 0) envelope_380)]
theorem common_sub_511 : commonEnvelope childrenD_511 ⊆ insert (0, 0) required_511 := by decide
theorem child_required_sub_511 : ∀ j, childrenC_511 j ⊆ insert (0, 0) required_511 := by decide
theorem child_envelope_sub_511 : ∀ j, childrenD_511 j ⊆ envelope_511 := by decide
theorem pivot_mem_511 : (0, 0) ∈ envelope_511 := by decide
theorem children_work_511 : ∀ j, Template HasSnaky 9 (childrenC_511 j) (childrenD_511 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_15 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_331 0 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_380 4 (-2, 0)).mono (by decide)
theorem row_works_511 : Template HasSnaky 10 required_511 envelope_511 := by
  refine compose HasSnaky 9 childrenC_511 childrenD_511 children_work_511 (0, 0)
    required_511 envelope_511 pivot_mem_511 child_required_sub_511 child_envelope_sub_511 ?_
  intro b hb; exact common_sub_511 (mem_commonEnvelope childrenD_511 b hb)
end SnakyConditional

end OAI
