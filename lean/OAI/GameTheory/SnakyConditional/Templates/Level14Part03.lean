import OAI.GameTheory.SnakyConditional.Templates.Level13Part01
import OAI.GameTheory.SnakyConditional.Templates.Level13Part03

namespace OAI

namespace SnakyConditional
def required_393 : Finset Cell := ⟨(([(0, -2), (0, -1), (1, -2), (2, -3), (2, -2), (3, -2), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_393 : Finset Cell := ⟨(([(-2, 1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_393 : Fin 4 → Finset Cell := ![(placedSet 3 (0, 1) required_107), (placedSet 0 (2, -1) required_348), (placedSet 3 (0, 1) required_65), (placedSet 0 (0, 1) required_303)]
def childrenD_393 : Fin 4 → Finset Cell := ![(placedSet 3 (0, 1) envelope_107), (placedSet 0 (2, -1) envelope_348), (placedSet 3 (0, 1) envelope_65), (placedSet 0 (0, 1) envelope_303)]
theorem common_sub_393 : commonEnvelope childrenD_393 ⊆ insert (0, 0) required_393 := by decide
theorem child_required_sub_393 : ∀ j, childrenC_393 j ⊆ insert (0, 0) required_393 := by decide
theorem child_envelope_sub_393 : ∀ j, childrenD_393 j ⊆ envelope_393 := by decide
theorem pivot_mem_393 : (0, 0) ∈ envelope_393 := by decide
theorem children_work_393 : ∀ j, Template HasSnaky 11 (childrenC_393 j) (childrenD_393 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_107 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_348 0 (2, -1)).mono (by decide)
  · exact (placed_template_map row_works_65 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_303 0 (0, 1)).mono (by decide)
theorem row_works_393 : Template HasSnaky 12 required_393 envelope_393 := by
  refine compose HasSnaky 11 childrenC_393 childrenD_393 children_work_393 (0, 0)
    required_393 envelope_393 pivot_mem_393 child_required_sub_393 child_envelope_sub_393 ?_
  intro b hb; exact common_sub_393 (mem_commonEnvelope childrenD_393 b hb)
def required_402 : Finset Cell := ⟨(([(-1, -3), (0, -3), (0, -2), (1, -3), (2, -3), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_402 : Finset Cell := ⟨(([(-3, 1), (-2, -4), (-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -3), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_402 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, -4) required_29), (placedSet 0 (1, 0) required_384)]
def childrenD_402 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, -4) envelope_29), (placedSet 0 (1, 0) envelope_384)]
theorem common_sub_402 : commonEnvelope childrenD_402 ⊆ insert (0, 0) required_402 := by decide
theorem child_required_sub_402 : ∀ j, childrenC_402 j ⊆ insert (0, 0) required_402 := by decide
theorem child_envelope_sub_402 : ∀ j, childrenD_402 j ⊆ envelope_402 := by decide
theorem pivot_mem_402 : (0, 0) ∈ envelope_402 := by decide
theorem children_work_402 : ∀ j, Template HasSnaky 11 (childrenC_402 j) (childrenD_402 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_29 3 (-1, -4)).mono (by decide)
  · exact (placed_template_map row_works_384 0 (1, 0)).mono (by decide)
theorem row_works_402 : Template HasSnaky 12 required_402 envelope_402 := by
  refine compose HasSnaky 11 childrenC_402 childrenD_402 children_work_402 (0, 0)
    required_402 envelope_402 pivot_mem_402 child_required_sub_402 child_envelope_sub_402 ?_
  intro b hb; exact common_sub_402 (mem_commonEnvelope childrenD_402 b hb)
def required_403 : Finset Cell := ⟨(([(-1, -2), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_403 : Finset Cell := ⟨(([(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_403 : Fin 5 → Finset Cell := ![(placedSet 1 (0, 1) required_202), (placedSet 0 (0, 1) required_180), (placedSet 4 (1, 0) required_314), (placedSet 0 (-1, 1) required_63), (placedSet 0 (-1, 0) required_388)]
def childrenD_403 : Fin 5 → Finset Cell := ![(placedSet 1 (0, 1) envelope_202), (placedSet 0 (0, 1) envelope_180), (placedSet 4 (1, 0) envelope_314), (placedSet 0 (-1, 1) envelope_63), (placedSet 0 (-1, 0) envelope_388)]
theorem common_sub_403 : commonEnvelope childrenD_403 ⊆ insert (0, 0) required_403 := by decide
theorem child_required_sub_403 : ∀ j, childrenC_403 j ⊆ insert (0, 0) required_403 := by decide
theorem child_envelope_sub_403 : ∀ j, childrenD_403 j ⊆ envelope_403 := by decide
theorem pivot_mem_403 : (0, 0) ∈ envelope_403 := by decide
theorem children_work_403 : ∀ j, Template HasSnaky 11 (childrenC_403 j) (childrenD_403 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_202 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_180 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_314 4 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_63 0 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_388 0 (-1, 0)).mono (by decide)
theorem row_works_403 : Template HasSnaky 12 required_403 envelope_403 := by
  refine compose HasSnaky 11 childrenC_403 childrenD_403 children_work_403 (0, 0)
    required_403 envelope_403 pivot_mem_403 child_required_sub_403 child_envelope_sub_403 ?_
  intro b hb; exact common_sub_403 (mem_commonEnvelope childrenD_403 b hb)
def required_404 : Finset Cell := ⟨(([(-1, -1), (-1, 0), (-1, 1), (-1, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_404 : Finset Cell := ⟨(([(-6, 1), (-5, 1), (-5, 2), (-5, 3), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (4, 1), (4, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_404 : Fin 2 → Finset Cell := ![(placedSet 6 (-2, -1) required_82), (placedSet 4 (0, 2) required_388)]
def childrenD_404 : Fin 2 → Finset Cell := ![(placedSet 6 (-2, -1) envelope_82), (placedSet 4 (0, 2) envelope_388)]
theorem common_sub_404 : commonEnvelope childrenD_404 ⊆ insert (0, 0) required_404 := by decide
theorem child_required_sub_404 : ∀ j, childrenC_404 j ⊆ insert (0, 0) required_404 := by decide
theorem child_envelope_sub_404 : ∀ j, childrenD_404 j ⊆ envelope_404 := by decide
theorem pivot_mem_404 : (0, 0) ∈ envelope_404 := by decide
theorem children_work_404 : ∀ j, Template HasSnaky 11 (childrenC_404 j) (childrenD_404 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_82 6 (-2, -1)).mono (by decide)
  · exact (placed_template_map row_works_388 4 (0, 2)).mono (by decide)
theorem row_works_404 : Template HasSnaky 12 required_404 envelope_404 := by
  refine compose HasSnaky 11 childrenC_404 childrenD_404 children_work_404 (0, 0)
    required_404 envelope_404 pivot_mem_404 child_required_sub_404 child_envelope_sub_404 ?_
  intro b hb; exact common_sub_404 (mem_commonEnvelope childrenD_404 b hb)
end SnakyConditional

end OAI
