import OAI.GameTheory.SnakyConditional.Templates.Level13Part01
import OAI.GameTheory.SnakyConditional.Templates.Level13Part05
import OAI.GameTheory.SnakyConditional.Templates.Level13Part06

namespace OAI

namespace SnakyConditional
def required_484 : Finset Cell := ⟨(([(-2, 0), (-2, 1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_484 : Finset Cell := ⟨(([(-5, 1), (-4, -1), (-4, 1), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-2, 2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_484 : Fin 4 → Finset Cell := ![(placedSet 4 (-3, 1) required_25), (placedSet 2 (1, 0) required_107), (placedSet 3 (-3, 1) required_349), (placedSet 2 (1, 0) required_163)]
def childrenD_484 : Fin 4 → Finset Cell := ![(placedSet 4 (-3, 1) envelope_25), (placedSet 2 (1, 0) envelope_107), (placedSet 3 (-3, 1) envelope_349), (placedSet 2 (1, 0) envelope_163)]
theorem common_sub_484 : commonEnvelope childrenD_484 ⊆ insert (0, 0) required_484 := by decide
theorem child_required_sub_484 : ∀ j, childrenC_484 j ⊆ insert (0, 0) required_484 := by decide
theorem child_envelope_sub_484 : ∀ j, childrenD_484 j ⊆ envelope_484 := by decide
theorem pivot_mem_484 : (0, 0) ∈ envelope_484 := by decide
theorem children_work_484 : ∀ j, Template HasSnaky 11 (childrenC_484 j) (childrenD_484 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_25 4 (-3, 1)).mono (by decide)
  · exact (placed_template_map row_works_107 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_349 3 (-3, 1)).mono (by decide)
  · exact (placed_template_map row_works_163 2 (1, 0)).mono (by decide)
theorem row_works_484 : Template HasSnaky 12 required_484 envelope_484 := by
  refine compose HasSnaky 11 childrenC_484 childrenD_484 children_work_484 (0, 0)
    required_484 envelope_484 pivot_mem_484 child_required_sub_484 child_envelope_sub_484 ?_
  intro b hb; exact common_sub_484 (mem_commonEnvelope childrenD_484 b hb)
def required_487 : Finset Cell := ⟨(([(-2, -2), (-1, 0), (-1, 1), (0, -3), (0, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_487 : Finset Cell := ⟨(([(-4, 0), (-3, -1), (-3, 0), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1), (4, 2), (5, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_487 : Fin 2 → Finset Cell := ![(placedSet 3 (0, -1) required_2), (placedSet 0 (1, 0) required_481)]
def childrenD_487 : Fin 2 → Finset Cell := ![(placedSet 3 (0, -1) envelope_2), (placedSet 0 (1, 0) envelope_481)]
theorem common_sub_487 : commonEnvelope childrenD_487 ⊆ insert (0, 0) required_487 := by decide
theorem child_required_sub_487 : ∀ j, childrenC_487 j ⊆ insert (0, 0) required_487 := by decide
theorem child_envelope_sub_487 : ∀ j, childrenD_487 j ⊆ envelope_487 := by decide
theorem pivot_mem_487 : (0, 0) ∈ envelope_487 := by decide
theorem children_work_487 : ∀ j, Template HasSnaky 11 (childrenC_487 j) (childrenD_487 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_2 3 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_481 0 (1, 0)).mono (by decide)
theorem row_works_487 : Template HasSnaky 12 required_487 envelope_487 := by
  refine compose HasSnaky 11 childrenC_487 childrenD_487 children_work_487 (0, 0)
    required_487 envelope_487 pivot_mem_487 child_required_sub_487 child_envelope_sub_487 ?_
  intro b hb; exact common_sub_487 (mem_commonEnvelope childrenD_487 b hb)
def required_496 : Finset Cell := ⟨(([(1, 0), (2, 0), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_496 : Finset Cell := ⟨(([(-3, -1), (-3, 1), (-3, 2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_496 : Fin 4 → Finset Cell := ![(placedSet 0 (3, 1) required_25), (placedSet 6 (-1, 0) required_107), (placedSet 6 (-1, 0) required_163), (placedSet 0 (3, 0) required_494)]
def childrenD_496 : Fin 4 → Finset Cell := ![(placedSet 0 (3, 1) envelope_25), (placedSet 6 (-1, 0) envelope_107), (placedSet 6 (-1, 0) envelope_163), (placedSet 0 (3, 0) envelope_494)]
theorem common_sub_496 : commonEnvelope childrenD_496 ⊆ insert (0, 0) required_496 := by decide
theorem child_required_sub_496 : ∀ j, childrenC_496 j ⊆ insert (0, 0) required_496 := by decide
theorem child_envelope_sub_496 : ∀ j, childrenD_496 j ⊆ envelope_496 := by decide
theorem pivot_mem_496 : (0, 0) ∈ envelope_496 := by decide
theorem children_work_496 : ∀ j, Template HasSnaky 11 (childrenC_496 j) (childrenD_496 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_25 0 (3, 1)).mono (by decide)
  · exact (placed_template_map row_works_107 6 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_163 6 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_494 0 (3, 0)).mono (by decide)
theorem row_works_496 : Template HasSnaky 12 required_496 envelope_496 := by
  refine compose HasSnaky 11 childrenC_496 childrenD_496 children_work_496 (0, 0)
    required_496 envelope_496 pivot_mem_496 child_required_sub_496 child_envelope_sub_496 ?_
  intro b hb; exact common_sub_496 (mem_commonEnvelope childrenD_496 b hb)
def required_500 : Finset Cell := ⟨(([(-1, -1), (-1, 0), (-1, 1), (-1, 3), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_500 : Finset Cell := ⟨(([(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_500 : Fin 2 → Finset Cell := ![(placedSet 5 (-1, 2) required_1), (placedSet 0 (1, 0) required_351)]
def childrenD_500 : Fin 2 → Finset Cell := ![(placedSet 5 (-1, 2) envelope_1), (placedSet 0 (1, 0) envelope_351)]
theorem common_sub_500 : commonEnvelope childrenD_500 ⊆ insert (0, 0) required_500 := by decide
theorem child_required_sub_500 : ∀ j, childrenC_500 j ⊆ insert (0, 0) required_500 := by decide
theorem child_envelope_sub_500 : ∀ j, childrenD_500 j ⊆ envelope_500 := by decide
theorem pivot_mem_500 : (0, 0) ∈ envelope_500 := by decide
theorem children_work_500 : ∀ j, Template HasSnaky 11 (childrenC_500 j) (childrenD_500 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_1 5 (-1, 2)).mono (by decide)
  · exact (placed_template_map row_works_351 0 (1, 0)).mono (by decide)
theorem row_works_500 : Template HasSnaky 12 required_500 envelope_500 := by
  refine compose HasSnaky 11 childrenC_500 childrenD_500 children_work_500 (0, 0)
    required_500 envelope_500 pivot_mem_500 child_required_sub_500 child_envelope_sub_500 ?_
  intro b hb; exact common_sub_500 (mem_commonEnvelope childrenD_500 b hb)
end SnakyConditional

end OAI
