import OAI.GameTheory.SnakyConditional.Templates.Level14Part04
import OAI.GameTheory.SnakyConditional.Templates.Level14Part06

namespace OAI

namespace SnakyConditional
def required_431 : Finset Cell := ⟨(([(-1, -4), (-1, -3), (-1, -2), (0, -3), (1, -3), (2, -3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_431 : Finset Cell := ⟨(([(-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (6, -2), (6, -1), (6, 0), (6, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_431 : Fin 4 → Finset Cell := ![(placedSet 4 (-1, -1) required_73), (placedSet 1 (1, -2) required_302), (placedSet 0 (2, 0) required_415), (placedSet 0 (2, 0) required_398)]
def childrenD_431 : Fin 4 → Finset Cell := ![(placedSet 4 (-1, -1) envelope_73), (placedSet 1 (1, -2) envelope_302), (placedSet 0 (2, 0) envelope_415), (placedSet 0 (2, 0) envelope_398)]
theorem common_sub_431 : commonEnvelope childrenD_431 ⊆ insert (0, 0) required_431 := by decide
theorem child_required_sub_431 : ∀ j, childrenC_431 j ⊆ insert (0, 0) required_431 := by decide
theorem child_envelope_sub_431 : ∀ j, childrenD_431 j ⊆ envelope_431 := by decide
theorem pivot_mem_431 : (0, 0) ∈ envelope_431 := by decide
theorem children_work_431 : ∀ j, Template HasSnaky 12 (childrenC_431 j) (childrenD_431 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_73 4 (-1, -1)).mono (by decide)
  · exact (placed_template_map row_works_302 1 (1, -2)).mono (by decide)
  · exact (placed_template_map row_works_415 0 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_398 0 (2, 0)).mono (by decide)
theorem row_works_431 : Template HasSnaky 13 required_431 envelope_431 := by
  refine compose HasSnaky 12 childrenC_431 childrenD_431 children_work_431 (0, 0)
    required_431 envelope_431 pivot_mem_431 child_required_sub_431 child_envelope_sub_431 ?_
  intro b hb; exact common_sub_431 (mem_commonEnvelope childrenD_431 b hb)
def required_485 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (0, -3), (0, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_485 : Finset Cell := ⟨(([(-4, 1), (-3, -1), (-3, 1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_485 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) required_484), (placedSet 3 (0, -1) required_2)]
def childrenD_485 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) envelope_484), (placedSet 3 (0, -1) envelope_2)]
theorem common_sub_485 : commonEnvelope childrenD_485 ⊆ insert (0, 0) required_485 := by decide
theorem child_required_sub_485 : ∀ j, childrenC_485 j ⊆ insert (0, 0) required_485 := by decide
theorem child_envelope_sub_485 : ∀ j, childrenD_485 j ⊆ envelope_485 := by decide
theorem pivot_mem_485 : (0, 0) ∈ envelope_485 := by decide
theorem children_work_485 : ∀ j, Template HasSnaky 12 (childrenC_485 j) (childrenD_485 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_484 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_2 3 (0, -1)).mono (by decide)
theorem row_works_485 : Template HasSnaky 13 required_485 envelope_485 := by
  refine compose HasSnaky 12 childrenC_485 childrenD_485 children_work_485 (0, 0)
    required_485 envelope_485 pivot_mem_485 child_required_sub_485 child_envelope_sub_485 ?_
  intro b hb; exact common_sub_485 (mem_commonEnvelope childrenD_485 b hb)
def required_492 : Finset Cell := ⟨(([(1, 0), (1, 2), (1, 3), (2, -1), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_492 : Finset Cell := ⟨(([(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 1), (6, 3), (6, 4), (7, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_492 : Fin 3 → Finset Cell := ![(placedSet 4 (-1, 0) required_62), (placedSet 4 (-1, 0) required_107), (placedSet 0 (2, 2) required_487)]
def childrenD_492 : Fin 3 → Finset Cell := ![(placedSet 4 (-1, 0) envelope_62), (placedSet 4 (-1, 0) envelope_107), (placedSet 0 (2, 2) envelope_487)]
theorem common_sub_492 : commonEnvelope childrenD_492 ⊆ insert (0, 0) required_492 := by decide
theorem child_required_sub_492 : ∀ j, childrenC_492 j ⊆ insert (0, 0) required_492 := by decide
theorem child_envelope_sub_492 : ∀ j, childrenD_492 j ⊆ envelope_492 := by decide
theorem pivot_mem_492 : (0, 0) ∈ envelope_492 := by decide
theorem children_work_492 : ∀ j, Template HasSnaky 12 (childrenC_492 j) (childrenD_492 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_62 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_107 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_487 0 (2, 2)).mono (by decide)
theorem row_works_492 : Template HasSnaky 13 required_492 envelope_492 := by
  refine compose HasSnaky 12 childrenC_492 childrenD_492 children_work_492 (0, 0)
    required_492 envelope_492 pivot_mem_492 child_required_sub_492 child_envelope_sub_492 ?_
  intro b hb; exact common_sub_492 (mem_commonEnvelope childrenD_492 b hb)
end SnakyConditional

end OAI
