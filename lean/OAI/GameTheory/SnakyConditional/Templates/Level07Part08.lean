import OAI.GameTheory.SnakyConditional.Templates.Level06Part01
import OAI.GameTheory.SnakyConditional.Templates.Level06Part06
import OAI.GameTheory.SnakyConditional.Templates.Level06Part07
import OAI.GameTheory.SnakyConditional.Templates.Level06Part08

namespace OAI

namespace SnakyConditional
def required_211 : Finset Cell := ⟨(([(-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_211 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_211 : Fin 2 → Finset Cell := ![(placedSet 5 (1, 0) required_49), (placedSet 6 (-4, -1) required_6)]
def childrenD_211 : Fin 2 → Finset Cell := ![(placedSet 5 (1, 0) envelope_49), (placedSet 6 (-4, -1) envelope_6)]
theorem common_sub_211 : commonEnvelope childrenD_211 ⊆ insert (0, 0) required_211 := by decide
theorem child_required_sub_211 : ∀ j, childrenC_211 j ⊆ insert (0, 0) required_211 := by decide
theorem child_envelope_sub_211 : ∀ j, childrenD_211 j ⊆ envelope_211 := by decide
theorem pivot_mem_211 : (0, 0) ∈ envelope_211 := by decide
theorem children_work_211 : ∀ j, Template HasSnaky 4 (childrenC_211 j) (childrenD_211 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_49 5 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_6 6 (-4, -1)).mono (by decide)
theorem row_works_211 : Template HasSnaky 5 required_211 envelope_211 := by
  refine compose HasSnaky 4 childrenC_211 childrenD_211 children_work_211 (0, 0)
    required_211 envelope_211 pivot_mem_211 child_required_sub_211 child_envelope_sub_211 ?_
  intro b hb; exact common_sub_211 (mem_commonEnvelope childrenD_211 b hb)
def required_280 : Finset Cell := ⟨(([(-3, -2), (-2, -3), (-2, -2), (-1, -2), (-1, 0), (-1, 1), (0, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_280 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -2), (-2, 0), (-2, 1), (-1, -2), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_280 : Fin 2 → Finset Cell := ![(placedSet 0 (-3, 1) required_184), (placedSet 2 (0, -1) required_116)]
def childrenD_280 : Fin 2 → Finset Cell := ![(placedSet 0 (-3, 1) envelope_184), (placedSet 2 (0, -1) envelope_116)]
theorem common_sub_280 : commonEnvelope childrenD_280 ⊆ insert (0, 0) required_280 := by decide
theorem child_required_sub_280 : ∀ j, childrenC_280 j ⊆ insert (0, 0) required_280 := by decide
theorem child_envelope_sub_280 : ∀ j, childrenD_280 j ⊆ envelope_280 := by decide
theorem pivot_mem_280 : (0, 0) ∈ envelope_280 := by decide
theorem children_work_280 : ∀ j, Template HasSnaky 4 (childrenC_280 j) (childrenD_280 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_184 0 (-3, 1)).mono (by decide)
  · exact (placed_template_map row_works_116 2 (0, -1)).mono (by decide)
theorem row_works_280 : Template HasSnaky 5 required_280 envelope_280 := by
  refine compose HasSnaky 4 childrenC_280 childrenD_280 children_work_280 (0, 0)
    required_280 envelope_280 pivot_mem_280 child_required_sub_280 child_envelope_sub_280 ?_
  intro b hb; exact common_sub_280 (mem_commonEnvelope childrenD_280 b hb)
def required_382 : Finset Cell := ⟨(([(-2, -2), (-1, -3), (-1, -2), (0, -2), (0, 1), (1, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_382 : Finset Cell := ⟨(([(-2, -2), (-1, -3), (-1, -2), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_382 : Fin 2 → Finset Cell := ![(placedSet 1 (1, -1) required_124), (placedSet 7 (0, -1) required_2)]
def childrenD_382 : Fin 2 → Finset Cell := ![(placedSet 1 (1, -1) envelope_124), (placedSet 7 (0, -1) envelope_2)]
theorem common_sub_382 : commonEnvelope childrenD_382 ⊆ insert (0, 0) required_382 := by decide
theorem child_required_sub_382 : ∀ j, childrenC_382 j ⊆ insert (0, 0) required_382 := by decide
theorem child_envelope_sub_382 : ∀ j, childrenD_382 j ⊆ envelope_382 := by decide
theorem pivot_mem_382 : (0, 0) ∈ envelope_382 := by decide
theorem children_work_382 : ∀ j, Template HasSnaky 4 (childrenC_382 j) (childrenD_382 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_124 1 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_2 7 (0, -1)).mono (by decide)
theorem row_works_382 : Template HasSnaky 5 required_382 envelope_382 := by
  refine compose HasSnaky 4 childrenC_382 childrenD_382 children_work_382 (0, 0)
    required_382 envelope_382 pivot_mem_382 child_required_sub_382 child_envelope_sub_382 ?_
  intro b hb; exact common_sub_382 (mem_commonEnvelope childrenD_382 b hb)
def required_455 : Finset Cell := ⟨(([(-3, -1), (-3, 0), (-3, 1), (-2, 1), (-1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_455 : Finset Cell := ⟨(([(-5, 2), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_455 : Fin 3 → Finset Cell := ![(placedSet 2 (0, 1) required_20), (placedSet 3 (-4, 1) required_118), (placedSet 2 (-1, 0) required_39)]
def childrenD_455 : Fin 3 → Finset Cell := ![(placedSet 2 (0, 1) envelope_20), (placedSet 3 (-4, 1) envelope_118), (placedSet 2 (-1, 0) envelope_39)]
theorem common_sub_455 : commonEnvelope childrenD_455 ⊆ insert (0, 0) required_455 := by decide
theorem child_required_sub_455 : ∀ j, childrenC_455 j ⊆ insert (0, 0) required_455 := by decide
theorem child_envelope_sub_455 : ∀ j, childrenD_455 j ⊆ envelope_455 := by decide
theorem pivot_mem_455 : (0, 0) ∈ envelope_455 := by decide
theorem children_work_455 : ∀ j, Template HasSnaky 4 (childrenC_455 j) (childrenD_455 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_20 2 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_118 3 (-4, 1)).mono (by decide)
  · exact (placed_template_map row_works_39 2 (-1, 0)).mono (by decide)
theorem row_works_455 : Template HasSnaky 5 required_455 envelope_455 := by
  refine compose HasSnaky 4 childrenC_455 childrenD_455 children_work_455 (0, 0)
    required_455 envelope_455 pivot_mem_455 child_required_sub_455 child_envelope_sub_455 ?_
  intro b hb; exact common_sub_455 (mem_commonEnvelope childrenD_455 b hb)
end SnakyConditional

end OAI
