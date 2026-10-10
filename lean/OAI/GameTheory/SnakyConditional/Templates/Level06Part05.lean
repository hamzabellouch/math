import OAI.GameTheory.SnakyConditional.Templates.Level05Part02
import OAI.GameTheory.SnakyConditional.Templates.Level05Part03
import OAI.GameTheory.SnakyConditional.Templates.Level05Part06

namespace OAI

namespace SnakyConditional
def required_93 : Finset Cell := ⟨(([(1, -4), (1, -3), (1, -2), (1, -1), (2, 0), (3, -1), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_93 : Finset Cell := ⟨(([(0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (3, -1), (3, 0), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_93 : Fin 2 → Finset Cell := ![(placedSet 3 (0, -1) required_4), (placedSet 0 (1, 0) required_47)]
def childrenD_93 : Fin 2 → Finset Cell := ![(placedSet 3 (0, -1) envelope_4), (placedSet 0 (1, 0) envelope_47)]
theorem common_sub_93 : commonEnvelope childrenD_93 ⊆ insert (0, 0) required_93 := by decide
theorem child_required_sub_93 : ∀ j, childrenC_93 j ⊆ insert (0, 0) required_93 := by decide
theorem child_envelope_sub_93 : ∀ j, childrenD_93 j ⊆ envelope_93 := by decide
theorem pivot_mem_93 : (0, 0) ∈ envelope_93 := by decide
theorem children_work_93 : ∀ j, Template HasSnaky 3 (childrenC_93 j) (childrenD_93 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_4 3 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_47 0 (1, 0)).mono (by decide)
theorem row_works_93 : Template HasSnaky 4 required_93 envelope_93 := by
  refine compose HasSnaky 3 childrenC_93 childrenD_93 children_work_93 (0, 0)
    required_93 envelope_93 pivot_mem_93 child_required_sub_93 child_envelope_sub_93 ?_
  intro b hb; exact common_sub_93 (mem_commonEnvelope childrenD_93 b hb)
def required_94 : Finset Cell := ⟨(([(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_94 : Finset Cell := ⟨(([(-2, -2), (-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_94 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_6), (placedSet 3 (-1, 2) required_27)]
def childrenD_94 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_6), (placedSet 3 (-1, 2) envelope_27)]
theorem common_sub_94 : commonEnvelope childrenD_94 ⊆ insert (0, 0) required_94 := by decide
theorem child_required_sub_94 : ∀ j, childrenC_94 j ⊆ insert (0, 0) required_94 := by decide
theorem child_envelope_sub_94 : ∀ j, childrenD_94 j ⊆ envelope_94 := by decide
theorem pivot_mem_94 : (0, 0) ∈ envelope_94 := by decide
theorem children_work_94 : ∀ j, Template HasSnaky 3 (childrenC_94 j) (childrenD_94 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_27 3 (-1, 2)).mono (by decide)
theorem row_works_94 : Template HasSnaky 4 required_94 envelope_94 := by
  refine compose HasSnaky 3 childrenC_94 childrenD_94 children_work_94 (0, 0)
    required_94 envelope_94 pivot_mem_94 child_required_sub_94 child_envelope_sub_94 ?_
  intro b hb; exact common_sub_94 (mem_commonEnvelope childrenD_94 b hb)
def required_95 : Finset Cell := ⟨(([(-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -1), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_95 : Finset Cell := ⟨(([(-2, 1), (-2, 2), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_95 : Fin 2 → Finset Cell := ![(placedSet 5 (-1, 3) required_0), (placedSet 0 (-2, 1) required_29)]
def childrenD_95 : Fin 2 → Finset Cell := ![(placedSet 5 (-1, 3) envelope_0), (placedSet 0 (-2, 1) envelope_29)]
theorem common_sub_95 : commonEnvelope childrenD_95 ⊆ insert (0, 0) required_95 := by decide
theorem child_required_sub_95 : ∀ j, childrenC_95 j ⊆ insert (0, 0) required_95 := by decide
theorem child_envelope_sub_95 : ∀ j, childrenD_95 j ⊆ envelope_95 := by decide
theorem pivot_mem_95 : (0, 0) ∈ envelope_95 := by decide
theorem children_work_95 : ∀ j, Template HasSnaky 3 (childrenC_95 j) (childrenD_95 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 5 (-1, 3)).mono (by decide)
  · exact (placed_template_map row_works_29 0 (-2, 1)).mono (by decide)
theorem row_works_95 : Template HasSnaky 4 required_95 envelope_95 := by
  refine compose HasSnaky 3 childrenC_95 childrenD_95 children_work_95 (0, 0)
    required_95 envelope_95 pivot_mem_95 child_required_sub_95 child_envelope_sub_95 ?_
  intro b hb; exact common_sub_95 (mem_commonEnvelope childrenD_95 b hb)
def required_99 : Finset Cell := ⟨(([(-2, -1), (-1, -4), (-1, -3), (-1, -1), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_99 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (0, -1), (0, 0), (1, -1), (1, 0), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_99 : Fin 2 → Finset Cell := ![(placedSet 1 (-1, -2) required_2), (placedSet 0 (1, 0) required_24)]
def childrenD_99 : Fin 2 → Finset Cell := ![(placedSet 1 (-1, -2) envelope_2), (placedSet 0 (1, 0) envelope_24)]
theorem common_sub_99 : commonEnvelope childrenD_99 ⊆ insert (0, 0) required_99 := by decide
theorem child_required_sub_99 : ∀ j, childrenC_99 j ⊆ insert (0, 0) required_99 := by decide
theorem child_envelope_sub_99 : ∀ j, childrenD_99 j ⊆ envelope_99 := by decide
theorem pivot_mem_99 : (0, 0) ∈ envelope_99 := by decide
theorem children_work_99 : ∀ j, Template HasSnaky 3 (childrenC_99 j) (childrenD_99 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_2 1 (-1, -2)).mono (by decide)
  · exact (placed_template_map row_works_24 0 (1, 0)).mono (by decide)
theorem row_works_99 : Template HasSnaky 4 required_99 envelope_99 := by
  refine compose HasSnaky 3 childrenC_99 childrenD_99 children_work_99 (0, 0)
    required_99 envelope_99 pivot_mem_99 child_required_sub_99 child_envelope_sub_99 ?_
  intro b hb; exact common_sub_99 (mem_commonEnvelope childrenD_99 b hb)
def required_100 : Finset Cell := ⟨(([(-3, -1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_100 : Finset Cell := ⟨(([(-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_100 : Fin 2 → Finset Cell := ![(placedSet 6 (1, 0) required_0), (placedSet 0 (-3, 0) required_48)]
def childrenD_100 : Fin 2 → Finset Cell := ![(placedSet 6 (1, 0) envelope_0), (placedSet 0 (-3, 0) envelope_48)]
theorem common_sub_100 : commonEnvelope childrenD_100 ⊆ insert (0, 0) required_100 := by decide
theorem child_required_sub_100 : ∀ j, childrenC_100 j ⊆ insert (0, 0) required_100 := by decide
theorem child_envelope_sub_100 : ∀ j, childrenD_100 j ⊆ envelope_100 := by decide
theorem pivot_mem_100 : (0, 0) ∈ envelope_100 := by decide
theorem children_work_100 : ∀ j, Template HasSnaky 3 (childrenC_100 j) (childrenD_100 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 6 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_48 0 (-3, 0)).mono (by decide)
theorem row_works_100 : Template HasSnaky 4 required_100 envelope_100 := by
  refine compose HasSnaky 3 childrenC_100 childrenD_100 children_work_100 (0, 0)
    required_100 envelope_100 pivot_mem_100 child_required_sub_100 child_envelope_sub_100 ?_
  intro b hb; exact common_sub_100 (mem_commonEnvelope childrenD_100 b hb)
def required_101 : Finset Cell := ⟨(([(-2, -1), (-1, -2), (-1, -1), (0, -1), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_101 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -2), (-1, -1), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_101 : Fin 2 → Finset Cell := ![(placedSet 7 (0, 2) required_0), (placedSet 0 (1, 0) required_24)]
def childrenD_101 : Fin 2 → Finset Cell := ![(placedSet 7 (0, 2) envelope_0), (placedSet 0 (1, 0) envelope_24)]
theorem common_sub_101 : commonEnvelope childrenD_101 ⊆ insert (0, 0) required_101 := by decide
theorem child_required_sub_101 : ∀ j, childrenC_101 j ⊆ insert (0, 0) required_101 := by decide
theorem child_envelope_sub_101 : ∀ j, childrenD_101 j ⊆ envelope_101 := by decide
theorem pivot_mem_101 : (0, 0) ∈ envelope_101 := by decide
theorem children_work_101 : ∀ j, Template HasSnaky 3 (childrenC_101 j) (childrenD_101 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 7 (0, 2)).mono (by decide)
  · exact (placed_template_map row_works_24 0 (1, 0)).mono (by decide)
theorem row_works_101 : Template HasSnaky 4 required_101 envelope_101 := by
  refine compose HasSnaky 3 childrenC_101 childrenD_101 children_work_101 (0, 0)
    required_101 envelope_101 pivot_mem_101 child_required_sub_101 child_envelope_sub_101 ?_
  intro b hb; exact common_sub_101 (mem_commonEnvelope childrenD_101 b hb)
def required_102 : Finset Cell := ⟨(([(-1, 0), (1, -3), (1, -2), (1, -1), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_102 : Finset Cell := ⟨(([(-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_102 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_6), (placedSet 2 (2, -1) required_25)]
def childrenD_102 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_6), (placedSet 2 (2, -1) envelope_25)]
theorem common_sub_102 : commonEnvelope childrenD_102 ⊆ insert (0, 0) required_102 := by decide
theorem child_required_sub_102 : ∀ j, childrenC_102 j ⊆ insert (0, 0) required_102 := by decide
theorem child_envelope_sub_102 : ∀ j, childrenD_102 j ⊆ envelope_102 := by decide
theorem pivot_mem_102 : (0, 0) ∈ envelope_102 := by decide
theorem children_work_102 : ∀ j, Template HasSnaky 3 (childrenC_102 j) (childrenD_102 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_25 2 (2, -1)).mono (by decide)
theorem row_works_102 : Template HasSnaky 4 required_102 envelope_102 := by
  refine compose HasSnaky 3 childrenC_102 childrenD_102 children_work_102 (0, 0)
    required_102 envelope_102 pivot_mem_102 child_required_sub_102 child_envelope_sub_102 ?_
  intro b hb; exact common_sub_102 (mem_commonEnvelope childrenD_102 b hb)
end SnakyConditional

end OAI
