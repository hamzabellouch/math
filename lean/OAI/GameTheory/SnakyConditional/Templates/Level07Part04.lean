import OAI.GameTheory.SnakyConditional.Templates.Level06Part01
import OAI.GameTheory.SnakyConditional.Templates.Level06Part02
import OAI.GameTheory.SnakyConditional.Templates.Level06Part06

namespace OAI

namespace SnakyConditional
def required_120 : Finset Cell := ⟨(([(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_120 : Finset Cell := ⟨(([(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_120 : Fin 2 → Finset Cell := ![(placedSet 0 (0, 1) required_4), (placedSet 2 (1, 0) required_58)]
def childrenD_120 : Fin 2 → Finset Cell := ![(placedSet 0 (0, 1) envelope_4), (placedSet 2 (1, 0) envelope_58)]
theorem common_sub_120 : commonEnvelope childrenD_120 ⊆ insert (0, 0) required_120 := by decide
theorem child_required_sub_120 : ∀ j, childrenC_120 j ⊆ insert (0, 0) required_120 := by decide
theorem child_envelope_sub_120 : ∀ j, childrenD_120 j ⊆ envelope_120 := by decide
theorem pivot_mem_120 : (0, 0) ∈ envelope_120 := by decide
theorem children_work_120 : ∀ j, Template HasSnaky 4 (childrenC_120 j) (childrenD_120 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_4 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_58 2 (1, 0)).mono (by decide)
theorem row_works_120 : Template HasSnaky 5 required_120 envelope_120 := by
  refine compose HasSnaky 4 childrenC_120 childrenD_120 children_work_120 (0, 0)
    required_120 envelope_120 pivot_mem_120 child_required_sub_120 child_envelope_sub_120 ?_
  intro b hb; exact common_sub_120 (mem_commonEnvelope childrenD_120 b hb)
def required_122 : Finset Cell := ⟨(([(0, -1), (1, 0), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_122 : Finset Cell := ⟨(([(-1, -1), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (3, 0), (4, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_122 : Fin 2 → Finset Cell := ![(placedSet 6 (-1, -1) required_6), (placedSet 1 (0, 1) required_105)]
def childrenD_122 : Fin 2 → Finset Cell := ![(placedSet 6 (-1, -1) envelope_6), (placedSet 1 (0, 1) envelope_105)]
theorem common_sub_122 : commonEnvelope childrenD_122 ⊆ insert (0, 0) required_122 := by decide
theorem child_required_sub_122 : ∀ j, childrenC_122 j ⊆ insert (0, 0) required_122 := by decide
theorem child_envelope_sub_122 : ∀ j, childrenD_122 j ⊆ envelope_122 := by decide
theorem pivot_mem_122 : (0, 0) ∈ envelope_122 := by decide
theorem children_work_122 : ∀ j, Template HasSnaky 4 (childrenC_122 j) (childrenD_122 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 6 (-1, -1)).mono (by decide)
  · exact (placed_template_map row_works_105 1 (0, 1)).mono (by decide)
theorem row_works_122 : Template HasSnaky 5 required_122 envelope_122 := by
  refine compose HasSnaky 4 childrenC_122 childrenD_122 children_work_122 (0, 0)
    required_122 envelope_122 pivot_mem_122 child_required_sub_122 child_envelope_sub_122 ?_
  intro b hb; exact common_sub_122 (mem_commonEnvelope childrenD_122 b hb)
def required_126 : Finset Cell := ⟨(([(1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_126 : Finset Cell := ⟨(([(0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_126 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_6), (placedSet 1 (1, 3) required_46)]
def childrenD_126 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_6), (placedSet 1 (1, 3) envelope_46)]
theorem common_sub_126 : commonEnvelope childrenD_126 ⊆ insert (0, 0) required_126 := by decide
theorem child_required_sub_126 : ∀ j, childrenC_126 j ⊆ insert (0, 0) required_126 := by decide
theorem child_envelope_sub_126 : ∀ j, childrenD_126 j ⊆ envelope_126 := by decide
theorem pivot_mem_126 : (0, 0) ∈ envelope_126 := by decide
theorem children_work_126 : ∀ j, Template HasSnaky 4 (childrenC_126 j) (childrenD_126 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_46 1 (1, 3)).mono (by decide)
theorem row_works_126 : Template HasSnaky 5 required_126 envelope_126 := by
  refine compose HasSnaky 4 childrenC_126 childrenD_126 children_work_126 (0, 0)
    required_126 envelope_126 pivot_mem_126 child_required_sub_126 child_envelope_sub_126 ?_
  intro b hb; exact common_sub_126 (mem_commonEnvelope childrenD_126 b hb)
def required_127 : Finset Cell := ⟨(([(-4, 0), (-3, -1), (-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_127 : Finset Cell := ⟨(([(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_127 : Fin 2 → Finset Cell := ![(placedSet 0 (0, 1) required_7), (placedSet 2 (1, 0) required_44)]
def childrenD_127 : Fin 2 → Finset Cell := ![(placedSet 0 (0, 1) envelope_7), (placedSet 2 (1, 0) envelope_44)]
theorem common_sub_127 : commonEnvelope childrenD_127 ⊆ insert (0, 0) required_127 := by decide
theorem child_required_sub_127 : ∀ j, childrenC_127 j ⊆ insert (0, 0) required_127 := by decide
theorem child_envelope_sub_127 : ∀ j, childrenD_127 j ⊆ envelope_127 := by decide
theorem pivot_mem_127 : (0, 0) ∈ envelope_127 := by decide
theorem children_work_127 : ∀ j, Template HasSnaky 4 (childrenC_127 j) (childrenD_127 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_7 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_44 2 (1, 0)).mono (by decide)
theorem row_works_127 : Template HasSnaky 5 required_127 envelope_127 := by
  refine compose HasSnaky 4 childrenC_127 childrenD_127 children_work_127 (0, 0)
    required_127 envelope_127 pivot_mem_127 child_required_sub_127 child_envelope_sub_127 ?_
  intro b hb; exact common_sub_127 (mem_commonEnvelope childrenD_127 b hb)
def required_128 : Finset Cell := ⟨(([(-2, 1), (-1, 0), (-1, 1), (0, 1), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_128 : Finset Cell := ⟨(([(-4, 1), (-3, 1), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 1), (2, 2), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_128 : Fin 2 → Finset Cell := ![(placedSet 6 (-3, 1) required_9), (placedSet 0 (2, 1) required_57)]
def childrenD_128 : Fin 2 → Finset Cell := ![(placedSet 6 (-3, 1) envelope_9), (placedSet 0 (2, 1) envelope_57)]
theorem common_sub_128 : commonEnvelope childrenD_128 ⊆ insert (0, 0) required_128 := by decide
theorem child_required_sub_128 : ∀ j, childrenC_128 j ⊆ insert (0, 0) required_128 := by decide
theorem child_envelope_sub_128 : ∀ j, childrenD_128 j ⊆ envelope_128 := by decide
theorem pivot_mem_128 : (0, 0) ∈ envelope_128 := by decide
theorem children_work_128 : ∀ j, Template HasSnaky 4 (childrenC_128 j) (childrenD_128 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_9 6 (-3, 1)).mono (by decide)
  · exact (placed_template_map row_works_57 0 (2, 1)).mono (by decide)
theorem row_works_128 : Template HasSnaky 5 required_128 envelope_128 := by
  refine compose HasSnaky 4 childrenC_128 childrenD_128 children_work_128 (0, 0)
    required_128 envelope_128 pivot_mem_128 child_required_sub_128 child_envelope_sub_128 ?_
  intro b hb; exact common_sub_128 (mem_commonEnvelope childrenD_128 b hb)
def required_129 : Finset Cell := ⟨(([(-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -1), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_129 : Finset Cell := ⟨(([(-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_129 : Fin 2 → Finset Cell := ![(placedSet 4 (-2, 1) required_6), (placedSet 1 (-1, 2) required_58)]
def childrenD_129 : Fin 2 → Finset Cell := ![(placedSet 4 (-2, 1) envelope_6), (placedSet 1 (-1, 2) envelope_58)]
theorem common_sub_129 : commonEnvelope childrenD_129 ⊆ insert (0, 0) required_129 := by decide
theorem child_required_sub_129 : ∀ j, childrenC_129 j ⊆ insert (0, 0) required_129 := by decide
theorem child_envelope_sub_129 : ∀ j, childrenD_129 j ⊆ envelope_129 := by decide
theorem pivot_mem_129 : (0, 0) ∈ envelope_129 := by decide
theorem children_work_129 : ∀ j, Template HasSnaky 4 (childrenC_129 j) (childrenD_129 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 4 (-2, 1)).mono (by decide)
  · exact (placed_template_map row_works_58 1 (-1, 2)).mono (by decide)
theorem row_works_129 : Template HasSnaky 5 required_129 envelope_129 := by
  refine compose HasSnaky 4 childrenC_129 childrenD_129 children_work_129 (0, 0)
    required_129 envelope_129 pivot_mem_129 child_required_sub_129 child_envelope_sub_129 ?_
  intro b hb; exact common_sub_129 (mem_commonEnvelope childrenD_129 b hb)
def required_131 : Finset Cell := ⟨(([(-1, -2), (0, -4), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_131 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_131 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_45), (placedSet 1 (1, 0) required_7)]
def childrenD_131 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_45), (placedSet 1 (1, 0) envelope_7)]
theorem common_sub_131 : commonEnvelope childrenD_131 ⊆ insert (0, 0) required_131 := by decide
theorem child_required_sub_131 : ∀ j, childrenC_131 j ⊆ insert (0, 0) required_131 := by decide
theorem child_envelope_sub_131 : ∀ j, childrenD_131 j ⊆ envelope_131 := by decide
theorem pivot_mem_131 : (0, 0) ∈ envelope_131 := by decide
theorem children_work_131 : ∀ j, Template HasSnaky 4 (childrenC_131 j) (childrenD_131 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_45 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_7 1 (1, 0)).mono (by decide)
theorem row_works_131 : Template HasSnaky 5 required_131 envelope_131 := by
  refine compose HasSnaky 4 childrenC_131 childrenD_131 children_work_131 (0, 0)
    required_131 envelope_131 pivot_mem_131 child_required_sub_131 child_envelope_sub_131 ?_
  intro b hb; exact common_sub_131 (mem_commonEnvelope childrenD_131 b hb)
end SnakyConditional

end OAI
