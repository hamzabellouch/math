import OAI.GameTheory.SnakyConditional.Templates.Level08Part01
import OAI.GameTheory.SnakyConditional.Templates.Level08Part02

namespace OAI

namespace SnakyConditional
def required_143 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_143 : Finset Cell := ⟨(([(-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1), (3, 1), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_143 : Fin 2 → Finset Cell := ![(placedSet 6 (-1, 0) required_6), (placedSet 0 (4, 1) required_108)]
def childrenD_143 : Fin 2 → Finset Cell := ![(placedSet 6 (-1, 0) envelope_6), (placedSet 0 (4, 1) envelope_108)]
theorem common_sub_143 : commonEnvelope childrenD_143 ⊆ insert (0, 0) required_143 := by decide
theorem child_required_sub_143 : ∀ j, childrenC_143 j ⊆ insert (0, 0) required_143 := by decide
theorem child_envelope_sub_143 : ∀ j, childrenD_143 j ⊆ envelope_143 := by decide
theorem pivot_mem_143 : (0, 0) ∈ envelope_143 := by decide
theorem children_work_143 : ∀ j, Template HasSnaky 6 (childrenC_143 j) (childrenD_143 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 6 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_108 0 (4, 1)).mono (by decide)
theorem row_works_143 : Template HasSnaky 7 required_143 envelope_143 := by
  refine compose HasSnaky 6 childrenC_143 childrenD_143 children_work_143 (0, 0)
    required_143 envelope_143 pivot_mem_143 child_required_sub_143 child_envelope_sub_143 ?_
  intro b hb; exact common_sub_143 (mem_commonEnvelope childrenD_143 b hb)
def required_164 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (-1, -1), (-1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_164 : Finset Cell := ⟨(([(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_164 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_6), (placedSet 0 (1, 0) required_110)]
def childrenD_164 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_6), (placedSet 0 (1, 0) envelope_110)]
theorem common_sub_164 : commonEnvelope childrenD_164 ⊆ insert (0, 0) required_164 := by decide
theorem child_required_sub_164 : ∀ j, childrenC_164 j ⊆ insert (0, 0) required_164 := by decide
theorem child_envelope_sub_164 : ∀ j, childrenD_164 j ⊆ envelope_164 := by decide
theorem pivot_mem_164 : (0, 0) ∈ envelope_164 := by decide
theorem children_work_164 : ∀ j, Template HasSnaky 6 (childrenC_164 j) (childrenD_164 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_110 0 (1, 0)).mono (by decide)
theorem row_works_164 : Template HasSnaky 7 required_164 envelope_164 := by
  refine compose HasSnaky 6 childrenC_164 childrenD_164 children_work_164 (0, 0)
    required_164 envelope_164 pivot_mem_164 child_required_sub_164 child_envelope_sub_164 ?_
  intro b hb; exact common_sub_164 (mem_commonEnvelope childrenD_164 b hb)
def required_165 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 3), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_165 : Finset Cell := ⟨(([(-1, 0), (0, 0), (0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_165 : Fin 2 → Finset Cell := ![(placedSet 7 (1, 4) required_0), (placedSet 0 (3, 1) required_107)]
def childrenD_165 : Fin 2 → Finset Cell := ![(placedSet 7 (1, 4) envelope_0), (placedSet 0 (3, 1) envelope_107)]
theorem common_sub_165 : commonEnvelope childrenD_165 ⊆ insert (0, 0) required_165 := by decide
theorem child_required_sub_165 : ∀ j, childrenC_165 j ⊆ insert (0, 0) required_165 := by decide
theorem child_envelope_sub_165 : ∀ j, childrenD_165 j ⊆ envelope_165 := by decide
theorem pivot_mem_165 : (0, 0) ∈ envelope_165 := by decide
theorem children_work_165 : ∀ j, Template HasSnaky 6 (childrenC_165 j) (childrenD_165 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 7 (1, 4)).mono (by decide)
  · exact (placed_template_map row_works_107 0 (3, 1)).mono (by decide)
theorem row_works_165 : Template HasSnaky 7 required_165 envelope_165 := by
  refine compose HasSnaky 6 childrenC_165 childrenD_165 children_work_165 (0, 0)
    required_165 envelope_165 pivot_mem_165 child_required_sub_165 child_envelope_sub_165 ?_
  intro b hb; exact common_sub_165 (mem_commonEnvelope childrenD_165 b hb)
def required_166 : Finset Cell := ⟨(([(-1, -1), (-1, 0), (0, 2), (0, 3), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_166 : Finset Cell := ⟨(([(-2, -1), (-1, -1), (-1, 0), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_166 : Fin 2 → Finset Cell := ![(placedSet 7 (0, 1) required_2), (placedSet 0 (2, 0) required_107)]
def childrenD_166 : Fin 2 → Finset Cell := ![(placedSet 7 (0, 1) envelope_2), (placedSet 0 (2, 0) envelope_107)]
theorem common_sub_166 : commonEnvelope childrenD_166 ⊆ insert (0, 0) required_166 := by decide
theorem child_required_sub_166 : ∀ j, childrenC_166 j ⊆ insert (0, 0) required_166 := by decide
theorem child_envelope_sub_166 : ∀ j, childrenD_166 j ⊆ envelope_166 := by decide
theorem pivot_mem_166 : (0, 0) ∈ envelope_166 := by decide
theorem children_work_166 : ∀ j, Template HasSnaky 6 (childrenC_166 j) (childrenD_166 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_2 7 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_107 0 (2, 0)).mono (by decide)
theorem row_works_166 : Template HasSnaky 7 required_166 envelope_166 := by
  refine compose HasSnaky 6 childrenC_166 childrenD_166 children_work_166 (0, 0)
    required_166 envelope_166 pivot_mem_166 child_required_sub_166 child_envelope_sub_166 ?_
  intro b hb; exact common_sub_166 (mem_commonEnvelope childrenD_166 b hb)
def required_168 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (1, 0), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_168 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_168 : Fin 2 → Finset Cell := ![(placedSet 1 (1, 1) required_6), (placedSet 0 (-1, 0) required_152)]
def childrenD_168 : Fin 2 → Finset Cell := ![(placedSet 1 (1, 1) envelope_6), (placedSet 0 (-1, 0) envelope_152)]
theorem common_sub_168 : commonEnvelope childrenD_168 ⊆ insert (0, 0) required_168 := by decide
theorem child_required_sub_168 : ∀ j, childrenC_168 j ⊆ insert (0, 0) required_168 := by decide
theorem child_envelope_sub_168 : ∀ j, childrenD_168 j ⊆ envelope_168 := by decide
theorem pivot_mem_168 : (0, 0) ∈ envelope_168 := by decide
theorem children_work_168 : ∀ j, Template HasSnaky 6 (childrenC_168 j) (childrenD_168 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_152 0 (-1, 0)).mono (by decide)
theorem row_works_168 : Template HasSnaky 7 required_168 envelope_168 := by
  refine compose HasSnaky 6 childrenC_168 childrenD_168 children_work_168 (0, 0)
    required_168 envelope_168 pivot_mem_168 child_required_sub_168 child_envelope_sub_168 ?_
  intro b hb; exact common_sub_168 (mem_commonEnvelope childrenD_168 b hb)
def required_179 : Finset Cell := ⟨(([(-3, -1), (-3, 0), (-2, 0), (-1, -1), (-1, 0), (-1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_179 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_179 : Fin 2 → Finset Cell := ![(placedSet 6 (-4, -1) required_6), (placedSet 5 (1, 0) required_148)]
def childrenD_179 : Fin 2 → Finset Cell := ![(placedSet 6 (-4, -1) envelope_6), (placedSet 5 (1, 0) envelope_148)]
theorem common_sub_179 : commonEnvelope childrenD_179 ⊆ insert (0, 0) required_179 := by decide
theorem child_required_sub_179 : ∀ j, childrenC_179 j ⊆ insert (0, 0) required_179 := by decide
theorem child_envelope_sub_179 : ∀ j, childrenD_179 j ⊆ envelope_179 := by decide
theorem pivot_mem_179 : (0, 0) ∈ envelope_179 := by decide
theorem children_work_179 : ∀ j, Template HasSnaky 6 (childrenC_179 j) (childrenD_179 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 6 (-4, -1)).mono (by decide)
  · exact (placed_template_map row_works_148 5 (1, 0)).mono (by decide)
theorem row_works_179 : Template HasSnaky 7 required_179 envelope_179 := by
  refine compose HasSnaky 6 childrenC_179 childrenD_179 children_work_179 (0, 0)
    required_179 envelope_179 pivot_mem_179 child_required_sub_179 child_envelope_sub_179 ?_
  intro b hb; exact common_sub_179 (mem_commonEnvelope childrenD_179 b hb)
end SnakyConditional

end OAI
