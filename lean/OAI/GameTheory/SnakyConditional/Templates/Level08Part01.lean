import OAI.GameTheory.SnakyConditional.Templates.Level07Part01
import OAI.GameTheory.SnakyConditional.Templates.Level07Part02

namespace OAI

namespace SnakyConditional
def required_107 : Finset Cell := ⟨(([(-3, -1), (-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_107 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_107 : Fin 2 → Finset Cell := ![(placedSet 6 (-4, -1) required_6), (placedSet 1 (1, -1) required_63)]
def childrenD_107 : Fin 2 → Finset Cell := ![(placedSet 6 (-4, -1) envelope_6), (placedSet 1 (1, -1) envelope_63)]
theorem common_sub_107 : commonEnvelope childrenD_107 ⊆ insert (0, 0) required_107 := by decide
theorem child_required_sub_107 : ∀ j, childrenC_107 j ⊆ insert (0, 0) required_107 := by decide
theorem child_envelope_sub_107 : ∀ j, childrenD_107 j ⊆ envelope_107 := by decide
theorem pivot_mem_107 : (0, 0) ∈ envelope_107 := by decide
theorem children_work_107 : ∀ j, Template HasSnaky 5 (childrenC_107 j) (childrenD_107 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 6 (-4, -1)).mono (by decide)
  · exact (placed_template_map row_works_63 1 (1, -1)).mono (by decide)
theorem row_works_107 : Template HasSnaky 6 required_107 envelope_107 := by
  refine compose HasSnaky 5 childrenC_107 childrenD_107 children_work_107 (0, 0)
    required_107 envelope_107 pivot_mem_107 child_required_sub_107 child_envelope_sub_107 ?_
  intro b hb; exact common_sub_107 (mem_commonEnvelope childrenD_107 b hb)
def required_108 : Finset Cell := ⟨(([(-4, -1), (-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_108 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_108 : Fin 2 → Finset Cell := ![(placedSet 6 (-3, -1) required_4), (placedSet 1 (1, -1) required_63)]
def childrenD_108 : Fin 2 → Finset Cell := ![(placedSet 6 (-3, -1) envelope_4), (placedSet 1 (1, -1) envelope_63)]
theorem common_sub_108 : commonEnvelope childrenD_108 ⊆ insert (0, 0) required_108 := by decide
theorem child_required_sub_108 : ∀ j, childrenC_108 j ⊆ insert (0, 0) required_108 := by decide
theorem child_envelope_sub_108 : ∀ j, childrenD_108 j ⊆ envelope_108 := by decide
theorem pivot_mem_108 : (0, 0) ∈ envelope_108 := by decide
theorem children_work_108 : ∀ j, Template HasSnaky 5 (childrenC_108 j) (childrenD_108 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_4 6 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_63 1 (1, -1)).mono (by decide)
theorem row_works_108 : Template HasSnaky 6 required_108 envelope_108 := by
  refine compose HasSnaky 5 childrenC_108 childrenD_108 children_work_108 (0, 0)
    required_108 envelope_108 pivot_mem_108 child_required_sub_108 child_envelope_sub_108 ?_
  intro b hb; exact common_sub_108 (mem_commonEnvelope childrenD_108 b hb)
def required_110 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-1, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_110 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-2, 0), (-1, 0), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_110 : Fin 2 → Finset Cell := ![(placedSet 6 (-3, -1) required_6), (placedSet 1 (2, -1) required_63)]
def childrenD_110 : Fin 2 → Finset Cell := ![(placedSet 6 (-3, -1) envelope_6), (placedSet 1 (2, -1) envelope_63)]
theorem common_sub_110 : commonEnvelope childrenD_110 ⊆ insert (0, 0) required_110 := by decide
theorem child_required_sub_110 : ∀ j, childrenC_110 j ⊆ insert (0, 0) required_110 := by decide
theorem child_envelope_sub_110 : ∀ j, childrenD_110 j ⊆ envelope_110 := by decide
theorem pivot_mem_110 : (0, 0) ∈ envelope_110 := by decide
theorem children_work_110 : ∀ j, Template HasSnaky 5 (childrenC_110 j) (childrenD_110 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 6 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_63 1 (2, -1)).mono (by decide)
theorem row_works_110 : Template HasSnaky 6 required_110 envelope_110 := by
  refine compose HasSnaky 5 childrenC_110 childrenD_110 children_work_110 (0, 0)
    required_110 envelope_110 pivot_mem_110 child_required_sub_110 child_envelope_sub_110 ?_
  intro b hb; exact common_sub_110 (mem_commonEnvelope childrenD_110 b hb)
def required_111 : Finset Cell := ⟨(([(1, 0), (1, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_111 : Finset Cell := ⟨(([(-1, 1), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (3, 0), (4, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_111 : Fin 2 → Finset Cell := ![(placedSet 7 (0, -1) required_6), (placedSet 0 (0, 1) required_83)]
def childrenD_111 : Fin 2 → Finset Cell := ![(placedSet 7 (0, -1) envelope_6), (placedSet 0 (0, 1) envelope_83)]
theorem common_sub_111 : commonEnvelope childrenD_111 ⊆ insert (0, 0) required_111 := by decide
theorem child_required_sub_111 : ∀ j, childrenC_111 j ⊆ insert (0, 0) required_111 := by decide
theorem child_envelope_sub_111 : ∀ j, childrenD_111 j ⊆ envelope_111 := by decide
theorem pivot_mem_111 : (0, 0) ∈ envelope_111 := by decide
theorem children_work_111 : ∀ j, Template HasSnaky 5 (childrenC_111 j) (childrenD_111 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 7 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_83 0 (0, 1)).mono (by decide)
theorem row_works_111 : Template HasSnaky 6 required_111 envelope_111 := by
  refine compose HasSnaky 5 childrenC_111 childrenD_111 children_work_111 (0, 0)
    required_111 envelope_111 pivot_mem_111 child_required_sub_111 child_envelope_sub_111 ?_
  intro b hb; exact common_sub_111 (mem_commonEnvelope childrenD_111 b hb)
def required_123 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-1, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_123 : Finset Cell := ⟨(([(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_123 : Fin 2 → Finset Cell := ![(placedSet 6 (-3, -1) required_6), (placedSet 2 (-2, 1) required_64)]
def childrenD_123 : Fin 2 → Finset Cell := ![(placedSet 6 (-3, -1) envelope_6), (placedSet 2 (-2, 1) envelope_64)]
theorem common_sub_123 : commonEnvelope childrenD_123 ⊆ insert (0, 0) required_123 := by decide
theorem child_required_sub_123 : ∀ j, childrenC_123 j ⊆ insert (0, 0) required_123 := by decide
theorem child_envelope_sub_123 : ∀ j, childrenD_123 j ⊆ envelope_123 := by decide
theorem pivot_mem_123 : (0, 0) ∈ envelope_123 := by decide
theorem children_work_123 : ∀ j, Template HasSnaky 5 (childrenC_123 j) (childrenD_123 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 6 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_64 2 (-2, 1)).mono (by decide)
theorem row_works_123 : Template HasSnaky 6 required_123 envelope_123 := by
  refine compose HasSnaky 5 childrenC_123 childrenD_123 children_work_123 (0, 0)
    required_123 envelope_123 pivot_mem_123 child_required_sub_123 child_envelope_sub_123 ?_
  intro b hb; exact common_sub_123 (mem_commonEnvelope childrenD_123 b hb)
def required_130 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (-1, -1), (-1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_130 : Finset Cell := ⟨(([(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (2, 0), (2, 1), (3, 0), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_130 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_6), (placedSet 0 (1, 0) required_60)]
def childrenD_130 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_6), (placedSet 0 (1, 0) envelope_60)]
theorem common_sub_130 : commonEnvelope childrenD_130 ⊆ insert (0, 0) required_130 := by decide
theorem child_required_sub_130 : ∀ j, childrenC_130 j ⊆ insert (0, 0) required_130 := by decide
theorem child_envelope_sub_130 : ∀ j, childrenD_130 j ⊆ envelope_130 := by decide
theorem pivot_mem_130 : (0, 0) ∈ envelope_130 := by decide
theorem children_work_130 : ∀ j, Template HasSnaky 5 (childrenC_130 j) (childrenD_130 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_60 0 (1, 0)).mono (by decide)
theorem row_works_130 : Template HasSnaky 6 required_130 envelope_130 := by
  refine compose HasSnaky 5 childrenC_130 childrenD_130 children_work_130 (0, 0)
    required_130 envelope_130 pivot_mem_130 child_required_sub_130 child_envelope_sub_130 ?_
  intro b hb; exact common_sub_130 (mem_commonEnvelope childrenD_130 b hb)
def required_137 : Finset Cell := ⟨(([(-1, -4), (-1, -3), (-1, -2), (-1, -1), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_137 : Finset Cell := ⟨(([(-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_137 : Fin 2 → Finset Cell := ![(placedSet 1 (0, -1) required_4), (placedSet 0 (-1, 0) required_96)]
def childrenD_137 : Fin 2 → Finset Cell := ![(placedSet 1 (0, -1) envelope_4), (placedSet 0 (-1, 0) envelope_96)]
theorem common_sub_137 : commonEnvelope childrenD_137 ⊆ insert (0, 0) required_137 := by decide
theorem child_required_sub_137 : ∀ j, childrenC_137 j ⊆ insert (0, 0) required_137 := by decide
theorem child_envelope_sub_137 : ∀ j, childrenD_137 j ⊆ envelope_137 := by decide
theorem pivot_mem_137 : (0, 0) ∈ envelope_137 := by decide
theorem children_work_137 : ∀ j, Template HasSnaky 5 (childrenC_137 j) (childrenD_137 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_4 1 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_96 0 (-1, 0)).mono (by decide)
theorem row_works_137 : Template HasSnaky 6 required_137 envelope_137 := by
  refine compose HasSnaky 5 childrenC_137 childrenD_137 children_work_137 (0, 0)
    required_137 envelope_137 pivot_mem_137 child_required_sub_137 child_envelope_sub_137 ?_
  intro b hb; exact common_sub_137 (mem_commonEnvelope childrenD_137 b hb)
end SnakyConditional

end OAI
