import OAI.GameTheory.SnakyConditional.Templates.Level05Part01
import OAI.GameTheory.SnakyConditional.Templates.Level05Part07

namespace OAI

namespace SnakyConditional
def required_56 : Finset Cell := ⟨(([(-4, 0), (-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_56 : Finset Cell := ⟨(([(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (0, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_56 : Fin 2 → Finset Cell := ![(placedSet 4 (-4, 1) required_7), (placedSet 6 (-4, -1) required_7)]
def childrenD_56 : Fin 2 → Finset Cell := ![(placedSet 4 (-4, 1) envelope_7), (placedSet 6 (-4, -1) envelope_7)]
theorem common_sub_56 : commonEnvelope childrenD_56 ⊆ insert (0, 0) required_56 := by decide
theorem child_required_sub_56 : ∀ j, childrenC_56 j ⊆ insert (0, 0) required_56 := by decide
theorem child_envelope_sub_56 : ∀ j, childrenD_56 j ⊆ envelope_56 := by decide
theorem pivot_mem_56 : (0, 0) ∈ envelope_56 := by decide
theorem children_work_56 : ∀ j, Template HasSnaky 3 (childrenC_56 j) (childrenD_56 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_7 4 (-4, 1)).mono (by decide)
  · exact (placed_template_map row_works_7 6 (-4, -1)).mono (by decide)
theorem row_works_56 : Template HasSnaky 4 required_56 envelope_56 := by
  refine compose HasSnaky 3 childrenC_56 childrenD_56 children_work_56 (0, 0)
    required_56 envelope_56 pivot_mem_56 child_required_sub_56 child_envelope_sub_56 ?_
  intro b hb; exact common_sub_56 (mem_commonEnvelope childrenD_56 b hb)
def required_57 : Finset Cell := ⟨(([(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_57 : Finset Cell := ⟨(([(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_57 : Fin 2 → Finset Cell := ![(placedSet 6 (1, 0) required_0), (placedSet 0 (0, 1) required_7)]
def childrenD_57 : Fin 2 → Finset Cell := ![(placedSet 6 (1, 0) envelope_0), (placedSet 0 (0, 1) envelope_7)]
theorem common_sub_57 : commonEnvelope childrenD_57 ⊆ insert (0, 0) required_57 := by decide
theorem child_required_sub_57 : ∀ j, childrenC_57 j ⊆ insert (0, 0) required_57 := by decide
theorem child_envelope_sub_57 : ∀ j, childrenD_57 j ⊆ envelope_57 := by decide
theorem pivot_mem_57 : (0, 0) ∈ envelope_57 := by decide
theorem children_work_57 : ∀ j, Template HasSnaky 3 (childrenC_57 j) (childrenD_57 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 6 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_7 0 (0, 1)).mono (by decide)
theorem row_works_57 : Template HasSnaky 4 required_57 envelope_57 := by
  refine compose HasSnaky 3 childrenC_57 childrenD_57 children_work_57 (0, 0)
    required_57 envelope_57 pivot_mem_57 child_required_sub_57 child_envelope_sub_57 ?_
  intro b hb; exact common_sub_57 (mem_commonEnvelope childrenD_57 b hb)
def required_58 : Finset Cell := ⟨(([(-4, 0), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_58 : Finset Cell := ⟨(([(-4, 0), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_58 : Fin 2 → Finset Cell := ![(placedSet 4 (1, 0) required_0), (placedSet 0 (0, 1) required_7)]
def childrenD_58 : Fin 2 → Finset Cell := ![(placedSet 4 (1, 0) envelope_0), (placedSet 0 (0, 1) envelope_7)]
theorem common_sub_58 : commonEnvelope childrenD_58 ⊆ insert (0, 0) required_58 := by decide
theorem child_required_sub_58 : ∀ j, childrenC_58 j ⊆ insert (0, 0) required_58 := by decide
theorem child_envelope_sub_58 : ∀ j, childrenD_58 j ⊆ envelope_58 := by decide
theorem pivot_mem_58 : (0, 0) ∈ envelope_58 := by decide
theorem children_work_58 : ∀ j, Template HasSnaky 3 (childrenC_58 j) (childrenD_58 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 4 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_7 0 (0, 1)).mono (by decide)
theorem row_works_58 : Template HasSnaky 4 required_58 envelope_58 := by
  refine compose HasSnaky 3 childrenC_58 childrenD_58 children_work_58 (0, 0)
    required_58 envelope_58 pivot_mem_58 child_required_sub_58 child_envelope_sub_58 ?_
  intro b hb; exact common_sub_58 (mem_commonEnvelope childrenD_58 b hb)
def required_59 : Finset Cell := ⟨(([(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_59 : Finset Cell := ⟨(([(-5, 1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, 0), (0, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_59 : Fin 2 → Finset Cell := ![(placedSet 6 (1, 0) required_0), (placedSet 4 (-4, 1) required_7)]
def childrenD_59 : Fin 2 → Finset Cell := ![(placedSet 6 (1, 0) envelope_0), (placedSet 4 (-4, 1) envelope_7)]
theorem common_sub_59 : commonEnvelope childrenD_59 ⊆ insert (0, 0) required_59 := by decide
theorem child_required_sub_59 : ∀ j, childrenC_59 j ⊆ insert (0, 0) required_59 := by decide
theorem child_envelope_sub_59 : ∀ j, childrenD_59 j ⊆ envelope_59 := by decide
theorem pivot_mem_59 : (0, 0) ∈ envelope_59 := by decide
theorem children_work_59 : ∀ j, Template HasSnaky 3 (childrenC_59 j) (childrenD_59 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 6 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_7 4 (-4, 1)).mono (by decide)
theorem row_works_59 : Template HasSnaky 4 required_59 envelope_59 := by
  refine compose HasSnaky 3 childrenC_59 childrenD_59 children_work_59 (0, 0)
    required_59 envelope_59 pivot_mem_59 child_required_sub_59 child_envelope_sub_59 ?_
  intro b hb; exact common_sub_59 (mem_commonEnvelope childrenD_59 b hb)
def required_62 : Finset Cell := ⟨(([(-3, -1), (-3, 0), (-2, 0), (-2, 2), (-2, 3), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_62 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, 0), (-2, 2), (-2, 3), (-1, 0), (0, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_62 : Fin 2 → Finset Cell := ![(placedSet 6 (-4, -1) required_6), (placedSet 0 (-3, 1) required_53)]
def childrenD_62 : Fin 2 → Finset Cell := ![(placedSet 6 (-4, -1) envelope_6), (placedSet 0 (-3, 1) envelope_53)]
theorem common_sub_62 : commonEnvelope childrenD_62 ⊆ insert (0, 0) required_62 := by decide
theorem child_required_sub_62 : ∀ j, childrenC_62 j ⊆ insert (0, 0) required_62 := by decide
theorem child_envelope_sub_62 : ∀ j, childrenD_62 j ⊆ envelope_62 := by decide
theorem pivot_mem_62 : (0, 0) ∈ envelope_62 := by decide
theorem children_work_62 : ∀ j, Template HasSnaky 3 (childrenC_62 j) (childrenD_62 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 6 (-4, -1)).mono (by decide)
  · exact (placed_template_map row_works_53 0 (-3, 1)).mono (by decide)
theorem row_works_62 : Template HasSnaky 4 required_62 envelope_62 := by
  refine compose HasSnaky 3 childrenC_62 childrenD_62 children_work_62 (0, 0)
    required_62 envelope_62 pivot_mem_62 child_required_sub_62 child_envelope_sub_62 ?_
  intro b hb; exact common_sub_62 (mem_commonEnvelope childrenD_62 b hb)
def required_66 : Finset Cell := ⟨(([(1, -3), (1, -2), (1, -1), (1, 0), (3, -1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_66 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (2, 1), (3, -1), (3, 0), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_66 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_6), (placedSet 5 (2, 0) required_53)]
def childrenD_66 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_6), (placedSet 5 (2, 0) envelope_53)]
theorem common_sub_66 : commonEnvelope childrenD_66 ⊆ insert (0, 0) required_66 := by decide
theorem child_required_sub_66 : ∀ j, childrenC_66 j ⊆ insert (0, 0) required_66 := by decide
theorem child_envelope_sub_66 : ∀ j, childrenD_66 j ⊆ envelope_66 := by decide
theorem pivot_mem_66 : (0, 0) ∈ envelope_66 := by decide
theorem children_work_66 : ∀ j, Template HasSnaky 3 (childrenC_66 j) (childrenD_66 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_53 5 (2, 0)).mono (by decide)
theorem row_works_66 : Template HasSnaky 4 required_66 envelope_66 := by
  refine compose HasSnaky 3 childrenC_66 childrenD_66 children_work_66 (0, 0)
    required_66 envelope_66 pivot_mem_66 child_required_sub_66 child_envelope_sub_66 ?_
  intro b hb; exact common_sub_66 (mem_commonEnvelope childrenD_66 b hb)
def required_67 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_67 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_67 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_6), (placedSet 2 (1, 0) required_9)]
def childrenD_67 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_6), (placedSet 2 (1, 0) envelope_9)]
theorem common_sub_67 : commonEnvelope childrenD_67 ⊆ insert (0, 0) required_67 := by decide
theorem child_required_sub_67 : ∀ j, childrenC_67 j ⊆ insert (0, 0) required_67 := by decide
theorem child_envelope_sub_67 : ∀ j, childrenD_67 j ⊆ envelope_67 := by decide
theorem pivot_mem_67 : (0, 0) ∈ envelope_67 := by decide
theorem children_work_67 : ∀ j, Template HasSnaky 3 (childrenC_67 j) (childrenD_67 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_9 2 (1, 0)).mono (by decide)
theorem row_works_67 : Template HasSnaky 4 required_67 envelope_67 := by
  refine compose HasSnaky 3 childrenC_67 childrenD_67 children_work_67 (0, 0)
    required_67 envelope_67 pivot_mem_67 child_required_sub_67 child_envelope_sub_67 ?_
  intro b hb; exact common_sub_67 (mem_commonEnvelope childrenD_67 b hb)
end SnakyConditional

end OAI
