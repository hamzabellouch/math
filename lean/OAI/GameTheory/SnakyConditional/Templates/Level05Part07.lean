import OAI.GameTheory.SnakyConditional.Templates.Level04Part01
import OAI.GameTheory.SnakyConditional.Templates.Level04Part02
import OAI.GameTheory.SnakyConditional.Templates.Level04Part05

namespace OAI

namespace SnakyConditional
def required_53 : Finset Cell := ⟨(([(0, -2), (0, -1), (1, -1), (1, 1), (1, 2), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_53 : Finset Cell := ⟨(([(-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 1), (1, 2), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_53 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) required_6), (placedSet 1 (0, 1) required_3)]
def childrenD_53 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) envelope_6), (placedSet 1 (0, 1) envelope_3)]
theorem common_sub_53 : commonEnvelope childrenD_53 ⊆ insert (0, 0) required_53 := by decide
theorem child_required_sub_53 : ∀ j, childrenC_53 j ⊆ insert (0, 0) required_53 := by decide
theorem child_envelope_sub_53 : ∀ j, childrenD_53 j ⊆ envelope_53 := by decide
theorem pivot_mem_53 : (0, 0) ∈ envelope_53 := by decide
theorem children_work_53 : ∀ j, Template HasSnaky 2 (childrenC_53 j) (childrenD_53 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_3 1 (0, 1)).mono (by decide)
theorem row_works_53 : Template HasSnaky 3 required_53 envelope_53 := by
  refine compose HasSnaky 2 childrenC_53 childrenD_53 children_work_53 (0, 0)
    required_53 envelope_53 pivot_mem_53 child_required_sub_53 child_envelope_sub_53 ?_
  intro b hb; exact common_sub_53 (mem_commonEnvelope childrenD_53 b hb)
def required_54 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_54 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_54 : Fin 2 → Finset Cell := ![(placedSet 0 (-2, -1) required_22), (placedSet 6 (-3, 0) required_3)]
def childrenD_54 : Fin 2 → Finset Cell := ![(placedSet 0 (-2, -1) envelope_22), (placedSet 6 (-3, 0) envelope_3)]
theorem common_sub_54 : commonEnvelope childrenD_54 ⊆ insert (0, 0) required_54 := by decide
theorem child_required_sub_54 : ∀ j, childrenC_54 j ⊆ insert (0, 0) required_54 := by decide
theorem child_envelope_sub_54 : ∀ j, childrenD_54 j ⊆ envelope_54 := by decide
theorem pivot_mem_54 : (0, 0) ∈ envelope_54 := by decide
theorem children_work_54 : ∀ j, Template HasSnaky 2 (childrenC_54 j) (childrenD_54 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_22 0 (-2, -1)).mono (by decide)
  · exact (placed_template_map row_works_3 6 (-3, 0)).mono (by decide)
theorem row_works_54 : Template HasSnaky 3 required_54 envelope_54 := by
  refine compose HasSnaky 2 childrenC_54 childrenD_54 children_work_54 (0, 0)
    required_54 envelope_54 pivot_mem_54 child_required_sub_54 child_envelope_sub_54 ?_
  intro b hb; exact common_sub_54 (mem_commonEnvelope childrenD_54 b hb)
def required_61 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -3), (-1, -2), (-1, -1), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_61 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -3), (-1, -2), (-1, -1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_61 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) required_6), (placedSet 1 (0, 1) required_14)]
def childrenD_61 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) envelope_6), (placedSet 1 (0, 1) envelope_14)]
theorem common_sub_61 : commonEnvelope childrenD_61 ⊆ insert (0, 0) required_61 := by decide
theorem child_required_sub_61 : ∀ j, childrenC_61 j ⊆ insert (0, 0) required_61 := by decide
theorem child_envelope_sub_61 : ∀ j, childrenD_61 j ⊆ envelope_61 := by decide
theorem pivot_mem_61 : (0, 0) ∈ envelope_61 := by decide
theorem children_work_61 : ∀ j, Template HasSnaky 2 (childrenC_61 j) (childrenD_61 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_14 1 (0, 1)).mono (by decide)
theorem row_works_61 : Template HasSnaky 3 required_61 envelope_61 := by
  refine compose HasSnaky 2 childrenC_61 childrenD_61 children_work_61 (0, 0)
    required_61 envelope_61 pivot_mem_61 child_required_sub_61 child_envelope_sub_61 ?_
  intro b hb; exact common_sub_61 (mem_commonEnvelope childrenD_61 b hb)
def required_71 : Finset Cell := ⟨(([(-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (1, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_71 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (2, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_71 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_6), (placedSet 2 (0, -1) required_23)]
def childrenD_71 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_6), (placedSet 2 (0, -1) envelope_23)]
theorem common_sub_71 : commonEnvelope childrenD_71 ⊆ insert (0, 0) required_71 := by decide
theorem child_required_sub_71 : ∀ j, childrenC_71 j ⊆ insert (0, 0) required_71 := by decide
theorem child_envelope_sub_71 : ∀ j, childrenD_71 j ⊆ envelope_71 := by decide
theorem pivot_mem_71 : (0, 0) ∈ envelope_71 := by decide
theorem children_work_71 : ∀ j, Template HasSnaky 2 (childrenC_71 j) (childrenD_71 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_23 2 (0, -1)).mono (by decide)
theorem row_works_71 : Template HasSnaky 3 required_71 envelope_71 := by
  refine compose HasSnaky 2 childrenC_71 childrenD_71 children_work_71 (0, 0)
    required_71 envelope_71 pivot_mem_71 child_required_sub_71 child_envelope_sub_71 ?_
  intro b hb; exact common_sub_71 (mem_commonEnvelope childrenD_71 b hb)
def required_76 : Finset Cell := ⟨(([(-1, 0), (0, -1), (1, 0), (1, 1), (1, 2), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_76 : Finset Cell := ⟨(([(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_76 : Fin 2 → Finset Cell := ![(placedSet 7 (1, 3) required_0), (placedSet 0 (3, 1) required_14)]
def childrenD_76 : Fin 2 → Finset Cell := ![(placedSet 7 (1, 3) envelope_0), (placedSet 0 (3, 1) envelope_14)]
theorem common_sub_76 : commonEnvelope childrenD_76 ⊆ insert (0, 0) required_76 := by decide
theorem child_required_sub_76 : ∀ j, childrenC_76 j ⊆ insert (0, 0) required_76 := by decide
theorem child_envelope_sub_76 : ∀ j, childrenD_76 j ⊆ envelope_76 := by decide
theorem pivot_mem_76 : (0, 0) ∈ envelope_76 := by decide
theorem children_work_76 : ∀ j, Template HasSnaky 2 (childrenC_76 j) (childrenD_76 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 7 (1, 3)).mono (by decide)
  · exact (placed_template_map row_works_14 0 (3, 1)).mono (by decide)
theorem row_works_76 : Template HasSnaky 3 required_76 envelope_76 := by
  refine compose HasSnaky 2 childrenC_76 childrenD_76 children_work_76 (0, 0)
    required_76 envelope_76 pivot_mem_76 child_required_sub_76 child_envelope_sub_76 ?_
  intro b hb; exact common_sub_76 (mem_commonEnvelope childrenD_76 b hb)
end SnakyConditional

end OAI
