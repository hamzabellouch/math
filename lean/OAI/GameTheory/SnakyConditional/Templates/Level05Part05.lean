import OAI.GameTheory.SnakyConditional.Templates.Level04Part01
import OAI.GameTheory.SnakyConditional.Templates.Level04Part03
import OAI.GameTheory.SnakyConditional.Templates.Level04Part04

namespace OAI

namespace SnakyConditional
def required_36 : Finset Cell := ⟨(([(1, 0), (2, 0), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_36 : Finset Cell := ⟨(([(-1, 0), (0, 0), (1, 0), (2, 0), (2, 1), (3, 0), (3, 1), (4, 1), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_36 : Fin 2 → Finset Cell := ![(placedSet 0 (-1, 0) required_0), (placedSet 0 (4, 1) required_17)]
def childrenD_36 : Fin 2 → Finset Cell := ![(placedSet 0 (-1, 0) envelope_0), (placedSet 0 (4, 1) envelope_17)]
theorem common_sub_36 : commonEnvelope childrenD_36 ⊆ insert (0, 0) required_36 := by decide
theorem child_required_sub_36 : ∀ j, childrenC_36 j ⊆ insert (0, 0) required_36 := by decide
theorem child_envelope_sub_36 : ∀ j, childrenD_36 j ⊆ envelope_36 := by decide
theorem pivot_mem_36 : (0, 0) ∈ envelope_36 := by decide
theorem children_work_36 : ∀ j, Template HasSnaky 2 (childrenC_36 j) (childrenD_36 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 0 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_17 0 (4, 1)).mono (by decide)
theorem row_works_36 : Template HasSnaky 3 required_36 envelope_36 := by
  refine compose HasSnaky 2 childrenC_36 childrenD_36 children_work_36 (0, 0)
    required_36 envelope_36 pivot_mem_36 child_required_sub_36 child_envelope_sub_36 ?_
  intro b hb; exact common_sub_36 (mem_commonEnvelope childrenD_36 b hb)
def required_37 : Finset Cell := ⟨(([(1, -3), (1, -2), (1, -1), (1, 0), (3, -1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_37 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_37 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_6), (placedSet 4 (2, -1) required_2)]
def childrenD_37 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_6), (placedSet 4 (2, -1) envelope_2)]
theorem common_sub_37 : commonEnvelope childrenD_37 ⊆ insert (0, 0) required_37 := by decide
theorem child_required_sub_37 : ∀ j, childrenC_37 j ⊆ insert (0, 0) required_37 := by decide
theorem child_envelope_sub_37 : ∀ j, childrenD_37 j ⊆ envelope_37 := by decide
theorem pivot_mem_37 : (0, 0) ∈ envelope_37 := by decide
theorem children_work_37 : ∀ j, Template HasSnaky 2 (childrenC_37 j) (childrenD_37 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_2 4 (2, -1)).mono (by decide)
theorem row_works_37 : Template HasSnaky 3 required_37 envelope_37 := by
  refine compose HasSnaky 2 childrenC_37 childrenD_37 children_work_37 (0, 0)
    required_37 envelope_37 pivot_mem_37 child_required_sub_37 child_envelope_sub_37 ?_
  intro b hb; exact common_sub_37 (mem_commonEnvelope childrenD_37 b hb)
def required_38 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-2, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_38 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_38 : Fin 2 → Finset Cell := ![(placedSet 0 (-1, -1) required_3), (placedSet 0 (-2, 0) required_16)]
def childrenD_38 : Fin 2 → Finset Cell := ![(placedSet 0 (-1, -1) envelope_3), (placedSet 0 (-2, 0) envelope_16)]
theorem common_sub_38 : commonEnvelope childrenD_38 ⊆ insert (0, 0) required_38 := by decide
theorem child_required_sub_38 : ∀ j, childrenC_38 j ⊆ insert (0, 0) required_38 := by decide
theorem child_envelope_sub_38 : ∀ j, childrenD_38 j ⊆ envelope_38 := by decide
theorem pivot_mem_38 : (0, 0) ∈ envelope_38 := by decide
theorem children_work_38 : ∀ j, Template HasSnaky 2 (childrenC_38 j) (childrenD_38 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_3 0 (-1, -1)).mono (by decide)
  · exact (placed_template_map row_works_16 0 (-2, 0)).mono (by decide)
theorem row_works_38 : Template HasSnaky 3 required_38 envelope_38 := by
  refine compose HasSnaky 2 childrenC_38 childrenD_38 children_work_38 (0, 0)
    required_38 envelope_38 pivot_mem_38 child_required_sub_38 child_envelope_sub_38 ?_
  intro b hb; exact common_sub_38 (mem_commonEnvelope childrenD_38 b hb)
def required_39 : Finset Cell := ⟨(([(-2, -1), (-1, -1), (0, -1), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_39 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -1), (0, -1), (0, 0), (1, -1), (1, 0), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_39 : Fin 2 → Finset Cell := ![(placedSet 0 (-3, -1) required_0), (placedSet 0 (2, 0) required_17)]
def childrenD_39 : Fin 2 → Finset Cell := ![(placedSet 0 (-3, -1) envelope_0), (placedSet 0 (2, 0) envelope_17)]
theorem common_sub_39 : commonEnvelope childrenD_39 ⊆ insert (0, 0) required_39 := by decide
theorem child_required_sub_39 : ∀ j, childrenC_39 j ⊆ insert (0, 0) required_39 := by decide
theorem child_envelope_sub_39 : ∀ j, childrenD_39 j ⊆ envelope_39 := by decide
theorem pivot_mem_39 : (0, 0) ∈ envelope_39 := by decide
theorem children_work_39 : ∀ j, Template HasSnaky 2 (childrenC_39 j) (childrenD_39 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 0 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_17 0 (2, 0)).mono (by decide)
theorem row_works_39 : Template HasSnaky 3 required_39 envelope_39 := by
  refine compose HasSnaky 2 childrenC_39 childrenD_39 children_work_39 (0, 0)
    required_39 envelope_39 pivot_mem_39 child_required_sub_39 child_envelope_sub_39 ?_
  intro b hb; exact common_sub_39 (mem_commonEnvelope childrenD_39 b hb)
def required_40 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -1), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_40 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_40 : Fin 2 → Finset Cell := ![(placedSet 0 (0, -1) required_3), (placedSet 0 (-1, 0) required_16)]
def childrenD_40 : Fin 2 → Finset Cell := ![(placedSet 0 (0, -1) envelope_3), (placedSet 0 (-1, 0) envelope_16)]
theorem common_sub_40 : commonEnvelope childrenD_40 ⊆ insert (0, 0) required_40 := by decide
theorem child_required_sub_40 : ∀ j, childrenC_40 j ⊆ insert (0, 0) required_40 := by decide
theorem child_envelope_sub_40 : ∀ j, childrenD_40 j ⊆ envelope_40 := by decide
theorem pivot_mem_40 : (0, 0) ∈ envelope_40 := by decide
theorem children_work_40 : ∀ j, Template HasSnaky 2 (childrenC_40 j) (childrenD_40 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_3 0 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_16 0 (-1, 0)).mono (by decide)
theorem row_works_40 : Template HasSnaky 3 required_40 envelope_40 := by
  refine compose HasSnaky 2 childrenC_40 childrenD_40 children_work_40 (0, 0)
    required_40 envelope_40 pivot_mem_40 child_required_sub_40 child_envelope_sub_40 ?_
  intro b hb; exact common_sub_40 (mem_commonEnvelope childrenD_40 b hb)
end SnakyConditional

end OAI
