import OAI.GameTheory.SnakyConditional.Templates.Level05Part01
import OAI.GameTheory.SnakyConditional.Templates.Level05Part03

namespace OAI

namespace SnakyConditional
def required_44 : Finset Cell := ⟨(([(-4, 0), (-4, 1), (-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_44 : Finset Cell := ⟨(([(-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_44 : Fin 2 → Finset Cell := ![(placedSet 4 (-3, 1) required_4), (placedSet 0 (0, 1) required_7)]
def childrenD_44 : Fin 2 → Finset Cell := ![(placedSet 4 (-3, 1) envelope_4), (placedSet 0 (0, 1) envelope_7)]
theorem common_sub_44 : commonEnvelope childrenD_44 ⊆ insert (0, 0) required_44 := by decide
theorem child_required_sub_44 : ∀ j, childrenC_44 j ⊆ insert (0, 0) required_44 := by decide
theorem child_envelope_sub_44 : ∀ j, childrenD_44 j ⊆ envelope_44 := by decide
theorem pivot_mem_44 : (0, 0) ∈ envelope_44 := by decide
theorem children_work_44 : ∀ j, Template HasSnaky 3 (childrenC_44 j) (childrenD_44 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_4 4 (-3, 1)).mono (by decide)
  · exact (placed_template_map row_works_7 0 (0, 1)).mono (by decide)
theorem row_works_44 : Template HasSnaky 4 required_44 envelope_44 := by
  refine compose HasSnaky 3 childrenC_44 childrenD_44 children_work_44 (0, 0)
    required_44 envelope_44 pivot_mem_44 child_required_sub_44 child_envelope_sub_44 ?_
  intro b hb; exact common_sub_44 (mem_commonEnvelope childrenD_44 b hb)
def required_45 : Finset Cell := ⟨(([(-4, 0), (-3, 0), (-3, 1), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_45 : Finset Cell := ⟨(([(-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_45 : Fin 2 → Finset Cell := ![(placedSet 4 (-4, 1) required_6), (placedSet 0 (0, 1) required_7)]
def childrenD_45 : Fin 2 → Finset Cell := ![(placedSet 4 (-4, 1) envelope_6), (placedSet 0 (0, 1) envelope_7)]
theorem common_sub_45 : commonEnvelope childrenD_45 ⊆ insert (0, 0) required_45 := by decide
theorem child_required_sub_45 : ∀ j, childrenC_45 j ⊆ insert (0, 0) required_45 := by decide
theorem child_envelope_sub_45 : ∀ j, childrenD_45 j ⊆ envelope_45 := by decide
theorem pivot_mem_45 : (0, 0) ∈ envelope_45 := by decide
theorem children_work_45 : ∀ j, Template HasSnaky 3 (childrenC_45 j) (childrenD_45 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 4 (-4, 1)).mono (by decide)
  · exact (placed_template_map row_works_7 0 (0, 1)).mono (by decide)
theorem row_works_45 : Template HasSnaky 4 required_45 envelope_45 := by
  refine compose HasSnaky 3 childrenC_45 childrenD_45 children_work_45 (0, 0)
    required_45 envelope_45 pivot_mem_45 child_required_sub_45 child_envelope_sub_45 ?_
  intro b hb; exact common_sub_45 (mem_commonEnvelope childrenD_45 b hb)
def required_46 : Finset Cell := ⟨(([(-4, 0), (-3, -1), (-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_46 : Finset Cell := ⟨(([(-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_46 : Fin 2 → Finset Cell := ![(placedSet 6 (-4, -1) required_6), (placedSet 0 (0, 1) required_7)]
def childrenD_46 : Fin 2 → Finset Cell := ![(placedSet 6 (-4, -1) envelope_6), (placedSet 0 (0, 1) envelope_7)]
theorem common_sub_46 : commonEnvelope childrenD_46 ⊆ insert (0, 0) required_46 := by decide
theorem child_required_sub_46 : ∀ j, childrenC_46 j ⊆ insert (0, 0) required_46 := by decide
theorem child_envelope_sub_46 : ∀ j, childrenD_46 j ⊆ envelope_46 := by decide
theorem pivot_mem_46 : (0, 0) ∈ envelope_46 := by decide
theorem children_work_46 : ∀ j, Template HasSnaky 3 (childrenC_46 j) (childrenD_46 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 6 (-4, -1)).mono (by decide)
  · exact (placed_template_map row_works_7 0 (0, 1)).mono (by decide)
theorem row_works_46 : Template HasSnaky 4 required_46 envelope_46 := by
  refine compose HasSnaky 3 childrenC_46 childrenD_46 children_work_46 (0, 0)
    required_46 envelope_46 pivot_mem_46 child_required_sub_46 child_envelope_sub_46 ?_
  intro b hb; exact common_sub_46 (mem_commonEnvelope childrenD_46 b hb)
def required_49 : Finset Cell := ⟨(([(-1, -4), (0, -4), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_49 : Finset Cell := ⟨(([(-1, -4), (-1, -3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_49 : Fin 2 → Finset Cell := ![(placedSet 7 (-1, -3) required_4), (placedSet 1 (1, 0) required_7)]
def childrenD_49 : Fin 2 → Finset Cell := ![(placedSet 7 (-1, -3) envelope_4), (placedSet 1 (1, 0) envelope_7)]
theorem common_sub_49 : commonEnvelope childrenD_49 ⊆ insert (0, 0) required_49 := by decide
theorem child_required_sub_49 : ∀ j, childrenC_49 j ⊆ insert (0, 0) required_49 := by decide
theorem child_envelope_sub_49 : ∀ j, childrenD_49 j ⊆ envelope_49 := by decide
theorem pivot_mem_49 : (0, 0) ∈ envelope_49 := by decide
theorem children_work_49 : ∀ j, Template HasSnaky 3 (childrenC_49 j) (childrenD_49 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_4 7 (-1, -3)).mono (by decide)
  · exact (placed_template_map row_works_7 1 (1, 0)).mono (by decide)
theorem row_works_49 : Template HasSnaky 4 required_49 envelope_49 := by
  refine compose HasSnaky 3 childrenC_49 childrenD_49 children_work_49 (0, 0)
    required_49 envelope_49 pivot_mem_49 child_required_sub_49 child_envelope_sub_49 ?_
  intro b hb; exact common_sub_49 (mem_commonEnvelope childrenD_49 b hb)
def required_50 : Finset Cell := ⟨(([(-1, 0), (0, -4), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_50 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_50 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, 1) required_6), (placedSet 1 (1, 0) required_7)]
def childrenD_50 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, 1) envelope_6), (placedSet 1 (1, 0) envelope_7)]
theorem common_sub_50 : commonEnvelope childrenD_50 ⊆ insert (0, 0) required_50 := by decide
theorem child_required_sub_50 : ∀ j, childrenC_50 j ⊆ insert (0, 0) required_50 := by decide
theorem child_envelope_sub_50 : ∀ j, childrenD_50 j ⊆ envelope_50 := by decide
theorem pivot_mem_50 : (0, 0) ∈ envelope_50 := by decide
theorem children_work_50 : ∀ j, Template HasSnaky 3 (childrenC_50 j) (childrenD_50 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_7 1 (1, 0)).mono (by decide)
theorem row_works_50 : Template HasSnaky 4 required_50 envelope_50 := by
  refine compose HasSnaky 3 childrenC_50 childrenD_50 children_work_50 (0, 0)
    required_50 envelope_50 pivot_mem_50 child_required_sub_50 child_envelope_sub_50 ?_
  intro b hb; exact common_sub_50 (mem_commonEnvelope childrenD_50 b hb)
def required_51 : Finset Cell := ⟨(([(-3, -1), (-3, 0), (-2, -1), (-2, 0), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_51 : Finset Cell := ⟨(([(-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_51 : Fin 4 → Finset Cell := ![(placedSet 2 (1, -1) required_10), (placedSet 0 (1, 0) required_10), (placedSet 2 (-1, 0) required_26), (placedSet 0 (-1, -1) required_26)]
def childrenD_51 : Fin 4 → Finset Cell := ![(placedSet 2 (1, -1) envelope_10), (placedSet 0 (1, 0) envelope_10), (placedSet 2 (-1, 0) envelope_26), (placedSet 0 (-1, -1) envelope_26)]
theorem common_sub_51 : commonEnvelope childrenD_51 ⊆ insert (0, 0) required_51 := by decide
theorem child_required_sub_51 : ∀ j, childrenC_51 j ⊆ insert (0, 0) required_51 := by decide
theorem child_envelope_sub_51 : ∀ j, childrenD_51 j ⊆ envelope_51 := by decide
theorem pivot_mem_51 : (0, 0) ∈ envelope_51 := by decide
theorem children_work_51 : ∀ j, Template HasSnaky 3 (childrenC_51 j) (childrenD_51 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_10 2 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_10 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_26 2 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_26 0 (-1, -1)).mono (by decide)
theorem row_works_51 : Template HasSnaky 4 required_51 envelope_51 := by
  refine compose HasSnaky 3 childrenC_51 childrenD_51 children_work_51 (0, 0)
    required_51 envelope_51 pivot_mem_51 child_required_sub_51 child_envelope_sub_51 ?_
  intro b hb; exact common_sub_51 (mem_commonEnvelope childrenD_51 b hb)
def required_55 : Finset Cell := ⟨(([(-4, 0), (-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_55 : Finset Cell := ⟨(([(-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_55 : Fin 2 → Finset Cell := ![(placedSet 4 (-4, 1) required_7), (placedSet 0 (0, 1) required_7)]
def childrenD_55 : Fin 2 → Finset Cell := ![(placedSet 4 (-4, 1) envelope_7), (placedSet 0 (0, 1) envelope_7)]
theorem common_sub_55 : commonEnvelope childrenD_55 ⊆ insert (0, 0) required_55 := by decide
theorem child_required_sub_55 : ∀ j, childrenC_55 j ⊆ insert (0, 0) required_55 := by decide
theorem child_envelope_sub_55 : ∀ j, childrenD_55 j ⊆ envelope_55 := by decide
theorem pivot_mem_55 : (0, 0) ∈ envelope_55 := by decide
theorem children_work_55 : ∀ j, Template HasSnaky 3 (childrenC_55 j) (childrenD_55 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_7 4 (-4, 1)).mono (by decide)
  · exact (placed_template_map row_works_7 0 (0, 1)).mono (by decide)
theorem row_works_55 : Template HasSnaky 4 required_55 envelope_55 := by
  refine compose HasSnaky 3 childrenC_55 childrenD_55 children_work_55 (0, 0)
    required_55 envelope_55 pivot_mem_55 child_required_sub_55 child_envelope_sub_55 ?_
  intro b hb; exact common_sub_55 (mem_commonEnvelope childrenD_55 b hb)
end SnakyConditional

end OAI
