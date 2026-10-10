import OAI.GameTheory.SnakyConditional.Templates.Level06Part01
import OAI.GameTheory.SnakyConditional.Templates.Level06Part02

namespace OAI

namespace SnakyConditional
def required_60 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-1, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_60 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0), (1, 1), (2, 0), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_60 : Fin 2 → Finset Cell := ![(placedSet 6 (-3, -1) required_6), (placedSet 1 (2, 0) required_49)]
def childrenD_60 : Fin 2 → Finset Cell := ![(placedSet 6 (-3, -1) envelope_6), (placedSet 1 (2, 0) envelope_49)]
theorem common_sub_60 : commonEnvelope childrenD_60 ⊆ insert (0, 0) required_60 := by decide
theorem child_required_sub_60 : ∀ j, childrenC_60 j ⊆ insert (0, 0) required_60 := by decide
theorem child_envelope_sub_60 : ∀ j, childrenD_60 j ⊆ envelope_60 := by decide
theorem pivot_mem_60 : (0, 0) ∈ envelope_60 := by decide
theorem children_work_60 : ∀ j, Template HasSnaky 4 (childrenC_60 j) (childrenD_60 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 6 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_49 1 (2, 0)).mono (by decide)
theorem row_works_60 : Template HasSnaky 5 required_60 envelope_60 := by
  refine compose HasSnaky 4 childrenC_60 childrenD_60 children_work_60 (0, 0)
    required_60 envelope_60 pivot_mem_60 child_required_sub_60 child_envelope_sub_60 ?_
  intro b hb; exact common_sub_60 (mem_commonEnvelope childrenD_60 b hb)
def required_63 : Finset Cell := ⟨(([(1, -4), (1, -3), (1, -2), (1, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_63 : Finset Cell := ⟨(([(0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_63 : Fin 2 → Finset Cell := ![(placedSet 3 (0, -1) required_4), (placedSet 0 (1, 0) required_50)]
def childrenD_63 : Fin 2 → Finset Cell := ![(placedSet 3 (0, -1) envelope_4), (placedSet 0 (1, 0) envelope_50)]
theorem common_sub_63 : commonEnvelope childrenD_63 ⊆ insert (0, 0) required_63 := by decide
theorem child_required_sub_63 : ∀ j, childrenC_63 j ⊆ insert (0, 0) required_63 := by decide
theorem child_envelope_sub_63 : ∀ j, childrenD_63 j ⊆ envelope_63 := by decide
theorem pivot_mem_63 : (0, 0) ∈ envelope_63 := by decide
theorem children_work_63 : ∀ j, Template HasSnaky 4 (childrenC_63 j) (childrenD_63 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_4 3 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_50 0 (1, 0)).mono (by decide)
theorem row_works_63 : Template HasSnaky 5 required_63 envelope_63 := by
  refine compose HasSnaky 4 childrenC_63 childrenD_63 children_work_63 (0, 0)
    required_63 envelope_63 pivot_mem_63 child_required_sub_63 child_envelope_sub_63 ?_
  intro b hb; exact common_sub_63 (mem_commonEnvelope childrenD_63 b hb)
def required_64 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_64 : Finset Cell := ⟨(([(-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1), (3, 1), (3, 2), (4, 1), (4, 2), (5, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_64 : Fin 2 → Finset Cell := ![(placedSet 6 (-1, 0) required_6), (placedSet 1 (4, 1) required_49)]
def childrenD_64 : Fin 2 → Finset Cell := ![(placedSet 6 (-1, 0) envelope_6), (placedSet 1 (4, 1) envelope_49)]
theorem common_sub_64 : commonEnvelope childrenD_64 ⊆ insert (0, 0) required_64 := by decide
theorem child_required_sub_64 : ∀ j, childrenC_64 j ⊆ insert (0, 0) required_64 := by decide
theorem child_envelope_sub_64 : ∀ j, childrenD_64 j ⊆ envelope_64 := by decide
theorem pivot_mem_64 : (0, 0) ∈ envelope_64 := by decide
theorem children_work_64 : ∀ j, Template HasSnaky 4 (childrenC_64 j) (childrenD_64 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 6 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_49 1 (4, 1)).mono (by decide)
theorem row_works_64 : Template HasSnaky 5 required_64 envelope_64 := by
  refine compose HasSnaky 4 childrenC_64 childrenD_64 children_work_64 (0, 0)
    required_64 envelope_64 pivot_mem_64 child_required_sub_64 child_envelope_sub_64 ?_
  intro b hb; exact common_sub_64 (mem_commonEnvelope childrenD_64 b hb)
def required_65 : Finset Cell := ⟨(([(-3, -1), (-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_65 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_65 : Fin 2 → Finset Cell := ![(placedSet 6 (-4, -1) required_6), (placedSet 1 (1, 0) required_49)]
def childrenD_65 : Fin 2 → Finset Cell := ![(placedSet 6 (-4, -1) envelope_6), (placedSet 1 (1, 0) envelope_49)]
theorem common_sub_65 : commonEnvelope childrenD_65 ⊆ insert (0, 0) required_65 := by decide
theorem child_required_sub_65 : ∀ j, childrenC_65 j ⊆ insert (0, 0) required_65 := by decide
theorem child_envelope_sub_65 : ∀ j, childrenD_65 j ⊆ envelope_65 := by decide
theorem pivot_mem_65 : (0, 0) ∈ envelope_65 := by decide
theorem children_work_65 : ∀ j, Template HasSnaky 4 (childrenC_65 j) (childrenD_65 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 6 (-4, -1)).mono (by decide)
  · exact (placed_template_map row_works_49 1 (1, 0)).mono (by decide)
theorem row_works_65 : Template HasSnaky 5 required_65 envelope_65 := by
  refine compose HasSnaky 4 childrenC_65 childrenD_65 children_work_65 (0, 0)
    required_65 envelope_65 pivot_mem_65 child_required_sub_65 child_envelope_sub_65 ?_
  intro b hb; exact common_sub_65 (mem_commonEnvelope childrenD_65 b hb)
def required_68 : Finset Cell := ⟨(([(-3, 0), (-3, 1), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_68 : Finset Cell := ⟨(([(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_68 : Fin 2 → Finset Cell := ![(placedSet 4 (-4, 1) required_6), (placedSet 0 (1, 0) required_44)]
def childrenD_68 : Fin 2 → Finset Cell := ![(placedSet 4 (-4, 1) envelope_6), (placedSet 0 (1, 0) envelope_44)]
theorem common_sub_68 : commonEnvelope childrenD_68 ⊆ insert (0, 0) required_68 := by decide
theorem child_required_sub_68 : ∀ j, childrenC_68 j ⊆ insert (0, 0) required_68 := by decide
theorem child_envelope_sub_68 : ∀ j, childrenD_68 j ⊆ envelope_68 := by decide
theorem pivot_mem_68 : (0, 0) ∈ envelope_68 := by decide
theorem children_work_68 : ∀ j, Template HasSnaky 4 (childrenC_68 j) (childrenD_68 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 4 (-4, 1)).mono (by decide)
  · exact (placed_template_map row_works_44 0 (1, 0)).mono (by decide)
theorem row_works_68 : Template HasSnaky 5 required_68 envelope_68 := by
  refine compose HasSnaky 4 childrenC_68 childrenD_68 children_work_68 (0, 0)
    required_68 envelope_68 pivot_mem_68 child_required_sub_68 child_envelope_sub_68 ?_
  intro b hb; exact common_sub_68 (mem_commonEnvelope childrenD_68 b hb)
def required_73 : Finset Cell := ⟨(([(-1, 1), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_73 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_73 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, 0) required_4), (placedSet 0 (0, 1) required_50)]
def childrenD_73 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, 0) envelope_4), (placedSet 0 (0, 1) envelope_50)]
theorem common_sub_73 : commonEnvelope childrenD_73 ⊆ insert (0, 0) required_73 := by decide
theorem child_required_sub_73 : ∀ j, childrenC_73 j ⊆ insert (0, 0) required_73 := by decide
theorem child_envelope_sub_73 : ∀ j, childrenD_73 j ⊆ envelope_73 := by decide
theorem pivot_mem_73 : (0, 0) ∈ envelope_73 := by decide
theorem children_work_73 : ∀ j, Template HasSnaky 4 (childrenC_73 j) (childrenD_73 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_4 3 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_50 0 (0, 1)).mono (by decide)
theorem row_works_73 : Template HasSnaky 5 required_73 envelope_73 := by
  refine compose HasSnaky 4 childrenC_73 childrenD_73 children_work_73 (0, 0)
    required_73 envelope_73 pivot_mem_73 child_required_sub_73 child_envelope_sub_73 ?_
  intro b hb; exact common_sub_73 (mem_commonEnvelope childrenD_73 b hb)
def required_83 : Finset Cell := ⟨(([(0, -1), (1, -1), (1, 0), (1, 1), (1, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_83 : Finset Cell := ⟨(([(-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (3, -1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_83 : Fin 2 → Finset Cell := ![(placedSet 7 (1, 3) required_0), (placedSet 2 (2, -1) required_67)]
def childrenD_83 : Fin 2 → Finset Cell := ![(placedSet 7 (1, 3) envelope_0), (placedSet 2 (2, -1) envelope_67)]
theorem common_sub_83 : commonEnvelope childrenD_83 ⊆ insert (0, 0) required_83 := by decide
theorem child_required_sub_83 : ∀ j, childrenC_83 j ⊆ insert (0, 0) required_83 := by decide
theorem child_envelope_sub_83 : ∀ j, childrenD_83 j ⊆ envelope_83 := by decide
theorem pivot_mem_83 : (0, 0) ∈ envelope_83 := by decide
theorem children_work_83 : ∀ j, Template HasSnaky 4 (childrenC_83 j) (childrenD_83 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 7 (1, 3)).mono (by decide)
  · exact (placed_template_map row_works_67 2 (2, -1)).mono (by decide)
theorem row_works_83 : Template HasSnaky 5 required_83 envelope_83 := by
  refine compose HasSnaky 4 childrenC_83 childrenD_83 children_work_83 (0, 0)
    required_83 envelope_83 pivot_mem_83 child_required_sub_83 child_envelope_sub_83 ?_
  intro b hb; exact common_sub_83 (mem_commonEnvelope childrenD_83 b hb)
end SnakyConditional

end OAI
