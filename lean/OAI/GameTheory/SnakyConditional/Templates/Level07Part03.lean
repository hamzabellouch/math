import OAI.GameTheory.SnakyConditional.Templates.Level06Part01
import OAI.GameTheory.SnakyConditional.Templates.Level06Part02
import OAI.GameTheory.SnakyConditional.Templates.Level06Part03
import OAI.GameTheory.SnakyConditional.Templates.Level06Part05

namespace OAI

namespace SnakyConditional
def required_104 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -1), (0, -1), (1, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_104 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_104 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) required_6), (placedSet 0 (-1, 0) required_75)]
def childrenD_104 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) envelope_6), (placedSet 0 (-1, 0) envelope_75)]
theorem common_sub_104 : commonEnvelope childrenD_104 ⊆ insert (0, 0) required_104 := by decide
theorem child_required_sub_104 : ∀ j, childrenC_104 j ⊆ insert (0, 0) required_104 := by decide
theorem child_envelope_sub_104 : ∀ j, childrenD_104 j ⊆ envelope_104 := by decide
theorem pivot_mem_104 : (0, 0) ∈ envelope_104 := by decide
theorem children_work_104 : ∀ j, Template HasSnaky 4 (childrenC_104 j) (childrenD_104 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_75 0 (-1, 0)).mono (by decide)
theorem row_works_104 : Template HasSnaky 5 required_104 envelope_104 := by
  refine compose HasSnaky 4 childrenC_104 childrenD_104 children_work_104 (0, 0)
    required_104 envelope_104 pivot_mem_104 child_required_sub_104 child_envelope_sub_104 ?_
  intro b hb; exact common_sub_104 (mem_commonEnvelope childrenD_104 b hb)
def required_109 : Finset Cell := ⟨(([(-4, -1), (-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_109 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_109 : Fin 2 → Finset Cell := ![(placedSet 6 (-3, -1) required_4), (placedSet 0 (1, 0) required_55)]
def childrenD_109 : Fin 2 → Finset Cell := ![(placedSet 6 (-3, -1) envelope_4), (placedSet 0 (1, 0) envelope_55)]
theorem common_sub_109 : commonEnvelope childrenD_109 ⊆ insert (0, 0) required_109 := by decide
theorem child_required_sub_109 : ∀ j, childrenC_109 j ⊆ insert (0, 0) required_109 := by decide
theorem child_envelope_sub_109 : ∀ j, childrenD_109 j ⊆ envelope_109 := by decide
theorem pivot_mem_109 : (0, 0) ∈ envelope_109 := by decide
theorem children_work_109 : ∀ j, Template HasSnaky 4 (childrenC_109 j) (childrenD_109 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_4 6 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_55 0 (1, 0)).mono (by decide)
theorem row_works_109 : Template HasSnaky 5 required_109 envelope_109 := by
  refine compose HasSnaky 4 childrenC_109 childrenD_109 children_work_109 (0, 0)
    required_109 envelope_109 pivot_mem_109 child_required_sub_109 child_envelope_sub_109 ?_
  intro b hb; exact common_sub_109 (mem_commonEnvelope childrenD_109 b hb)
def required_112 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (1, 1), (2, 0), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_112 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_112 : Fin 2 → Finset Cell := ![(placedSet 1 (1, 0) required_4), (placedSet 0 (-1, 1) required_93)]
def childrenD_112 : Fin 2 → Finset Cell := ![(placedSet 1 (1, 0) envelope_4), (placedSet 0 (-1, 1) envelope_93)]
theorem common_sub_112 : commonEnvelope childrenD_112 ⊆ insert (0, 0) required_112 := by decide
theorem child_required_sub_112 : ∀ j, childrenC_112 j ⊆ insert (0, 0) required_112 := by decide
theorem child_envelope_sub_112 : ∀ j, childrenD_112 j ⊆ envelope_112 := by decide
theorem pivot_mem_112 : (0, 0) ∈ envelope_112 := by decide
theorem children_work_112 : ∀ j, Template HasSnaky 4 (childrenC_112 j) (childrenD_112 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_4 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_93 0 (-1, 1)).mono (by decide)
theorem row_works_112 : Template HasSnaky 5 required_112 envelope_112 := by
  refine compose HasSnaky 4 childrenC_112 childrenD_112 children_work_112 (0, 0)
    required_112 envelope_112 pivot_mem_112 child_required_sub_112 child_envelope_sub_112 ?_
  intro b hb; exact common_sub_112 (mem_commonEnvelope childrenD_112 b hb)
def required_114 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-1, -1), (-1, 0), (1, 0), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_114 : Finset Cell := ⟨(([(-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (1, 0), (1, 1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_114 : Fin 2 → Finset Cell := ![(placedSet 0 (2, 1) required_6), (placedSet 3 (-2, 1) required_67)]
def childrenD_114 : Fin 2 → Finset Cell := ![(placedSet 0 (2, 1) envelope_6), (placedSet 3 (-2, 1) envelope_67)]
theorem common_sub_114 : commonEnvelope childrenD_114 ⊆ insert (0, 0) required_114 := by decide
theorem child_required_sub_114 : ∀ j, childrenC_114 j ⊆ insert (0, 0) required_114 := by decide
theorem child_envelope_sub_114 : ∀ j, childrenD_114 j ⊆ envelope_114 := by decide
theorem pivot_mem_114 : (0, 0) ∈ envelope_114 := by decide
theorem children_work_114 : ∀ j, Template HasSnaky 4 (childrenC_114 j) (childrenD_114 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 0 (2, 1)).mono (by decide)
  · exact (placed_template_map row_works_67 3 (-2, 1)).mono (by decide)
theorem row_works_114 : Template HasSnaky 5 required_114 envelope_114 := by
  refine compose HasSnaky 4 childrenC_114 childrenD_114 children_work_114 (0, 0)
    required_114 envelope_114 pivot_mem_114 child_required_sub_114 child_envelope_sub_114 ?_
  intro b hb; exact common_sub_114 (mem_commonEnvelope childrenD_114 b hb)
def required_115 : Finset Cell := ⟨(([(-1, -3), (-1, -1), (-1, 0), (1, 0), (2, -1), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_115 : Finset Cell := ⟨(([(-3, 1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, 0), (1, 0), (2, -1), (2, 0), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_115 : Fin 2 → Finset Cell := ![(placedSet 2 (3, -1) required_6), (placedSet 7 (-2, 1) required_70)]
def childrenD_115 : Fin 2 → Finset Cell := ![(placedSet 2 (3, -1) envelope_6), (placedSet 7 (-2, 1) envelope_70)]
theorem common_sub_115 : commonEnvelope childrenD_115 ⊆ insert (0, 0) required_115 := by decide
theorem child_required_sub_115 : ∀ j, childrenC_115 j ⊆ insert (0, 0) required_115 := by decide
theorem child_envelope_sub_115 : ∀ j, childrenD_115 j ⊆ envelope_115 := by decide
theorem pivot_mem_115 : (0, 0) ∈ envelope_115 := by decide
theorem children_work_115 : ∀ j, Template HasSnaky 4 (childrenC_115 j) (childrenD_115 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 2 (3, -1)).mono (by decide)
  · exact (placed_template_map row_works_70 7 (-2, 1)).mono (by decide)
theorem row_works_115 : Template HasSnaky 5 required_115 envelope_115 := by
  refine compose HasSnaky 4 childrenC_115 childrenD_115 children_work_115 (0, 0)
    required_115 envelope_115 pivot_mem_115 child_required_sub_115 child_envelope_sub_115 ?_
  intro b hb; exact common_sub_115 (mem_commonEnvelope childrenD_115 b hb)
def required_117 : Finset Cell := ⟨(([(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (1, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_117 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (2, -1), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_117 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_6), (placedSet 0 (1, 0) required_100)]
def childrenD_117 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_6), (placedSet 0 (1, 0) envelope_100)]
theorem common_sub_117 : commonEnvelope childrenD_117 ⊆ insert (0, 0) required_117 := by decide
theorem child_required_sub_117 : ∀ j, childrenC_117 j ⊆ insert (0, 0) required_117 := by decide
theorem child_envelope_sub_117 : ∀ j, childrenD_117 j ⊆ envelope_117 := by decide
theorem pivot_mem_117 : (0, 0) ∈ envelope_117 := by decide
theorem children_work_117 : ∀ j, Template HasSnaky 4 (childrenC_117 j) (childrenD_117 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_100 0 (1, 0)).mono (by decide)
theorem row_works_117 : Template HasSnaky 5 required_117 envelope_117 := by
  refine compose HasSnaky 4 childrenC_117 childrenD_117 children_work_117 (0, 0)
    required_117 envelope_117 pivot_mem_117 child_required_sub_117 child_envelope_sub_117 ?_
  intro b hb; exact common_sub_117 (mem_commonEnvelope childrenD_117 b hb)
def required_119 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-1, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_119 : Finset Cell := ⟨(([(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (1, 0), (1, 1), (2, 0), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_119 : Fin 2 → Finset Cell := ![(placedSet 6 (-3, -1) required_6), (placedSet 0 (2, 0) required_55)]
def childrenD_119 : Fin 2 → Finset Cell := ![(placedSet 6 (-3, -1) envelope_6), (placedSet 0 (2, 0) envelope_55)]
theorem common_sub_119 : commonEnvelope childrenD_119 ⊆ insert (0, 0) required_119 := by decide
theorem child_required_sub_119 : ∀ j, childrenC_119 j ⊆ insert (0, 0) required_119 := by decide
theorem child_envelope_sub_119 : ∀ j, childrenD_119 j ⊆ envelope_119 := by decide
theorem pivot_mem_119 : (0, 0) ∈ envelope_119 := by decide
theorem children_work_119 : ∀ j, Template HasSnaky 4 (childrenC_119 j) (childrenD_119 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 6 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_55 0 (2, 0)).mono (by decide)
theorem row_works_119 : Template HasSnaky 5 required_119 envelope_119 := by
  refine compose HasSnaky 4 childrenC_119 childrenD_119 children_work_119 (0, 0)
    required_119 envelope_119 pivot_mem_119 child_required_sub_119 child_envelope_sub_119 ?_
  intro b hb; exact common_sub_119 (mem_commonEnvelope childrenD_119 b hb)
end SnakyConditional

end OAI
