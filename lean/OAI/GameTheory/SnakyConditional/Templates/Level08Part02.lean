import OAI.GameTheory.SnakyConditional.Templates.Level07Part01
import OAI.GameTheory.SnakyConditional.Templates.Level07Part02
import OAI.GameTheory.SnakyConditional.Templates.Level07Part03
import OAI.GameTheory.SnakyConditional.Templates.Level07Part04

namespace OAI

namespace SnakyConditional
def required_144 : Finset Cell := ⟨(([(-4, 0), (-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_144 : Finset Cell := ⟨(([(-6, 0), (-5, 0), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_144 : Fin 3 → Finset Cell := ![(placedSet 0 (0, 1) required_7), (placedSet 4 (-3, 1) required_104), (placedSet 0 (1, 0) required_55)]
def childrenD_144 : Fin 3 → Finset Cell := ![(placedSet 0 (0, 1) envelope_7), (placedSet 4 (-3, 1) envelope_104), (placedSet 0 (1, 0) envelope_55)]
theorem common_sub_144 : commonEnvelope childrenD_144 ⊆ insert (0, 0) required_144 := by decide
theorem child_required_sub_144 : ∀ j, childrenC_144 j ⊆ insert (0, 0) required_144 := by decide
theorem child_envelope_sub_144 : ∀ j, childrenD_144 j ⊆ envelope_144 := by decide
theorem pivot_mem_144 : (0, 0) ∈ envelope_144 := by decide
theorem children_work_144 : ∀ j, Template HasSnaky 5 (childrenC_144 j) (childrenD_144 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_7 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_104 4 (-3, 1)).mono (by decide)
  · exact (placed_template_map row_works_55 0 (1, 0)).mono (by decide)
theorem row_works_144 : Template HasSnaky 6 required_144 envelope_144 := by
  refine compose HasSnaky 5 childrenC_144 childrenD_144 children_work_144 (0, 0)
    required_144 envelope_144 pivot_mem_144 child_required_sub_144 child_envelope_sub_144 ?_
  intro b hb; exact common_sub_144 (mem_commonEnvelope childrenD_144 b hb)
def required_145 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (1, -3), (1, -2), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_145 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_145 : Fin 2 → Finset Cell := ![(placedSet 5 (0, 1) required_0), (placedSet 0 (-1, 0) required_91)]
def childrenD_145 : Fin 2 → Finset Cell := ![(placedSet 5 (0, 1) envelope_0), (placedSet 0 (-1, 0) envelope_91)]
theorem common_sub_145 : commonEnvelope childrenD_145 ⊆ insert (0, 0) required_145 := by decide
theorem child_required_sub_145 : ∀ j, childrenC_145 j ⊆ insert (0, 0) required_145 := by decide
theorem child_envelope_sub_145 : ∀ j, childrenD_145 j ⊆ envelope_145 := by decide
theorem pivot_mem_145 : (0, 0) ∈ envelope_145 := by decide
theorem children_work_145 : ∀ j, Template HasSnaky 5 (childrenC_145 j) (childrenD_145 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 5 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_91 0 (-1, 0)).mono (by decide)
theorem row_works_145 : Template HasSnaky 6 required_145 envelope_145 := by
  refine compose HasSnaky 5 childrenC_145 childrenD_145 children_work_145 (0, 0)
    required_145 envelope_145 pivot_mem_145 child_required_sub_145 child_envelope_sub_145 ?_
  intro b hb; exact common_sub_145 (mem_commonEnvelope childrenD_145 b hb)
def required_148 : Finset Cell := ⟨(([(-1, -2), (0, -4), (0, -3), (0, -2), (0, -1), (1, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_148 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_148 : Fin 4 → Finset Cell := ![(placedSet 1 (1, 0) required_7), (placedSet 1 (0, 1) required_46), (placedSet 0 (1, -1) required_94), (placedSet 1 (0, 1) required_97)]
def childrenD_148 : Fin 4 → Finset Cell := ![(placedSet 1 (1, 0) envelope_7), (placedSet 1 (0, 1) envelope_46), (placedSet 0 (1, -1) envelope_94), (placedSet 1 (0, 1) envelope_97)]
theorem common_sub_148 : commonEnvelope childrenD_148 ⊆ insert (0, 0) required_148 := by decide
theorem child_required_sub_148 : ∀ j, childrenC_148 j ⊆ insert (0, 0) required_148 := by decide
theorem child_envelope_sub_148 : ∀ j, childrenD_148 j ⊆ envelope_148 := by decide
theorem pivot_mem_148 : (0, 0) ∈ envelope_148 := by decide
theorem children_work_148 : ∀ j, Template HasSnaky 5 (childrenC_148 j) (childrenD_148 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_7 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_46 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_94 0 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_97 1 (0, 1)).mono (by decide)
theorem row_works_148 : Template HasSnaky 6 required_148 envelope_148 := by
  refine compose HasSnaky 5 childrenC_148 childrenD_148 children_work_148 (0, 0)
    required_148 envelope_148 pivot_mem_148 child_required_sub_148 child_envelope_sub_148 ?_
  intro b hb; exact common_sub_148 (mem_commonEnvelope childrenD_148 b hb)
def required_150 : Finset Cell := ⟨(([(-5, 0), (-4, -1), (-4, 0), (-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_150 : Finset Cell := ⟨(([(-5, 0), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_150 : Fin 2 → Finset Cell := ![(placedSet 6 (-3, -1) required_4), (placedSet 5 (-2, 1) required_126)]
def childrenD_150 : Fin 2 → Finset Cell := ![(placedSet 6 (-3, -1) envelope_4), (placedSet 5 (-2, 1) envelope_126)]
theorem common_sub_150 : commonEnvelope childrenD_150 ⊆ insert (0, 0) required_150 := by decide
theorem child_required_sub_150 : ∀ j, childrenC_150 j ⊆ insert (0, 0) required_150 := by decide
theorem child_envelope_sub_150 : ∀ j, childrenD_150 j ⊆ envelope_150 := by decide
theorem pivot_mem_150 : (0, 0) ∈ envelope_150 := by decide
theorem children_work_150 : ∀ j, Template HasSnaky 5 (childrenC_150 j) (childrenD_150 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_4 6 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_126 5 (-2, 1)).mono (by decide)
theorem row_works_150 : Template HasSnaky 6 required_150 envelope_150 := by
  refine compose HasSnaky 5 childrenC_150 childrenD_150 children_work_150 (0, 0)
    required_150 envelope_150 pivot_mem_150 child_required_sub_150 child_envelope_sub_150 ?_
  intro b hb; exact common_sub_150 (mem_commonEnvelope childrenD_150 b hb)
def required_152 : Finset Cell := ⟨(([(1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_152 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_152 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_6), (placedSet 1 (3, 0) required_73)]
def childrenD_152 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_6), (placedSet 1 (3, 0) envelope_73)]
theorem common_sub_152 : commonEnvelope childrenD_152 ⊆ insert (0, 0) required_152 := by decide
theorem child_required_sub_152 : ∀ j, childrenC_152 j ⊆ insert (0, 0) required_152 := by decide
theorem child_envelope_sub_152 : ∀ j, childrenD_152 j ⊆ envelope_152 := by decide
theorem pivot_mem_152 : (0, 0) ∈ envelope_152 := by decide
theorem children_work_152 : ∀ j, Template HasSnaky 5 (childrenC_152 j) (childrenD_152 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_73 1 (3, 0)).mono (by decide)
theorem row_works_152 : Template HasSnaky 6 required_152 envelope_152 := by
  refine compose HasSnaky 5 childrenC_152 childrenD_152 children_work_152 (0, 0)
    required_152 envelope_152 pivot_mem_152 child_required_sub_152 child_envelope_sub_152 ?_
  intro b hb; exact common_sub_152 (mem_commonEnvelope childrenD_152 b hb)
def required_154 : Finset Cell := ⟨(([(1, 0), (2, 0), (3, 0), (4, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_154 : Finset Cell := ⟨(([(-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (5, 0), (6, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_154 : Fin 2 → Finset Cell := ![(placedSet 6 (0, -1) required_7), (placedSet 0 (3, 1) required_104)]
def childrenD_154 : Fin 2 → Finset Cell := ![(placedSet 6 (0, -1) envelope_7), (placedSet 0 (3, 1) envelope_104)]
theorem common_sub_154 : commonEnvelope childrenD_154 ⊆ insert (0, 0) required_154 := by decide
theorem child_required_sub_154 : ∀ j, childrenC_154 j ⊆ insert (0, 0) required_154 := by decide
theorem child_envelope_sub_154 : ∀ j, childrenD_154 j ⊆ envelope_154 := by decide
theorem pivot_mem_154 : (0, 0) ∈ envelope_154 := by decide
theorem children_work_154 : ∀ j, Template HasSnaky 5 (childrenC_154 j) (childrenD_154 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_7 6 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_104 0 (3, 1)).mono (by decide)
theorem row_works_154 : Template HasSnaky 6 required_154 envelope_154 := by
  refine compose HasSnaky 5 childrenC_154 childrenD_154 children_work_154 (0, 0)
    required_154 envelope_154 pivot_mem_154 child_required_sub_154 child_envelope_sub_154 ?_
  intro b hb; exact common_sub_154 (mem_commonEnvelope childrenD_154 b hb)
def required_156 : Finset Cell := ⟨(([(-3, -1), (-3, 0), (-3, 1), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_156 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_156 : Fin 3 → Finset Cell := ![(placedSet 0 (-2, 0) required_11), (placedSet 2 (-2, 0) required_98), (placedSet 0 (-2, -1) required_33)]
def childrenD_156 : Fin 3 → Finset Cell := ![(placedSet 0 (-2, 0) envelope_11), (placedSet 2 (-2, 0) envelope_98), (placedSet 0 (-2, -1) envelope_33)]
theorem common_sub_156 : commonEnvelope childrenD_156 ⊆ insert (0, 0) required_156 := by decide
theorem child_required_sub_156 : ∀ j, childrenC_156 j ⊆ insert (0, 0) required_156 := by decide
theorem child_envelope_sub_156 : ∀ j, childrenD_156 j ⊆ envelope_156 := by decide
theorem pivot_mem_156 : (0, 0) ∈ envelope_156 := by decide
theorem children_work_156 : ∀ j, Template HasSnaky 5 (childrenC_156 j) (childrenD_156 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_11 0 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_98 2 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_33 0 (-2, -1)).mono (by decide)
theorem row_works_156 : Template HasSnaky 6 required_156 envelope_156 := by
  refine compose HasSnaky 5 childrenC_156 childrenD_156 children_work_156 (0, 0)
    required_156 envelope_156 pivot_mem_156 child_required_sub_156 child_envelope_sub_156 ?_
  intro b hb; exact common_sub_156 (mem_commonEnvelope childrenD_156 b hb)
end SnakyConditional

end OAI
