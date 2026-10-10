import OAI.GameTheory.SnakyConditional.Templates.Level11Part01
import OAI.GameTheory.SnakyConditional.Templates.Level11Part02
import OAI.GameTheory.SnakyConditional.Templates.Level11Part03

namespace OAI

namespace SnakyConditional
def required_318 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_318 : Finset Cell := ⟨(([(-2, 0), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_318 : Fin 4 → Finset Cell := ![(placedSet 3 (1, -3) required_64), (placedSet 0 (-1, 1) required_63), (placedSet 0 (-1, 0) required_261), (placedSet 1 (0, 1) required_55)]
def childrenD_318 : Fin 4 → Finset Cell := ![(placedSet 3 (1, -3) envelope_64), (placedSet 0 (-1, 1) envelope_63), (placedSet 0 (-1, 0) envelope_261), (placedSet 1 (0, 1) envelope_55)]
theorem common_sub_318 : commonEnvelope childrenD_318 ⊆ insert (0, 0) required_318 := by decide
theorem child_required_sub_318 : ∀ j, childrenC_318 j ⊆ insert (0, 0) required_318 := by decide
theorem child_envelope_sub_318 : ∀ j, childrenD_318 j ⊆ envelope_318 := by decide
theorem pivot_mem_318 : (0, 0) ∈ envelope_318 := by decide
theorem children_work_318 : ∀ j, Template HasSnaky 9 (childrenC_318 j) (childrenD_318 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_64 3 (1, -3)).mono (by decide)
  · exact (placed_template_map row_works_63 0 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_261 0 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_55 1 (0, 1)).mono (by decide)
theorem row_works_318 : Template HasSnaky 10 required_318 envelope_318 := by
  refine compose HasSnaky 9 childrenC_318 childrenD_318 children_work_318 (0, 0)
    required_318 envelope_318 pivot_mem_318 child_required_sub_318 child_envelope_sub_318 ?_
  intro b hb; exact common_sub_318 (mem_commonEnvelope childrenD_318 b hb)
def required_319 : Finset Cell := ⟨(([(-3, 1), (-2, 1), (-1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_319 : Finset Cell := ⟨(([(-6, 2), (-5, 1), (-5, 2), (-4, 1), (-4, 2), (-3, 1), (-2, 1), (-2, 2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_319 : Fin 4 → Finset Cell := ![(placedSet 2 (-1, 0) required_39), (placedSet 4 (-4, 1) required_109), (placedSet 1 (0, 1) required_266), (placedSet 4 (0, 1) required_122)]
def childrenD_319 : Fin 4 → Finset Cell := ![(placedSet 2 (-1, 0) envelope_39), (placedSet 4 (-4, 1) envelope_109), (placedSet 1 (0, 1) envelope_266), (placedSet 4 (0, 1) envelope_122)]
theorem common_sub_319 : commonEnvelope childrenD_319 ⊆ insert (0, 0) required_319 := by decide
theorem child_required_sub_319 : ∀ j, childrenC_319 j ⊆ insert (0, 0) required_319 := by decide
theorem child_envelope_sub_319 : ∀ j, childrenD_319 j ⊆ envelope_319 := by decide
theorem pivot_mem_319 : (0, 0) ∈ envelope_319 := by decide
theorem children_work_319 : ∀ j, Template HasSnaky 9 (childrenC_319 j) (childrenD_319 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_39 2 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_109 4 (-4, 1)).mono (by decide)
  · exact (placed_template_map row_works_266 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_122 4 (0, 1)).mono (by decide)
theorem row_works_319 : Template HasSnaky 10 required_319 envelope_319 := by
  refine compose HasSnaky 9 childrenC_319 childrenD_319 children_work_319 (0, 0)
    required_319 envelope_319 pivot_mem_319 child_required_sub_319 child_envelope_sub_319 ?_
  intro b hb; exact common_sub_319 (mem_commonEnvelope childrenD_319 b hb)
def required_326 : Finset Cell := ⟨(([(-4, -3), (-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_326 : Finset Cell := ⟨(([(-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 1), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_326 : Fin 2 → Finset Cell := ![(placedSet 1 (1, -1) required_63), (placedSet 7 (-4, 0) required_255)]
def childrenD_326 : Fin 2 → Finset Cell := ![(placedSet 1 (1, -1) envelope_63), (placedSet 7 (-4, 0) envelope_255)]
theorem common_sub_326 : commonEnvelope childrenD_326 ⊆ insert (0, 0) required_326 := by decide
theorem child_required_sub_326 : ∀ j, childrenC_326 j ⊆ insert (0, 0) required_326 := by decide
theorem child_envelope_sub_326 : ∀ j, childrenD_326 j ⊆ envelope_326 := by decide
theorem pivot_mem_326 : (0, 0) ∈ envelope_326 := by decide
theorem children_work_326 : ∀ j, Template HasSnaky 9 (childrenC_326 j) (childrenD_326 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_63 1 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_255 7 (-4, 0)).mono (by decide)
theorem row_works_326 : Template HasSnaky 10 required_326 envelope_326 := by
  refine compose HasSnaky 9 childrenC_326 childrenD_326 children_work_326 (0, 0)
    required_326 envelope_326 pivot_mem_326 child_required_sub_326 child_envelope_sub_326 ?_
  intro b hb; exact common_sub_326 (mem_commonEnvelope childrenD_326 b hb)
def required_328 : Finset Cell := ⟨(([(-1, -3), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_328 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_328 : Fin 3 → Finset Cell := ![(placedSet 0 (0, 1) required_49), (placedSet 3 (0, 1) required_44), (placedSet 0 (-1, 0) required_285)]
def childrenD_328 : Fin 3 → Finset Cell := ![(placedSet 0 (0, 1) envelope_49), (placedSet 3 (0, 1) envelope_44), (placedSet 0 (-1, 0) envelope_285)]
theorem common_sub_328 : commonEnvelope childrenD_328 ⊆ insert (0, 0) required_328 := by decide
theorem child_required_sub_328 : ∀ j, childrenC_328 j ⊆ insert (0, 0) required_328 := by decide
theorem child_envelope_sub_328 : ∀ j, childrenD_328 j ⊆ envelope_328 := by decide
theorem pivot_mem_328 : (0, 0) ∈ envelope_328 := by decide
theorem children_work_328 : ∀ j, Template HasSnaky 9 (childrenC_328 j) (childrenD_328 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_49 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_44 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_285 0 (-1, 0)).mono (by decide)
theorem row_works_328 : Template HasSnaky 10 required_328 envelope_328 := by
  refine compose HasSnaky 9 childrenC_328 childrenD_328 children_work_328 (0, 0)
    required_328 envelope_328 pivot_mem_328 child_required_sub_328 child_envelope_sub_328 ?_
  intro b hb; exact common_sub_328 (mem_commonEnvelope childrenD_328 b hb)
def required_330 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_330 : Finset Cell := ⟨(([(-5, 0), (-4, 0), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_330 : Fin 5 → Finset Cell := ![(placedSet 1 (1, -1) required_63), (placedSet 0 (0, 1) required_268), (placedSet 0 (1, 0) required_144), (placedSet 4 (1, 0) required_154), (placedSet 5 (1, 0) required_155)]
def childrenD_330 : Fin 5 → Finset Cell := ![(placedSet 1 (1, -1) envelope_63), (placedSet 0 (0, 1) envelope_268), (placedSet 0 (1, 0) envelope_144), (placedSet 4 (1, 0) envelope_154), (placedSet 5 (1, 0) envelope_155)]
theorem common_sub_330 : commonEnvelope childrenD_330 ⊆ insert (0, 0) required_330 := by decide
theorem child_required_sub_330 : ∀ j, childrenC_330 j ⊆ insert (0, 0) required_330 := by decide
theorem child_envelope_sub_330 : ∀ j, childrenD_330 j ⊆ envelope_330 := by decide
theorem pivot_mem_330 : (0, 0) ∈ envelope_330 := by decide
theorem children_work_330 : ∀ j, Template HasSnaky 9 (childrenC_330 j) (childrenD_330 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_63 1 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_268 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_144 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_154 4 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_155 5 (1, 0)).mono (by decide)
theorem row_works_330 : Template HasSnaky 10 required_330 envelope_330 := by
  refine compose HasSnaky 9 childrenC_330 childrenD_330 children_work_330 (0, 0)
    required_330 envelope_330 pivot_mem_330 child_required_sub_330 child_envelope_sub_330 ?_
  intro b hb; exact common_sub_330 (mem_commonEnvelope childrenD_330 b hb)
end SnakyConditional

end OAI
