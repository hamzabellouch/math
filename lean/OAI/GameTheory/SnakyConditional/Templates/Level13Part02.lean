import OAI.GameTheory.SnakyConditional.Templates.Level12Part02
import OAI.GameTheory.SnakyConditional.Templates.Level12Part05

namespace OAI

namespace SnakyConditional
def required_352 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (1, -2), (2, -2), (3, -2), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_352 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_352 : Fin 5 → Finset Cell := ![(placedSet 0 (0, 1) required_214), (placedSet 0 (-1, 0) required_91), (placedSet 0 (-1, 1) required_63), (placedSet 0 (0, 1) required_344), (placedSet 4 (0, 1) required_180)]
def childrenD_352 : Fin 5 → Finset Cell := ![(placedSet 0 (0, 1) envelope_214), (placedSet 0 (-1, 0) envelope_91), (placedSet 0 (-1, 1) envelope_63), (placedSet 0 (0, 1) envelope_344), (placedSet 4 (0, 1) envelope_180)]
theorem common_sub_352 : commonEnvelope childrenD_352 ⊆ insert (0, 0) required_352 := by decide
theorem child_required_sub_352 : ∀ j, childrenC_352 j ⊆ insert (0, 0) required_352 := by decide
theorem child_envelope_sub_352 : ∀ j, childrenD_352 j ⊆ envelope_352 := by decide
theorem pivot_mem_352 : (0, 0) ∈ envelope_352 := by decide
theorem children_work_352 : ∀ j, Template HasSnaky 10 (childrenC_352 j) (childrenD_352 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_214 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_91 0 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_63 0 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_344 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_180 4 (0, 1)).mono (by decide)
theorem row_works_352 : Template HasSnaky 11 required_352 envelope_352 := by
  refine compose HasSnaky 10 childrenC_352 childrenD_352 children_work_352 (0, 0)
    required_352 envelope_352 pivot_mem_352 child_required_sub_352 child_envelope_sub_352 ?_
  intro b hb; exact common_sub_352 (mem_commonEnvelope childrenD_352 b hb)
def required_354 : Finset Cell := ⟨(([(-1, -1), (-1, 0), (-1, 1), (0, -2), (0, 1), (1, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_354 : Finset Cell := ⟨(([(-3, 0), (-2, -1), (-2, 0), (-2, 3), (-1, -1), (-1, 0), (-1, 1), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 3), (0, 4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (4, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_354 : Fin 4 → Finset Cell := ![(placedSet 2 (1, 0) required_138), (placedSet 5 (0, -1) required_114), (placedSet 0 (1, 1) required_312), (placedSet 2 (-2, 0) required_182)]
def childrenD_354 : Fin 4 → Finset Cell := ![(placedSet 2 (1, 0) envelope_138), (placedSet 5 (0, -1) envelope_114), (placedSet 0 (1, 1) envelope_312), (placedSet 2 (-2, 0) envelope_182)]
theorem common_sub_354 : commonEnvelope childrenD_354 ⊆ insert (0, 0) required_354 := by decide
theorem child_required_sub_354 : ∀ j, childrenC_354 j ⊆ insert (0, 0) required_354 := by decide
theorem child_envelope_sub_354 : ∀ j, childrenD_354 j ⊆ envelope_354 := by decide
theorem pivot_mem_354 : (0, 0) ∈ envelope_354 := by decide
theorem children_work_354 : ∀ j, Template HasSnaky 10 (childrenC_354 j) (childrenD_354 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_138 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_114 5 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_312 0 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_182 2 (-2, 0)).mono (by decide)
theorem row_works_354 : Template HasSnaky 11 required_354 envelope_354 := by
  refine compose HasSnaky 10 childrenC_354 childrenD_354 children_work_354 (0, 0)
    required_354 envelope_354 pivot_mem_354 child_required_sub_354 child_envelope_sub_354 ?_
  intro b hb; exact common_sub_354 (mem_commonEnvelope childrenD_354 b hb)
def required_358 : Finset Cell := ⟨(([(-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-1, -1), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_358 : Finset Cell := ⟨(([(-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_358 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) required_6), (placedSet 0 (0, 2) required_346)]
def childrenD_358 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) envelope_6), (placedSet 0 (0, 2) envelope_346)]
theorem common_sub_358 : commonEnvelope childrenD_358 ⊆ insert (0, 0) required_358 := by decide
theorem child_required_sub_358 : ∀ j, childrenC_358 j ⊆ insert (0, 0) required_358 := by decide
theorem child_envelope_sub_358 : ∀ j, childrenD_358 j ⊆ envelope_358 := by decide
theorem pivot_mem_358 : (0, 0) ∈ envelope_358 := by decide
theorem children_work_358 : ∀ j, Template HasSnaky 10 (childrenC_358 j) (childrenD_358 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_346 0 (0, 2)).mono (by decide)
theorem row_works_358 : Template HasSnaky 11 required_358 envelope_358 := by
  refine compose HasSnaky 10 childrenC_358 childrenD_358 children_work_358 (0, 0)
    required_358 envelope_358 pivot_mem_358 child_required_sub_358 child_envelope_sub_358 ?_
  intro b hb; exact common_sub_358 (mem_commonEnvelope childrenD_358 b hb)
def required_362 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-3, 2), (-2, -1), (-1, -1), (-1, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_362 : Finset Cell := ⟨(([(-6, 3), (-5, 2), (-5, 3), (-4, -1), (-4, 2), (-4, 3), (-3, -1), (-3, 2), (-3, 3), (-2, -1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_362 : Fin 2 → Finset Cell := ![(placedSet 0 (-1, 0) required_4), (placedSet 0 (0, -1) required_345)]
def childrenD_362 : Fin 2 → Finset Cell := ![(placedSet 0 (-1, 0) envelope_4), (placedSet 0 (0, -1) envelope_345)]
theorem common_sub_362 : commonEnvelope childrenD_362 ⊆ insert (0, 0) required_362 := by decide
theorem child_required_sub_362 : ∀ j, childrenC_362 j ⊆ insert (0, 0) required_362 := by decide
theorem child_envelope_sub_362 : ∀ j, childrenD_362 j ⊆ envelope_362 := by decide
theorem pivot_mem_362 : (0, 0) ∈ envelope_362 := by decide
theorem children_work_362 : ∀ j, Template HasSnaky 10 (childrenC_362 j) (childrenD_362 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_4 0 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_345 0 (0, -1)).mono (by decide)
theorem row_works_362 : Template HasSnaky 11 required_362 envelope_362 := by
  refine compose HasSnaky 10 childrenC_362 childrenD_362 children_work_362 (0, 0)
    required_362 envelope_362 pivot_mem_362 child_required_sub_362 child_envelope_sub_362 ?_
  intro b hb; exact common_sub_362 (mem_commonEnvelope childrenD_362 b hb)
def required_366 : Finset Cell := ⟨(([(1, -3), (1, -2), (1, -1), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_366 : Finset Cell := ⟨(([(-2, -3), (-1, -3), (-1, -1), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_366 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_6), (placedSet 0 (2, -2) required_357)]
def childrenD_366 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_6), (placedSet 0 (2, -2) envelope_357)]
theorem common_sub_366 : commonEnvelope childrenD_366 ⊆ insert (0, 0) required_366 := by decide
theorem child_required_sub_366 : ∀ j, childrenC_366 j ⊆ insert (0, 0) required_366 := by decide
theorem child_envelope_sub_366 : ∀ j, childrenD_366 j ⊆ envelope_366 := by decide
theorem pivot_mem_366 : (0, 0) ∈ envelope_366 := by decide
theorem children_work_366 : ∀ j, Template HasSnaky 10 (childrenC_366 j) (childrenD_366 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_357 0 (2, -2)).mono (by decide)
theorem row_works_366 : Template HasSnaky 11 required_366 envelope_366 := by
  refine compose HasSnaky 10 childrenC_366 childrenD_366 children_work_366 (0, 0)
    required_366 envelope_366 pivot_mem_366 child_required_sub_366 child_envelope_sub_366 ?_
  intro b hb; exact common_sub_366 (mem_commonEnvelope childrenD_366 b hb)
end SnakyConditional

end OAI
