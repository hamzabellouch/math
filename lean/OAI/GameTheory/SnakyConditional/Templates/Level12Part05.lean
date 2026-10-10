import OAI.GameTheory.SnakyConditional.Templates.Level11Part01
import OAI.GameTheory.SnakyConditional.Templates.Level11Part02
import OAI.GameTheory.SnakyConditional.Templates.Level11Part04
import OAI.GameTheory.SnakyConditional.Templates.Level11Part06

namespace OAI

namespace SnakyConditional
def required_344 : Finset Cell := ⟨(([(0, -4), (0, -3), (0, -2), (0, -1), (1, -3), (2, -3), (3, -3), (3, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_344 : Finset Cell := ⟨(([(-1, -1), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_344 : Fin 3 → Finset Cell := ![(placedSet 1 (1, 0) required_7), (placedSet 3 (0, 1) required_108), (placedSet 4 (1, -2) required_262)]
def childrenD_344 : Fin 3 → Finset Cell := ![(placedSet 1 (1, 0) envelope_7), (placedSet 3 (0, 1) envelope_108), (placedSet 4 (1, -2) envelope_262)]
theorem common_sub_344 : commonEnvelope childrenD_344 ⊆ insert (0, 0) required_344 := by decide
theorem child_required_sub_344 : ∀ j, childrenC_344 j ⊆ insert (0, 0) required_344 := by decide
theorem child_envelope_sub_344 : ∀ j, childrenD_344 j ⊆ envelope_344 := by decide
theorem pivot_mem_344 : (0, 0) ∈ envelope_344 := by decide
theorem children_work_344 : ∀ j, Template HasSnaky 9 (childrenC_344 j) (childrenD_344 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_7 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_108 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_262 4 (1, -2)).mono (by decide)
theorem row_works_344 : Template HasSnaky 10 required_344 envelope_344 := by
  refine compose HasSnaky 9 childrenC_344 childrenD_344 children_work_344 (0, 0)
    required_344 envelope_344 pivot_mem_344 child_required_sub_344 child_envelope_sub_344 ?_
  intro b hb; exact common_sub_344 (mem_commonEnvelope childrenD_344 b hb)
def required_345 : Finset Cell := ⟨(([(-3, 0), (-3, 3), (-2, 0), (-1, 0), (-1, 3), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_345 : Finset Cell := ⟨(([(-6, 4), (-5, 3), (-5, 4), (-4, 3), (-4, 4), (-3, 0), (-3, 3), (-3, 4), (-2, 0), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 3), (-1, 4), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_345 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 1) required_6), (placedSet 4 (0, 3) required_320)]
def childrenD_345 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 1) envelope_6), (placedSet 4 (0, 3) envelope_320)]
theorem common_sub_345 : commonEnvelope childrenD_345 ⊆ insert (0, 0) required_345 := by decide
theorem child_required_sub_345 : ∀ j, childrenC_345 j ⊆ insert (0, 0) required_345 := by decide
theorem child_envelope_sub_345 : ∀ j, childrenD_345 j ⊆ envelope_345 := by decide
theorem pivot_mem_345 : (0, 0) ∈ envelope_345 := by decide
theorem children_work_345 : ∀ j, Template HasSnaky 9 (childrenC_345 j) (childrenD_345 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 0 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_320 4 (0, 3)).mono (by decide)
theorem row_works_345 : Template HasSnaky 10 required_345 envelope_345 := by
  refine compose HasSnaky 9 childrenC_345 childrenD_345 children_work_345 (0, 0)
    required_345 envelope_345 pivot_mem_345 child_required_sub_345 child_envelope_sub_345 ?_
  intro b hb; exact common_sub_345 (mem_commonEnvelope childrenD_345 b hb)
def required_346 : Finset Cell := ⟨(([(-3, -4), (-3, -3), (-3, -2), (-3, -1), (-1, -3), (0, -3), (0, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_346 : Finset Cell := ⟨(([(-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (1, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_346 : Fin 3 → Finset Cell := ![(placedSet 1 (0, -1) required_60), (placedSet 0 (-3, 0) required_255), (placedSet 0 (-3, 0) required_276)]
def childrenD_346 : Fin 3 → Finset Cell := ![(placedSet 1 (0, -1) envelope_60), (placedSet 0 (-3, 0) envelope_255), (placedSet 0 (-3, 0) envelope_276)]
theorem common_sub_346 : commonEnvelope childrenD_346 ⊆ insert (0, 0) required_346 := by decide
theorem child_required_sub_346 : ∀ j, childrenC_346 j ⊆ insert (0, 0) required_346 := by decide
theorem child_envelope_sub_346 : ∀ j, childrenD_346 j ⊆ envelope_346 := by decide
theorem pivot_mem_346 : (0, 0) ∈ envelope_346 := by decide
theorem children_work_346 : ∀ j, Template HasSnaky 9 (childrenC_346 j) (childrenD_346 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_60 1 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_255 0 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_276 0 (-3, 0)).mono (by decide)
theorem row_works_346 : Template HasSnaky 10 required_346 envelope_346 := by
  refine compose HasSnaky 9 childrenC_346 childrenD_346 children_work_346 (0, 0)
    required_346 envelope_346 pivot_mem_346 child_required_sub_346 child_envelope_sub_346 ?_
  intro b hb; exact common_sub_346 (mem_commonEnvelope childrenD_346 b hb)
def required_355 : Finset Cell := ⟨(([(1, -1), (1, 0), (2, -1), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_355 : Finset Cell := ⟨(([(-2, 0), (-2, 1), (-2, 3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_355 : Fin 3 → Finset Cell := ![(placedSet 2 (3, -1) required_12), (placedSet 0 (3, 0) required_167), (placedSet 0 (2, 2) required_342)]
def childrenD_355 : Fin 3 → Finset Cell := ![(placedSet 2 (3, -1) envelope_12), (placedSet 0 (3, 0) envelope_167), (placedSet 0 (2, 2) envelope_342)]
theorem common_sub_355 : commonEnvelope childrenD_355 ⊆ insert (0, 0) required_355 := by decide
theorem child_required_sub_355 : ∀ j, childrenC_355 j ⊆ insert (0, 0) required_355 := by decide
theorem child_envelope_sub_355 : ∀ j, childrenD_355 j ⊆ envelope_355 := by decide
theorem pivot_mem_355 : (0, 0) ∈ envelope_355 := by decide
theorem children_work_355 : ∀ j, Template HasSnaky 9 (childrenC_355 j) (childrenD_355 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_12 2 (3, -1)).mono (by decide)
  · exact (placed_template_map row_works_167 0 (3, 0)).mono (by decide)
  · exact (placed_template_map row_works_342 0 (2, 2)).mono (by decide)
theorem row_works_355 : Template HasSnaky 10 required_355 envelope_355 := by
  refine compose HasSnaky 9 childrenC_355 childrenD_355 children_work_355 (0, 0)
    required_355 envelope_355 pivot_mem_355 child_required_sub_355 child_envelope_sub_355 ?_
  intro b hb; exact common_sub_355 (mem_commonEnvelope childrenD_355 b hb)
def required_357 : Finset Cell := ⟨(([(-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_357 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, 0), (0, 1), (0, 2), (0, 4), (0, 5), (0, 6), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_357 : Fin 2 → Finset Cell := ![(placedSet 6 (-2, -1) required_82), (placedSet 0 (1, 2) required_283)]
def childrenD_357 : Fin 2 → Finset Cell := ![(placedSet 6 (-2, -1) envelope_82), (placedSet 0 (1, 2) envelope_283)]
theorem common_sub_357 : commonEnvelope childrenD_357 ⊆ insert (0, 0) required_357 := by decide
theorem child_required_sub_357 : ∀ j, childrenC_357 j ⊆ insert (0, 0) required_357 := by decide
theorem child_envelope_sub_357 : ∀ j, childrenD_357 j ⊆ envelope_357 := by decide
theorem pivot_mem_357 : (0, 0) ∈ envelope_357 := by decide
theorem children_work_357 : ∀ j, Template HasSnaky 9 (childrenC_357 j) (childrenD_357 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_82 6 (-2, -1)).mono (by decide)
  · exact (placed_template_map row_works_283 0 (1, 2)).mono (by decide)
theorem row_works_357 : Template HasSnaky 10 required_357 envelope_357 := by
  refine compose HasSnaky 9 childrenC_357 childrenD_357 children_work_357 (0, 0)
    required_357 envelope_357 pivot_mem_357 child_required_sub_357 child_envelope_sub_357 ?_
  intro b hb; exact common_sub_357 (mem_commonEnvelope childrenD_357 b hb)
end SnakyConditional

end OAI
