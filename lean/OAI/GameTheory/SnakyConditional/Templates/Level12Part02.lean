import OAI.GameTheory.SnakyConditional.Templates.Level11Part01
import OAI.GameTheory.SnakyConditional.Templates.Level11Part02
import OAI.GameTheory.SnakyConditional.Templates.Level11Part03

namespace OAI

namespace SnakyConditional
def required_299 : Finset Cell := ⟨(([(0, -2), (0, -1), (1, -1), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_299 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (3, -1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_299 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) required_6), (placedSet 0 (0, 1) required_284)]
def childrenD_299 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) envelope_6), (placedSet 0 (0, 1) envelope_284)]
theorem common_sub_299 : commonEnvelope childrenD_299 ⊆ insert (0, 0) required_299 := by decide
theorem child_required_sub_299 : ∀ j, childrenC_299 j ⊆ insert (0, 0) required_299 := by decide
theorem child_envelope_sub_299 : ∀ j, childrenD_299 j ⊆ envelope_299 := by decide
theorem pivot_mem_299 : (0, 0) ∈ envelope_299 := by decide
theorem children_work_299 : ∀ j, Template HasSnaky 9 (childrenC_299 j) (childrenD_299 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_284 0 (0, 1)).mono (by decide)
theorem row_works_299 : Template HasSnaky 10 required_299 envelope_299 := by
  refine compose HasSnaky 9 childrenC_299 childrenD_299 children_work_299 (0, 0)
    required_299 envelope_299 pivot_mem_299 child_required_sub_299 child_envelope_sub_299 ?_
  intro b hb; exact common_sub_299 (mem_commonEnvelope childrenD_299 b hb)
def required_301 : Finset Cell := ⟨(([(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_301 : Finset Cell := ⟨(([(-4, 1), (-4, 3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_301 : Fin 3 → Finset Cell := ![(placedSet 0 (1, 0) required_59), (placedSet 0 (1, 0) required_57), (placedSet 4 (0, 1) required_258)]
def childrenD_301 : Fin 3 → Finset Cell := ![(placedSet 0 (1, 0) envelope_59), (placedSet 0 (1, 0) envelope_57), (placedSet 4 (0, 1) envelope_258)]
theorem common_sub_301 : commonEnvelope childrenD_301 ⊆ insert (0, 0) required_301 := by decide
theorem child_required_sub_301 : ∀ j, childrenC_301 j ⊆ insert (0, 0) required_301 := by decide
theorem child_envelope_sub_301 : ∀ j, childrenD_301 j ⊆ envelope_301 := by decide
theorem pivot_mem_301 : (0, 0) ∈ envelope_301 := by decide
theorem children_work_301 : ∀ j, Template HasSnaky 9 (childrenC_301 j) (childrenD_301 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_59 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_57 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_258 4 (0, 1)).mono (by decide)
theorem row_works_301 : Template HasSnaky 10 required_301 envelope_301 := by
  refine compose HasSnaky 9 childrenC_301 childrenD_301 children_work_301 (0, 0)
    required_301 envelope_301 pivot_mem_301 child_required_sub_301 child_envelope_sub_301 ?_
  intro b hb; exact common_sub_301 (mem_commonEnvelope childrenD_301 b hb)
def required_303 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (1, -3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_303 : Finset Cell := ⟨(([(-2, 0), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_303 : Fin 4 → Finset Cell := ![(placedSet 4 (0, 1) required_49), (placedSet 1 (0, 1) required_44), (placedSet 0 (-1, 1) required_63), (placedSet 0 (-1, 0) required_261)]
def childrenD_303 : Fin 4 → Finset Cell := ![(placedSet 4 (0, 1) envelope_49), (placedSet 1 (0, 1) envelope_44), (placedSet 0 (-1, 1) envelope_63), (placedSet 0 (-1, 0) envelope_261)]
theorem common_sub_303 : commonEnvelope childrenD_303 ⊆ insert (0, 0) required_303 := by decide
theorem child_required_sub_303 : ∀ j, childrenC_303 j ⊆ insert (0, 0) required_303 := by decide
theorem child_envelope_sub_303 : ∀ j, childrenD_303 j ⊆ envelope_303 := by decide
theorem pivot_mem_303 : (0, 0) ∈ envelope_303 := by decide
theorem children_work_303 : ∀ j, Template HasSnaky 9 (childrenC_303 j) (childrenD_303 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_49 4 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_44 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_63 0 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_261 0 (-1, 0)).mono (by decide)
theorem row_works_303 : Template HasSnaky 10 required_303 envelope_303 := by
  refine compose HasSnaky 9 childrenC_303 childrenD_303 children_work_303 (0, 0)
    required_303 envelope_303 pivot_mem_303 child_required_sub_303 child_envelope_sub_303 ?_
  intro b hb; exact common_sub_303 (mem_commonEnvelope childrenD_303 b hb)
def required_309 : Finset Cell := ⟨(([(-2, 0), (0, 1), (0, 2), (0, 3), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_309 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, -1), (-1, 0), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_309 : Fin 2 → Finset Cell := ![(placedSet 6 (-1, 0) required_28), (placedSet 1 (1, 3) required_268)]
def childrenD_309 : Fin 2 → Finset Cell := ![(placedSet 6 (-1, 0) envelope_28), (placedSet 1 (1, 3) envelope_268)]
theorem common_sub_309 : commonEnvelope childrenD_309 ⊆ insert (0, 0) required_309 := by decide
theorem child_required_sub_309 : ∀ j, childrenC_309 j ⊆ insert (0, 0) required_309 := by decide
theorem child_envelope_sub_309 : ∀ j, childrenD_309 j ⊆ envelope_309 := by decide
theorem pivot_mem_309 : (0, 0) ∈ envelope_309 := by decide
theorem children_work_309 : ∀ j, Template HasSnaky 9 (childrenC_309 j) (childrenD_309 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_28 6 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_268 1 (1, 3)).mono (by decide)
theorem row_works_309 : Template HasSnaky 10 required_309 envelope_309 := by
  refine compose HasSnaky 9 childrenC_309 childrenD_309 children_work_309 (0, 0)
    required_309 envelope_309 pivot_mem_309 child_required_sub_309 child_envelope_sub_309 ?_
  intro b hb; exact common_sub_309 (mem_commonEnvelope childrenD_309 b hb)
def required_312 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-1, -3), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_312 : Finset Cell := ⟨(([(-3, -1), (-3, 2), (-2, -1), (-2, 0), (-2, 2), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_312 : Fin 2 → Finset Cell := ![(placedSet 2 (1, 0) required_9), (placedSet 0 (0, 1) required_272)]
def childrenD_312 : Fin 2 → Finset Cell := ![(placedSet 2 (1, 0) envelope_9), (placedSet 0 (0, 1) envelope_272)]
theorem common_sub_312 : commonEnvelope childrenD_312 ⊆ insert (0, 0) required_312 := by decide
theorem child_required_sub_312 : ∀ j, childrenC_312 j ⊆ insert (0, 0) required_312 := by decide
theorem child_envelope_sub_312 : ∀ j, childrenD_312 j ⊆ envelope_312 := by decide
theorem pivot_mem_312 : (0, 0) ∈ envelope_312 := by decide
theorem children_work_312 : ∀ j, Template HasSnaky 9 (childrenC_312 j) (childrenD_312 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_9 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_272 0 (0, 1)).mono (by decide)
theorem row_works_312 : Template HasSnaky 10 required_312 envelope_312 := by
  refine compose HasSnaky 9 childrenC_312 childrenD_312 children_work_312 (0, 0)
    required_312 envelope_312 pivot_mem_312 child_required_sub_312 child_envelope_sub_312 ?_
  intro b hb; exact common_sub_312 (mem_commonEnvelope childrenD_312 b hb)
end SnakyConditional

end OAI
