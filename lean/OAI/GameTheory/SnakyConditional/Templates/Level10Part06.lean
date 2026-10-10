import OAI.GameTheory.SnakyConditional.Templates.Level09Part01
import OAI.GameTheory.SnakyConditional.Templates.Level09Part02
import OAI.GameTheory.SnakyConditional.Templates.Level09Part03
import OAI.GameTheory.SnakyConditional.Templates.Level09Part04
import OAI.GameTheory.SnakyConditional.Templates.Level09Part05
import OAI.GameTheory.SnakyConditional.Templates.Level09Part06
import OAI.GameTheory.SnakyConditional.Templates.Level09Part07
import OAI.GameTheory.SnakyConditional.Templates.Level09Part08

namespace OAI

namespace SnakyConditional
def required_315 : Finset Cell := ⟨(([(-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-1, -1), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_315 : Finset Cell := ⟨(([(-4, 1), (-4, 2), (-4, 3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -1), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_315 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) required_6), (placedSet 0 (0, 1) required_296)]
def childrenD_315 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) envelope_6), (placedSet 0 (0, 1) envelope_296)]
theorem common_sub_315 : commonEnvelope childrenD_315 ⊆ insert (0, 0) required_315 := by decide
theorem child_required_sub_315 : ∀ j, childrenC_315 j ⊆ insert (0, 0) required_315 := by decide
theorem child_envelope_sub_315 : ∀ j, childrenD_315 j ⊆ envelope_315 := by decide
theorem pivot_mem_315 : (0, 0) ∈ envelope_315 := by decide
theorem children_work_315 : ∀ j, Template HasSnaky 7 (childrenC_315 j) (childrenD_315 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_296 0 (0, 1)).mono (by decide)
theorem row_works_315 : Template HasSnaky 8 required_315 envelope_315 := by
  refine compose HasSnaky 7 childrenC_315 childrenD_315 children_work_315 (0, 0)
    required_315 envelope_315 pivot_mem_315 child_required_sub_315 child_envelope_sub_315 ?_
  intro b hb; exact common_sub_315 (mem_commonEnvelope childrenD_315 b hb)
def required_321 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_321 : Finset Cell := ⟨(([(-3, 3), (-2, 3), (-1, -1), (-1, 0), (-1, 3), (-1, 4), (-1, 5), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (3, 1), (3, 2), (4, 1), (4, 2), (5, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_321 : Fin 3 → Finset Cell := ![(placedSet 1 (-1, 0) required_165), (placedSet 0 (3, 1) required_97), (placedSet 3 (0, 3) required_223)]
def childrenD_321 : Fin 3 → Finset Cell := ![(placedSet 1 (-1, 0) envelope_165), (placedSet 0 (3, 1) envelope_97), (placedSet 3 (0, 3) envelope_223)]
theorem common_sub_321 : commonEnvelope childrenD_321 ⊆ insert (0, 0) required_321 := by decide
theorem child_required_sub_321 : ∀ j, childrenC_321 j ⊆ insert (0, 0) required_321 := by decide
theorem child_envelope_sub_321 : ∀ j, childrenD_321 j ⊆ envelope_321 := by decide
theorem pivot_mem_321 : (0, 0) ∈ envelope_321 := by decide
theorem children_work_321 : ∀ j, Template HasSnaky 7 (childrenC_321 j) (childrenD_321 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_165 1 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_97 0 (3, 1)).mono (by decide)
  · exact (placed_template_map row_works_223 3 (0, 3)).mono (by decide)
theorem row_works_321 : Template HasSnaky 8 required_321 envelope_321 := by
  refine compose HasSnaky 7 childrenC_321 childrenD_321 children_work_321 (0, 0)
    required_321 envelope_321 pivot_mem_321 child_required_sub_321 child_envelope_sub_321 ?_
  intro b hb; exact common_sub_321 (mem_commonEnvelope childrenD_321 b hb)
def required_323 : Finset Cell := ⟨(([(-2, 0), (-1, -2), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_323 : Finset Cell := ⟨(([(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_323 : Fin 3 → Finset Cell := ![(placedSet 6 (0, 1) required_165), (placedSet 0 (-3, 0) required_278), (placedSet 1 (0, 1) required_25)]
def childrenD_323 : Fin 3 → Finset Cell := ![(placedSet 6 (0, 1) envelope_165), (placedSet 0 (-3, 0) envelope_278), (placedSet 1 (0, 1) envelope_25)]
theorem common_sub_323 : commonEnvelope childrenD_323 ⊆ insert (0, 0) required_323 := by decide
theorem child_required_sub_323 : ∀ j, childrenC_323 j ⊆ insert (0, 0) required_323 := by decide
theorem child_envelope_sub_323 : ∀ j, childrenD_323 j ⊆ envelope_323 := by decide
theorem pivot_mem_323 : (0, 0) ∈ envelope_323 := by decide
theorem children_work_323 : ∀ j, Template HasSnaky 7 (childrenC_323 j) (childrenD_323 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_165 6 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_278 0 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_25 1 (0, 1)).mono (by decide)
theorem row_works_323 : Template HasSnaky 8 required_323 envelope_323 := by
  refine compose HasSnaky 7 childrenC_323 childrenD_323 children_work_323 (0, 0)
    required_323 envelope_323 pivot_mem_323 child_required_sub_323 child_envelope_sub_323 ?_
  intro b hb; exact common_sub_323 (mem_commonEnvelope childrenD_323 b hb)
def required_325 : Finset Cell := ⟨(([(-1, 0), (1, -2), (1, -1), (1, 0), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_325 : Finset Cell := ⟨(([(-2, 0), (-1, 0), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_325 : Fin 3 → Finset Cell := ![(placedSet 0 (2, 1) required_25), (placedSet 1 (2, 0) required_313), (placedSet 2 (2, -1) required_24)]
def childrenD_325 : Fin 3 → Finset Cell := ![(placedSet 0 (2, 1) envelope_25), (placedSet 1 (2, 0) envelope_313), (placedSet 2 (2, -1) envelope_24)]
theorem common_sub_325 : commonEnvelope childrenD_325 ⊆ insert (0, 0) required_325 := by decide
theorem child_required_sub_325 : ∀ j, childrenC_325 j ⊆ insert (0, 0) required_325 := by decide
theorem child_envelope_sub_325 : ∀ j, childrenD_325 j ⊆ envelope_325 := by decide
theorem pivot_mem_325 : (0, 0) ∈ envelope_325 := by decide
theorem children_work_325 : ∀ j, Template HasSnaky 7 (childrenC_325 j) (childrenD_325 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_25 0 (2, 1)).mono (by decide)
  · exact (placed_template_map row_works_313 1 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_24 2 (2, -1)).mono (by decide)
theorem row_works_325 : Template HasSnaky 8 required_325 envelope_325 := by
  refine compose HasSnaky 7 childrenC_325 childrenD_325 children_work_325 (0, 0)
    required_325 envelope_325 pivot_mem_325 child_required_sub_325 child_envelope_sub_325 ?_
  intro b hb; exact common_sub_325 (mem_commonEnvelope childrenD_325 b hb)
def required_327 : Finset Cell := ⟨(([(-1, -1), (-1, 0), (1, -1), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_327 : Finset Cell := ⟨(([(-6, -1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_327 : Fin 4 → Finset Cell := ![(placedSet 2 (2, -1) required_24), (placedSet 4 (-2, 0) required_195), (placedSet 0 (2, 0) required_195), (placedSet 6 (-2, -1) required_24)]
def childrenD_327 : Fin 4 → Finset Cell := ![(placedSet 2 (2, -1) envelope_24), (placedSet 4 (-2, 0) envelope_195), (placedSet 0 (2, 0) envelope_195), (placedSet 6 (-2, -1) envelope_24)]
theorem common_sub_327 : commonEnvelope childrenD_327 ⊆ insert (0, 0) required_327 := by decide
theorem child_required_sub_327 : ∀ j, childrenC_327 j ⊆ insert (0, 0) required_327 := by decide
theorem child_envelope_sub_327 : ∀ j, childrenD_327 j ⊆ envelope_327 := by decide
theorem pivot_mem_327 : (0, 0) ∈ envelope_327 := by decide
theorem children_work_327 : ∀ j, Template HasSnaky 7 (childrenC_327 j) (childrenD_327 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_24 2 (2, -1)).mono (by decide)
  · exact (placed_template_map row_works_195 4 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_195 0 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_24 6 (-2, -1)).mono (by decide)
theorem row_works_327 : Template HasSnaky 8 required_327 envelope_327 := by
  refine compose HasSnaky 7 childrenC_327 childrenD_327 children_work_327 (0, 0)
    required_327 envelope_327 pivot_mem_327 child_required_sub_327 child_envelope_sub_327 ?_
  intro b hb; exact common_sub_327 (mem_commonEnvelope childrenD_327 b hb)
def required_338 : Finset Cell := ⟨(([(-1, 0), (1, -2), (1, -1), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_338 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_338 : Fin 3 → Finset Cell := ![(placedSet 0 (2, 0) required_241), (placedSet 4 (-2, 0) required_275), (placedSet 4 (-2, 0) required_107)]
def childrenD_338 : Fin 3 → Finset Cell := ![(placedSet 0 (2, 0) envelope_241), (placedSet 4 (-2, 0) envelope_275), (placedSet 4 (-2, 0) envelope_107)]
theorem common_sub_338 : commonEnvelope childrenD_338 ⊆ insert (0, 0) required_338 := by decide
theorem child_required_sub_338 : ∀ j, childrenC_338 j ⊆ insert (0, 0) required_338 := by decide
theorem child_envelope_sub_338 : ∀ j, childrenD_338 j ⊆ envelope_338 := by decide
theorem pivot_mem_338 : (0, 0) ∈ envelope_338 := by decide
theorem children_work_338 : ∀ j, Template HasSnaky 7 (childrenC_338 j) (childrenD_338 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_241 0 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_275 4 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_107 4 (-2, 0)).mono (by decide)
theorem row_works_338 : Template HasSnaky 8 required_338 envelope_338 := by
  refine compose HasSnaky 7 childrenC_338 childrenD_338 children_work_338 (0, 0)
    required_338 envelope_338 pivot_mem_338 child_required_sub_338 child_envelope_sub_338 ?_
  intro b hb; exact common_sub_338 (mem_commonEnvelope childrenD_338 b hb)
def required_350 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (1, 0), (1, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_350 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_350 : Fin 4 → Finset Cell := ![(placedSet 4 (-2, 1) required_24), (placedSet 2 (2, 0) required_107), (placedSet 4 (1, 1) required_271), (placedSet 0 (1, 1) required_215)]
def childrenD_350 : Fin 4 → Finset Cell := ![(placedSet 4 (-2, 1) envelope_24), (placedSet 2 (2, 0) envelope_107), (placedSet 4 (1, 1) envelope_271), (placedSet 0 (1, 1) envelope_215)]
theorem common_sub_350 : commonEnvelope childrenD_350 ⊆ insert (0, 0) required_350 := by decide
theorem child_required_sub_350 : ∀ j, childrenC_350 j ⊆ insert (0, 0) required_350 := by decide
theorem child_envelope_sub_350 : ∀ j, childrenD_350 j ⊆ envelope_350 := by decide
theorem pivot_mem_350 : (0, 0) ∈ envelope_350 := by decide
theorem children_work_350 : ∀ j, Template HasSnaky 7 (childrenC_350 j) (childrenD_350 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_24 4 (-2, 1)).mono (by decide)
  · exact (placed_template_map row_works_107 2 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_271 4 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_215 0 (1, 1)).mono (by decide)
theorem row_works_350 : Template HasSnaky 8 required_350 envelope_350 := by
  refine compose HasSnaky 7 childrenC_350 childrenD_350 children_work_350 (0, 0)
    required_350 envelope_350 pivot_mem_350 child_required_sub_350 child_envelope_sub_350 ?_
  intro b hb; exact common_sub_350 (mem_commonEnvelope childrenD_350 b hb)
end SnakyConditional

end OAI
