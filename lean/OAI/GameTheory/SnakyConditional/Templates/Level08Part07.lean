import OAI.GameTheory.SnakyConditional.Templates.Level07Part01
import OAI.GameTheory.SnakyConditional.Templates.Level07Part04
import OAI.GameTheory.SnakyConditional.Templates.Level07Part05
import OAI.GameTheory.SnakyConditional.Templates.Level07Part06
import OAI.GameTheory.SnakyConditional.Templates.Level07Part07

namespace OAI

namespace SnakyConditional
def required_216 : Finset Cell := ⟨(([(-4, 0), (-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_216 : Finset Cell := ⟨(([(-5, -1), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_216 : Fin 2 → Finset Cell := ![(placedSet 6 (-4, -1) required_7), (placedSet 5 (1, 0) required_155)]
def childrenD_216 : Fin 2 → Finset Cell := ![(placedSet 6 (-4, -1) envelope_7), (placedSet 5 (1, 0) envelope_155)]
theorem common_sub_216 : commonEnvelope childrenD_216 ⊆ insert (0, 0) required_216 := by decide
theorem child_required_sub_216 : ∀ j, childrenC_216 j ⊆ insert (0, 0) required_216 := by decide
theorem child_envelope_sub_216 : ∀ j, childrenD_216 j ⊆ envelope_216 := by decide
theorem pivot_mem_216 : (0, 0) ∈ envelope_216 := by decide
theorem children_work_216 : ∀ j, Template HasSnaky 5 (childrenC_216 j) (childrenD_216 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_7 6 (-4, -1)).mono (by decide)
  · exact (placed_template_map row_works_155 5 (1, 0)).mono (by decide)
theorem row_works_216 : Template HasSnaky 6 required_216 envelope_216 := by
  refine compose HasSnaky 5 childrenC_216 childrenD_216 children_work_216 (0, 0)
    required_216 envelope_216 pivot_mem_216 child_required_sub_216 child_envelope_sub_216 ?_
  intro b hb; exact common_sub_216 (mem_commonEnvelope childrenD_216 b hb)
def required_218 : Finset Cell := ⟨(([(-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -1), (1, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_218 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_218 : Fin 2 → Finset Cell := ![(placedSet 5 (-1, 3) required_0), (placedSet 0 (-2, 0) required_182)]
def childrenD_218 : Fin 2 → Finset Cell := ![(placedSet 5 (-1, 3) envelope_0), (placedSet 0 (-2, 0) envelope_182)]
theorem common_sub_218 : commonEnvelope childrenD_218 ⊆ insert (0, 0) required_218 := by decide
theorem child_required_sub_218 : ∀ j, childrenC_218 j ⊆ insert (0, 0) required_218 := by decide
theorem child_envelope_sub_218 : ∀ j, childrenD_218 j ⊆ envelope_218 := by decide
theorem pivot_mem_218 : (0, 0) ∈ envelope_218 := by decide
theorem children_work_218 : ∀ j, Template HasSnaky 5 (childrenC_218 j) (childrenD_218 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 5 (-1, 3)).mono (by decide)
  · exact (placed_template_map row_works_182 0 (-2, 0)).mono (by decide)
theorem row_works_218 : Template HasSnaky 6 required_218 envelope_218 := by
  refine compose HasSnaky 5 childrenC_218 childrenD_218 children_work_218 (0, 0)
    required_218 envelope_218 pivot_mem_218 child_required_sub_218 child_envelope_sub_218 ?_
  intro b hb; exact common_sub_218 (mem_commonEnvelope childrenD_218 b hb)
def required_222 : Finset Cell := ⟨(([(-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_222 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_222 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_6), (placedSet 5 (1, 0) required_158)]
def childrenD_222 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_6), (placedSet 5 (1, 0) envelope_158)]
theorem common_sub_222 : commonEnvelope childrenD_222 ⊆ insert (0, 0) required_222 := by decide
theorem child_required_sub_222 : ∀ j, childrenC_222 j ⊆ insert (0, 0) required_222 := by decide
theorem child_envelope_sub_222 : ∀ j, childrenD_222 j ⊆ envelope_222 := by decide
theorem pivot_mem_222 : (0, 0) ∈ envelope_222 := by decide
theorem children_work_222 : ∀ j, Template HasSnaky 5 (childrenC_222 j) (childrenD_222 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_158 5 (1, 0)).mono (by decide)
theorem row_works_222 : Template HasSnaky 6 required_222 envelope_222 := by
  refine compose HasSnaky 5 childrenC_222 childrenD_222 children_work_222 (0, 0)
    required_222 envelope_222 pivot_mem_222 child_required_sub_222 child_envelope_sub_222 ?_
  intro b hb; exact common_sub_222 (mem_commonEnvelope childrenD_222 b hb)
def required_228 : Finset Cell := ⟨(([(1, -2), (1, -1), (1, 0), (1, 1), (1, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_228 : Finset Cell := ⟨(([(-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 3), (0, 4), (0, 5), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_228 : Fin 2 → Finset Cell := ![(placedSet 0 (2, 1) required_82), (placedSet 3 (1, 3) required_68)]
def childrenD_228 : Fin 2 → Finset Cell := ![(placedSet 0 (2, 1) envelope_82), (placedSet 3 (1, 3) envelope_68)]
theorem common_sub_228 : commonEnvelope childrenD_228 ⊆ insert (0, 0) required_228 := by decide
theorem child_required_sub_228 : ∀ j, childrenC_228 j ⊆ insert (0, 0) required_228 := by decide
theorem child_envelope_sub_228 : ∀ j, childrenD_228 j ⊆ envelope_228 := by decide
theorem pivot_mem_228 : (0, 0) ∈ envelope_228 := by decide
theorem children_work_228 : ∀ j, Template HasSnaky 5 (childrenC_228 j) (childrenD_228 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_82 0 (2, 1)).mono (by decide)
  · exact (placed_template_map row_works_68 3 (1, 3)).mono (by decide)
theorem row_works_228 : Template HasSnaky 6 required_228 envelope_228 := by
  refine compose HasSnaky 5 childrenC_228 childrenD_228 children_work_228 (0, 0)
    required_228 envelope_228 pivot_mem_228 child_required_sub_228 child_envelope_sub_228 ?_
  intro b hb; exact common_sub_228 (mem_commonEnvelope childrenD_228 b hb)
def required_233 : Finset Cell := ⟨(([(-1, -2), (0, -2), (0, -1), (1, -2), (2, -2), (2, -1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_233 : Finset Cell := ⟨(([(-2, -3), (-1, -3), (-1, -2), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, 0), (2, -2), (2, -1), (2, 0), (2, 1), (3, 0), (3, 1), (3, 2), (4, 1), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_233 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, -3) required_32), (placedSet 0 (2, 0) required_133)]
def childrenD_233 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, -3) envelope_32), (placedSet 0 (2, 0) envelope_133)]
theorem common_sub_233 : commonEnvelope childrenD_233 ⊆ insert (0, 0) required_233 := by decide
theorem child_required_sub_233 : ∀ j, childrenC_233 j ⊆ insert (0, 0) required_233 := by decide
theorem child_envelope_sub_233 : ∀ j, childrenD_233 j ⊆ envelope_233 := by decide
theorem pivot_mem_233 : (0, 0) ∈ envelope_233 := by decide
theorem children_work_233 : ∀ j, Template HasSnaky 5 (childrenC_233 j) (childrenD_233 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_32 3 (-1, -3)).mono (by decide)
  · exact (placed_template_map row_works_133 0 (2, 0)).mono (by decide)
theorem row_works_233 : Template HasSnaky 6 required_233 envelope_233 := by
  refine compose HasSnaky 5 childrenC_233 childrenD_233 children_work_233 (0, 0)
    required_233 envelope_233 pivot_mem_233 child_required_sub_233 child_envelope_sub_233 ?_
  intro b hb; exact common_sub_233 (mem_commonEnvelope childrenD_233 b hb)
def required_236 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (-1, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_236 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_236 : Fin 4 → Finset Cell := ![(placedSet 1 (0, 1) required_38), (placedSet 7 (-1, 0) required_122), (placedSet 0 (-2, -1) required_181), (placedSet 1 (0, -1) required_30)]
def childrenD_236 : Fin 4 → Finset Cell := ![(placedSet 1 (0, 1) envelope_38), (placedSet 7 (-1, 0) envelope_122), (placedSet 0 (-2, -1) envelope_181), (placedSet 1 (0, -1) envelope_30)]
theorem common_sub_236 : commonEnvelope childrenD_236 ⊆ insert (0, 0) required_236 := by decide
theorem child_required_sub_236 : ∀ j, childrenC_236 j ⊆ insert (0, 0) required_236 := by decide
theorem child_envelope_sub_236 : ∀ j, childrenD_236 j ⊆ envelope_236 := by decide
theorem pivot_mem_236 : (0, 0) ∈ envelope_236 := by decide
theorem children_work_236 : ∀ j, Template HasSnaky 5 (childrenC_236 j) (childrenD_236 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_38 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_122 7 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_181 0 (-2, -1)).mono (by decide)
  · exact (placed_template_map row_works_30 1 (0, -1)).mono (by decide)
theorem row_works_236 : Template HasSnaky 6 required_236 envelope_236 := by
  refine compose HasSnaky 5 childrenC_236 childrenD_236 children_work_236 (0, 0)
    required_236 envelope_236 pivot_mem_236 child_required_sub_236 child_envelope_sub_236 ?_
  intro b hb; exact common_sub_236 (mem_commonEnvelope childrenD_236 b hb)
def required_270 : Finset Cell := ⟨(([(-1, -1), (0, -1), (0, 1), (0, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_270 : Finset Cell := ⟨(([(-1, -2), (-1, -1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_270 : Fin 2 → Finset Cell := ![(placedSet 0 (-1, 3) required_63), (placedSet 7 (-1, -2) required_6)]
def childrenD_270 : Fin 2 → Finset Cell := ![(placedSet 0 (-1, 3) envelope_63), (placedSet 7 (-1, -2) envelope_6)]
theorem common_sub_270 : commonEnvelope childrenD_270 ⊆ insert (0, 0) required_270 := by decide
theorem child_required_sub_270 : ∀ j, childrenC_270 j ⊆ insert (0, 0) required_270 := by decide
theorem child_envelope_sub_270 : ∀ j, childrenD_270 j ⊆ envelope_270 := by decide
theorem pivot_mem_270 : (0, 0) ∈ envelope_270 := by decide
theorem children_work_270 : ∀ j, Template HasSnaky 5 (childrenC_270 j) (childrenD_270 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_63 0 (-1, 3)).mono (by decide)
  · exact (placed_template_map row_works_6 7 (-1, -2)).mono (by decide)
theorem row_works_270 : Template HasSnaky 6 required_270 envelope_270 := by
  refine compose HasSnaky 5 childrenC_270 childrenD_270 children_work_270 (0, 0)
    required_270 envelope_270 pivot_mem_270 child_required_sub_270 child_envelope_sub_270 ?_
  intro b hb; exact common_sub_270 (mem_commonEnvelope childrenD_270 b hb)
end SnakyConditional

end OAI
