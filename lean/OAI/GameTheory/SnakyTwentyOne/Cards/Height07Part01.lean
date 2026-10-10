import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_116 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_116 : Finset Cell := ⟨(([(0, 2), (0, 4), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 3), (4, 3), (4, 4), (5, 3), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_116 : Fin 3 → Finset Cell := ![(placed21 1 (0, 3) required_7), (placed21 1 (0, 2) required_9), (placed21 2 (4, 0) required_115)]
def childrenD_116 : Fin 3 → Finset Cell := ![(placed21 1 (0, 3) envelope_7), (placed21 1 (0, 2) envelope_9), (placed21 2 (4, 0) envelope_115)]
theorem common_sub_116 : commonEnvelope childrenD_116 ⊆ insert (4, 3) required_116 := by decide +kernel
theorem child_required_sub_116 : ∀ j, childrenC_116 j ⊆ insert (4, 3) required_116 := by decide +kernel
theorem child_envelope_sub_116 : ∀ j, childrenD_116 j ⊆ envelope_116 := by decide +kernel
theorem pivot_mem_116 : (4, 3) ∈ envelope_116 := by decide +kernel
theorem children_work_116 : ∀ j, Template HasSnaky 6 (childrenC_116 j) (childrenD_116 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_115 2 (4, 0)).mono (by decide +kernel)
theorem row_works_116 : Template HasSnaky 7 required_116 envelope_116 := by
  refine compose HasSnaky 6 childrenC_116 childrenD_116 children_work_116 (4, 3)
    required_116 envelope_116 pivot_mem_116 child_required_sub_116 child_envelope_sub_116 ?_
  intro b hb
  exact common_sub_116 (mem_commonEnvelope childrenD_116 b hb)
def required_117 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_117 : Finset Cell := ⟨(([(0, 2), (0, 4), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 3), (4, 2), (4, 3), (5, 2), (5, 3), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_117 : Fin 3 → Finset Cell := ![(placed21 3 (0, 3) required_7), (placed21 3 (0, 4) required_9), (placed21 2 (4, 0) required_115)]
def childrenD_117 : Fin 3 → Finset Cell := ![(placed21 3 (0, 3) envelope_7), (placed21 3 (0, 4) envelope_9), (placed21 2 (4, 0) envelope_115)]
theorem common_sub_117 : commonEnvelope childrenD_117 ⊆ insert (4, 3) required_117 := by decide +kernel
theorem child_required_sub_117 : ∀ j, childrenC_117 j ⊆ insert (4, 3) required_117 := by decide +kernel
theorem child_envelope_sub_117 : ∀ j, childrenD_117 j ⊆ envelope_117 := by decide +kernel
theorem pivot_mem_117 : (4, 3) ∈ envelope_117 := by decide +kernel
theorem children_work_117 : ∀ j, Template HasSnaky 6 (childrenC_117 j) (childrenD_117 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 3 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 3 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_115 2 (4, 0)).mono (by decide +kernel)
theorem row_works_117 : Template HasSnaky 7 required_117 envelope_117 := by
  refine compose HasSnaky 6 childrenC_117 childrenD_117 children_work_117 (4, 3)
    required_117 envelope_117 pivot_mem_117 child_required_sub_117 child_envelope_sub_117 ?_
  intro b hb
  exact common_sub_117 (mem_commonEnvelope childrenD_117 b hb)
def required_118 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_118 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_118 : Fin 3 → Finset Cell := ![(placed21 3 (0, 3) required_7), (placed21 1 (0, 2) required_9), (placed21 0 (1, 0) required_115)]
def childrenD_118 : Fin 3 → Finset Cell := ![(placed21 3 (0, 3) envelope_7), (placed21 1 (0, 2) envelope_9), (placed21 0 (1, 0) envelope_115)]
theorem common_sub_118 : commonEnvelope childrenD_118 ⊆ insert (4, 3) required_118 := by decide +kernel
theorem child_required_sub_118 : ∀ j, childrenC_118 j ⊆ insert (4, 3) required_118 := by decide +kernel
theorem child_envelope_sub_118 : ∀ j, childrenD_118 j ⊆ envelope_118 := by decide +kernel
theorem pivot_mem_118 : (4, 3) ∈ envelope_118 := by decide +kernel
theorem children_work_118 : ∀ j, Template HasSnaky 6 (childrenC_118 j) (childrenD_118 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 3 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_115 0 (1, 0)).mono (by decide +kernel)
theorem row_works_118 : Template HasSnaky 7 required_118 envelope_118 := by
  refine compose HasSnaky 6 childrenC_118 childrenD_118 children_work_118 (4, 3)
    required_118 envelope_118 pivot_mem_118 child_required_sub_118 child_envelope_sub_118 ?_
  intro b hb
  exact common_sub_118 (mem_commonEnvelope childrenD_118 b hb)
def required_204 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_204 : Finset Cell := ⟨(([(0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (3, 2), (3, 3), (3, 4), (3, 6), (3, 7), (3, 8), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_204 : Fin 2 → Finset Cell := ![(placed21 4 (1, 6) required_52), (placed21 1 (0, 2) required_203)]
def childrenD_204 : Fin 2 → Finset Cell := ![(placed21 4 (1, 6) envelope_52), (placed21 1 (0, 2) envelope_203)]
theorem common_sub_204 : commonEnvelope childrenD_204 ⊆ insert (2, 3) required_204 := by decide +kernel
theorem child_required_sub_204 : ∀ j, childrenC_204 j ⊆ insert (2, 3) required_204 := by decide +kernel
theorem child_envelope_sub_204 : ∀ j, childrenD_204 j ⊆ envelope_204 := by decide +kernel
theorem pivot_mem_204 : (2, 3) ∈ envelope_204 := by decide +kernel
theorem children_work_204 : ∀ j, Template HasSnaky 6 (childrenC_204 j) (childrenD_204 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 4 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_203 1 (0, 2)).mono (by decide +kernel)
theorem row_works_204 : Template HasSnaky 7 required_204 envelope_204 := by
  refine compose HasSnaky 6 childrenC_204 childrenD_204 children_work_204 (2, 3)
    required_204 envelope_204 pivot_mem_204 child_required_sub_204 child_envelope_sub_204 ?_
  intro b hb
  exact common_sub_204 (mem_commonEnvelope childrenD_204 b hb)
def required_256 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_256 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_256 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) required_5), required_255]
def childrenD_256 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) envelope_5), envelope_255]
theorem common_sub_256 : commonEnvelope childrenD_256 ⊆ insert (3, 4) required_256 := by decide +kernel
theorem child_required_sub_256 : ∀ j, childrenC_256 j ⊆ insert (3, 4) required_256 := by decide +kernel
theorem child_envelope_sub_256 : ∀ j, childrenD_256 j ⊆ envelope_256 := by decide +kernel
theorem pivot_mem_256 : (3, 4) ∈ envelope_256 := by decide +kernel
theorem children_work_256 : ∀ j, Template HasSnaky 6 (childrenC_256 j) (childrenD_256 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 3)).mono (by decide +kernel)
  · exact row_works_255.mono (by decide +kernel)
theorem row_works_256 : Template HasSnaky 7 required_256 envelope_256 := by
  refine compose HasSnaky 6 childrenC_256 childrenD_256 children_work_256 (3, 4)
    required_256 envelope_256 pivot_mem_256 child_required_sub_256 child_envelope_sub_256 ?_
  intro b hb
  exact common_sub_256 (mem_commonEnvelope childrenD_256 b hb)
def required_276 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_276 : Finset Cell := ⟨(([(0, 3), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 6), (3, 7), (3, 8), (4, 2), (4, 6), (5, 2), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_276 : Fin 4 → Finset Cell := ![(placed21 6 (2, 6) required_44), (placed21 6 (2, 6) required_52), (placed21 3 (0, 6) required_155), (placed21 1 (0, 2) required_275)]
def childrenD_276 : Fin 4 → Finset Cell := ![(placed21 6 (2, 6) envelope_44), (placed21 6 (2, 6) envelope_52), (placed21 3 (0, 6) envelope_155), (placed21 1 (0, 2) envelope_275)]
theorem common_sub_276 : commonEnvelope childrenD_276 ⊆ insert (2, 4) required_276 := by decide +kernel
theorem child_required_sub_276 : ∀ j, childrenC_276 j ⊆ insert (2, 4) required_276 := by decide +kernel
theorem child_envelope_sub_276 : ∀ j, childrenD_276 j ⊆ envelope_276 := by decide +kernel
theorem pivot_mem_276 : (2, 4) ∈ envelope_276 := by decide +kernel
theorem children_work_276 : ∀ j, Template HasSnaky 6 (childrenC_276 j) (childrenD_276 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 6 (2, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 6 (2, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_155 3 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_275 1 (0, 2)).mono (by decide +kernel)
theorem row_works_276 : Template HasSnaky 7 required_276 envelope_276 := by
  refine compose HasSnaky 6 childrenC_276 childrenD_276 children_work_276 (2, 4)
    required_276 envelope_276 pivot_mem_276 child_required_sub_276 child_envelope_sub_276 ?_
  intro b hb
  exact common_sub_276 (mem_commonEnvelope childrenD_276 b hb)
def required_286 : Finset Cell := ⟨(([(0, 1), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_286 : Finset Cell := ⟨(([(0, 1), (0, 3), (1, 1), (1, 3), (2, 0), (2, 1), (2, 3), (2, 4), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_286 : Fin 2 → Finset Cell := ![(placed21 7 (4, 4) required_35), (placed21 5 (6, 1) required_253)]
def childrenD_286 : Fin 2 → Finset Cell := ![(placed21 7 (4, 4) envelope_35), (placed21 5 (6, 1) envelope_253)]
theorem common_sub_286 : commonEnvelope childrenD_286 ⊆ insert (4, 2) required_286 := by decide +kernel
theorem child_required_sub_286 : ∀ j, childrenC_286 j ⊆ insert (4, 2) required_286 := by decide +kernel
theorem child_envelope_sub_286 : ∀ j, childrenD_286 j ⊆ envelope_286 := by decide +kernel
theorem pivot_mem_286 : (4, 2) ∈ envelope_286 := by decide +kernel
theorem children_work_286 : ∀ j, Template HasSnaky 6 (childrenC_286 j) (childrenD_286 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_35 7 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_253 5 (6, 1)).mono (by decide +kernel)
theorem row_works_286 : Template HasSnaky 7 required_286 envelope_286 := by
  refine compose HasSnaky 6 childrenC_286 childrenD_286 children_work_286 (4, 2)
    required_286 envelope_286 pivot_mem_286 child_required_sub_286 child_envelope_sub_286 ?_
  intro b hb
  exact common_sub_286 (mem_commonEnvelope childrenD_286 b hb)
def required_290 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 4), (3, 1), (3, 4), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_290 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (3, 1), (3, 4), (4, 1), (4, 3), (4, 4), (5, 3), (5, 4), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_290 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) required_5), required_203]
def childrenD_290 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) envelope_5), envelope_203]
theorem common_sub_290 : commonEnvelope childrenD_290 ⊆ insert (2, 1) required_290 := by decide +kernel
theorem child_required_sub_290 : ∀ j, childrenC_290 j ⊆ insert (2, 1) required_290 := by decide +kernel
theorem child_envelope_sub_290 : ∀ j, childrenD_290 j ⊆ envelope_290 := by decide +kernel
theorem pivot_mem_290 : (2, 1) ∈ envelope_290 := by decide +kernel
theorem children_work_290 : ∀ j, Template HasSnaky 6 (childrenC_290 j) (childrenD_290 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 2 (4, 1)).mono (by decide +kernel)
  · exact row_works_203.mono (by decide +kernel)
theorem row_works_290 : Template HasSnaky 7 required_290 envelope_290 := by
  refine compose HasSnaky 6 childrenC_290 childrenD_290 children_work_290 (2, 1)
    required_290 envelope_290 pivot_mem_290 child_required_sub_290 child_envelope_sub_290 ?_
  intro b hb
  exact common_sub_290 (mem_commonEnvelope childrenD_290 b hb)
def required_295 : Finset Cell := ⟨(([(1, 1), (1, 2), (4, 1), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_295 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (1, 4), (2, 1), (2, 4), (3, 1), (3, 2), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_295 : Fin 2 → Finset Cell := ![(placed21 5 (5, 1) required_34), (placed21 5 (6, 0) required_180)]
def childrenD_295 : Fin 2 → Finset Cell := ![(placed21 5 (5, 1) envelope_34), (placed21 5 (6, 0) envelope_180)]
theorem common_sub_295 : commonEnvelope childrenD_295 ⊆ insert (3, 1) required_295 := by decide +kernel
theorem child_required_sub_295 : ∀ j, childrenC_295 j ⊆ insert (3, 1) required_295 := by decide +kernel
theorem child_envelope_sub_295 : ∀ j, childrenD_295 j ⊆ envelope_295 := by decide +kernel
theorem pivot_mem_295 : (3, 1) ∈ envelope_295 := by decide +kernel
theorem children_work_295 : ∀ j, Template HasSnaky 6 (childrenC_295 j) (childrenD_295 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_34 5 (5, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_180 5 (6, 0)).mono (by decide +kernel)
theorem row_works_295 : Template HasSnaky 7 required_295 envelope_295 := by
  refine compose HasSnaky 6 childrenC_295 childrenD_295 children_work_295 (3, 1)
    required_295 envelope_295 pivot_mem_295 child_required_sub_295 child_envelope_sub_295 ?_
  intro b hb
  exact common_sub_295 (mem_commonEnvelope childrenD_295 b hb)
def required_297 : Finset Cell := ⟨(([(2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_297 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 3), (5, 4), (6, 3), (6, 4), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_297 : Fin 3 → Finset Cell := ![(placed21 7 (6, 4) required_9), (placed21 0 (1, 0) required_142), (placed21 4 (2, 6) required_162)]
def childrenD_297 : Fin 3 → Finset Cell := ![(placed21 7 (6, 4) envelope_9), (placed21 0 (1, 0) envelope_142), (placed21 4 (2, 6) envelope_162)]
theorem common_sub_297 : commonEnvelope childrenD_297 ⊆ insert (5, 3) required_297 := by decide +kernel
theorem child_required_sub_297 : ∀ j, childrenC_297 j ⊆ insert (5, 3) required_297 := by decide +kernel
theorem child_envelope_sub_297 : ∀ j, childrenD_297 j ⊆ envelope_297 := by decide +kernel
theorem pivot_mem_297 : (5, 3) ∈ envelope_297 := by decide +kernel
theorem children_work_297 : ∀ j, Template HasSnaky 6 (childrenC_297 j) (childrenD_297 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_9 7 (6, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_142 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_162 4 (2, 6)).mono (by decide +kernel)
theorem row_works_297 : Template HasSnaky 7 required_297 envelope_297 := by
  refine compose HasSnaky 6 childrenC_297 childrenD_297 children_work_297 (5, 3)
    required_297 envelope_297 pivot_mem_297 child_required_sub_297 child_envelope_sub_297 ?_
  intro b hb
  exact common_sub_297 (mem_commonEnvelope childrenD_297 b hb)
def required_298 : Finset Cell := ⟨(([(2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_298 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 2), (5, 3), (6, 2), (6, 3), (7, 2), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_298 : Fin 3 → Finset Cell := ![(placed21 7 (6, 3) required_7), (placed21 0 (1, 0) required_142), (placed21 4 (2, 6) required_161)]
def childrenD_298 : Fin 3 → Finset Cell := ![(placed21 7 (6, 3) envelope_7), (placed21 0 (1, 0) envelope_142), (placed21 4 (2, 6) envelope_161)]
theorem common_sub_298 : commonEnvelope childrenD_298 ⊆ insert (5, 3) required_298 := by decide +kernel
theorem child_required_sub_298 : ∀ j, childrenC_298 j ⊆ insert (5, 3) required_298 := by decide +kernel
theorem child_envelope_sub_298 : ∀ j, childrenD_298 j ⊆ envelope_298 := by decide +kernel
theorem pivot_mem_298 : (5, 3) ∈ envelope_298 := by decide +kernel
theorem children_work_298 : ∀ j, Template HasSnaky 6 (childrenC_298 j) (childrenD_298 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 7 (6, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_142 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_161 4 (2, 6)).mono (by decide +kernel)
theorem row_works_298 : Template HasSnaky 7 required_298 envelope_298 := by
  refine compose HasSnaky 6 childrenC_298 childrenD_298 children_work_298 (5, 3)
    required_298 envelope_298 pivot_mem_298 child_required_sub_298 child_envelope_sub_298 ?_
  intro b hb
  exact common_sub_298 (mem_commonEnvelope childrenD_298 b hb)
def required_309 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_309 : Finset Cell := ⟨(([(0, 2), (0, 4), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 3), (4, 3), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4), (7, 2), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_309 : Fin 3 → Finset Cell := ![(placed21 1 (0, 2) required_19), (placed21 3 (0, 4) required_19), (placed21 2 (4, 0) required_115)]
def childrenD_309 : Fin 3 → Finset Cell := ![(placed21 1 (0, 2) envelope_19), (placed21 3 (0, 4) envelope_19), (placed21 2 (4, 0) envelope_115)]
theorem common_sub_309 : commonEnvelope childrenD_309 ⊆ insert (4, 3) required_309 := by decide +kernel
theorem child_required_sub_309 : ∀ j, childrenC_309 j ⊆ insert (4, 3) required_309 := by decide +kernel
theorem child_envelope_sub_309 : ∀ j, childrenD_309 j ⊆ envelope_309 := by decide +kernel
theorem pivot_mem_309 : (4, 3) ∈ envelope_309 := by decide +kernel
theorem children_work_309 : ∀ j, Template HasSnaky 6 (childrenC_309 j) (childrenD_309 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_19 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_19 3 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_115 2 (4, 0)).mono (by decide +kernel)
theorem row_works_309 : Template HasSnaky 7 required_309 envelope_309 := by
  refine compose HasSnaky 6 childrenC_309 childrenD_309 children_work_309 (4, 3)
    required_309 envelope_309 pivot_mem_309 child_required_sub_309 child_envelope_sub_309 ?_
  intro b hb
  exact common_sub_309 (mem_commonEnvelope childrenD_309 b hb)
def required_317 : Finset Cell := ⟨(([(1, 4), (2, 4), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_317 : Finset Cell := ⟨(([(0, 4), (1, 4), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 5), (4, 6), (4, 7), (4, 8), (5, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_317 : Fin 3 → Finset Cell := ![(placed21 1 (0, 4) required_44), (placed21 2 (4, 2) required_60), (placed21 0 (2, 0) required_316)]
def childrenD_317 : Fin 3 → Finset Cell := ![(placed21 1 (0, 4) envelope_44), (placed21 2 (4, 2) envelope_60), (placed21 0 (2, 0) envelope_316)]
theorem common_sub_317 : commonEnvelope childrenD_317 ⊆ insert (3, 5) required_317 := by decide +kernel
theorem child_required_sub_317 : ∀ j, childrenC_317 j ⊆ insert (3, 5) required_317 := by decide +kernel
theorem child_envelope_sub_317 : ∀ j, childrenD_317 j ⊆ envelope_317 := by decide +kernel
theorem pivot_mem_317 : (3, 5) ∈ envelope_317 := by decide +kernel
theorem children_work_317 : ∀ j, Template HasSnaky 6 (childrenC_317 j) (childrenD_317 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 1 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_60 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_316 0 (2, 0)).mono (by decide +kernel)
theorem row_works_317 : Template HasSnaky 7 required_317 envelope_317 := by
  refine compose HasSnaky 6 childrenC_317 childrenD_317 children_work_317 (3, 5)
    required_317 envelope_317 pivot_mem_317 child_required_sub_317 child_envelope_sub_317 ?_
  intro b hb
  exact common_sub_317 (mem_commonEnvelope childrenD_317 b hb)
def required_318 : Finset Cell := ⟨(([(0, 3), (0, 5), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_318 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 2), (2, 7), (2, 8), (2, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_318 : Fin 4 → Finset Cell := ![(placed21 4 (0, 6) required_10), (placed21 2 (1, 2) required_52), (placed21 6 (1, 6) required_52), (placed21 0 (0, 2) required_315)]
def childrenD_318 : Fin 4 → Finset Cell := ![(placed21 4 (0, 6) envelope_10), (placed21 2 (1, 2) envelope_52), (placed21 6 (1, 6) envelope_52), (placed21 0 (0, 2) envelope_315)]
theorem common_sub_318 : commonEnvelope childrenD_318 ⊆ insert (1, 3) required_318 := by decide +kernel
theorem child_required_sub_318 : ∀ j, childrenC_318 j ⊆ insert (1, 3) required_318 := by decide +kernel
theorem child_envelope_sub_318 : ∀ j, childrenD_318 j ⊆ envelope_318 := by decide +kernel
theorem pivot_mem_318 : (1, 3) ∈ envelope_318 := by decide +kernel
theorem children_work_318 : ∀ j, Template HasSnaky 6 (childrenC_318 j) (childrenD_318 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 4 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 2 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 6 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_315 0 (0, 2)).mono (by decide +kernel)
theorem row_works_318 : Template HasSnaky 7 required_318 envelope_318 := by
  refine compose HasSnaky 6 childrenC_318 childrenD_318 children_work_318 (1, 3)
    required_318 envelope_318 pivot_mem_318 child_required_sub_318 child_envelope_sub_318 ?_
  intro b hb
  exact common_sub_318 (mem_commonEnvelope childrenD_318 b hb)
def required_320 : Finset Cell := ⟨(([(0, 4), (1, 4), (2, 4), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_320 : Finset Cell := ⟨(([(0, 4), (1, 4), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 5), (4, 6), (4, 7), (4, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_320 : Fin 2 → Finset Cell := ![(placed21 0 (0, 4) required_5), (placed21 0 (2, 0) required_316)]
def childrenD_320 : Fin 2 → Finset Cell := ![(placed21 0 (0, 4) envelope_5), (placed21 0 (2, 0) envelope_316)]
theorem common_sub_320 : commonEnvelope childrenD_320 ⊆ insert (3, 5) required_320 := by decide +kernel
theorem child_required_sub_320 : ∀ j, childrenC_320 j ⊆ insert (3, 5) required_320 := by decide +kernel
theorem child_envelope_sub_320 : ∀ j, childrenD_320 j ⊆ envelope_320 := by decide +kernel
theorem pivot_mem_320 : (3, 5) ∈ envelope_320 := by decide +kernel
theorem children_work_320 : ∀ j, Template HasSnaky 6 (childrenC_320 j) (childrenD_320 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_316 0 (2, 0)).mono (by decide +kernel)
theorem row_works_320 : Template HasSnaky 7 required_320 envelope_320 := by
  refine compose HasSnaky 6 childrenC_320 childrenD_320 children_work_320 (3, 5)
    required_320 envelope_320 pivot_mem_320 child_required_sub_320 child_envelope_sub_320 ?_
  intro b hb
  exact common_sub_320 (mem_commonEnvelope childrenD_320 b hb)
def required_324 : Finset Cell := ⟨(([(1, 4), (1, 5), (2, 4), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_324 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 6), (0, 7), (0, 8), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 4), (4, 4), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_324 : Fin 4 → Finset Cell := ![(placed21 4 (0, 6) required_60), (placed21 0 (0, 2) required_237), (placed21 0 (0, 2) required_307), (placed21 2 (2, 0) required_316)]
def childrenD_324 : Fin 4 → Finset Cell := ![(placed21 4 (0, 6) envelope_60), (placed21 0 (0, 2) envelope_237), (placed21 0 (0, 2) envelope_307), (placed21 2 (2, 0) envelope_316)]
theorem common_sub_324 : commonEnvelope childrenD_324 ⊆ insert (1, 3) required_324 := by decide +kernel
theorem child_required_sub_324 : ∀ j, childrenC_324 j ⊆ insert (1, 3) required_324 := by decide +kernel
theorem child_envelope_sub_324 : ∀ j, childrenD_324 j ⊆ envelope_324 := by decide +kernel
theorem pivot_mem_324 : (1, 3) ∈ envelope_324 := by decide +kernel
theorem children_work_324 : ∀ j, Template HasSnaky 6 (childrenC_324 j) (childrenD_324 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_60 4 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_237 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_307 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_316 2 (2, 0)).mono (by decide +kernel)
theorem row_works_324 : Template HasSnaky 7 required_324 envelope_324 := by
  refine compose HasSnaky 6 childrenC_324 childrenD_324 children_work_324 (1, 3)
    required_324 envelope_324 pivot_mem_324 child_required_sub_324 child_envelope_sub_324 ?_
  intro b hb
  exact common_sub_324 (mem_commonEnvelope childrenD_324 b hb)
def required_329 : Finset Cell := ⟨(([(0, 3), (0, 5), (1, 3), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_329 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 2), (2, 7), (2, 8), (2, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_329 : Fin 4 → Finset Cell := ![(placed21 4 (0, 6) required_10), (placed21 2 (1, 2) required_52), (placed21 6 (1, 6) required_52), (placed21 0 (0, 2) required_315)]
def childrenD_329 : Fin 4 → Finset Cell := ![(placed21 4 (0, 6) envelope_10), (placed21 2 (1, 2) envelope_52), (placed21 6 (1, 6) envelope_52), (placed21 0 (0, 2) envelope_315)]
theorem common_sub_329 : commonEnvelope childrenD_329 ⊆ insert (1, 4) required_329 := by decide +kernel
theorem child_required_sub_329 : ∀ j, childrenC_329 j ⊆ insert (1, 4) required_329 := by decide +kernel
theorem child_envelope_sub_329 : ∀ j, childrenD_329 j ⊆ envelope_329 := by decide +kernel
theorem pivot_mem_329 : (1, 4) ∈ envelope_329 := by decide +kernel
theorem children_work_329 : ∀ j, Template HasSnaky 6 (childrenC_329 j) (childrenD_329 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 4 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 2 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 6 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_315 0 (0, 2)).mono (by decide +kernel)
theorem row_works_329 : Template HasSnaky 7 required_329 envelope_329 := by
  refine compose HasSnaky 6 childrenC_329 childrenD_329 children_work_329 (1, 4)
    required_329 envelope_329 pivot_mem_329 child_required_sub_329 child_envelope_sub_329 ?_
  intro b hb
  exact common_sub_329 (mem_commonEnvelope childrenD_329 b hb)
def required_332 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 4), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_332 : Finset Cell := ⟨(([(0, 2), (0, 4), (0, 5), (0, 6), (0, 7), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 3), (4, 3), (4, 4), (5, 3), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_332 : Fin 3 → Finset Cell := ![(placed21 1 (0, 2) required_9), (placed21 1 (0, 3) required_11), (placed21 2 (4, 0) required_331)]
def childrenD_332 : Fin 3 → Finset Cell := ![(placed21 1 (0, 2) envelope_9), (placed21 1 (0, 3) envelope_11), (placed21 2 (4, 0) envelope_331)]
theorem common_sub_332 : commonEnvelope childrenD_332 ⊆ insert (4, 3) required_332 := by decide +kernel
theorem child_required_sub_332 : ∀ j, childrenC_332 j ⊆ insert (4, 3) required_332 := by decide +kernel
theorem child_envelope_sub_332 : ∀ j, childrenD_332 j ⊆ envelope_332 := by decide +kernel
theorem pivot_mem_332 : (4, 3) ∈ envelope_332 := by decide +kernel
theorem children_work_332 : ∀ j, Template HasSnaky 6 (childrenC_332 j) (childrenD_332 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_9 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_11 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_331 2 (4, 0)).mono (by decide +kernel)
theorem row_works_332 : Template HasSnaky 7 required_332 envelope_332 := by
  refine compose HasSnaky 6 childrenC_332 childrenD_332 children_work_332 (4, 3)
    required_332 envelope_332 pivot_mem_332 child_required_sub_332 child_envelope_sub_332 ?_
  intro b hb
  exact common_sub_332 (mem_commonEnvelope childrenD_332 b hb)
def required_337 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_337 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (0, 7), (0, 8), (0, 9), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_337 : Fin 3 → Finset Cell := ![(placed21 4 (1, 6) required_7), (placed21 3 (0, 5) required_143), (placed21 0 (0, 2) required_336)]
def childrenD_337 : Fin 3 → Finset Cell := ![(placed21 4 (1, 6) envelope_7), (placed21 3 (0, 5) envelope_143), (placed21 0 (0, 2) envelope_336)]
theorem common_sub_337 : commonEnvelope childrenD_337 ⊆ insert (1, 2) required_337 := by decide +kernel
theorem child_required_sub_337 : ∀ j, childrenC_337 j ⊆ insert (1, 2) required_337 := by decide +kernel
theorem child_envelope_sub_337 : ∀ j, childrenD_337 j ⊆ envelope_337 := by decide +kernel
theorem pivot_mem_337 : (1, 2) ∈ envelope_337 := by decide +kernel
theorem children_work_337 : ∀ j, Template HasSnaky 6 (childrenC_337 j) (childrenD_337 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 4 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_143 3 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_336 0 (0, 2)).mono (by decide +kernel)
theorem row_works_337 : Template HasSnaky 7 required_337 envelope_337 := by
  refine compose HasSnaky 6 childrenC_337 childrenD_337 children_work_337 (1, 2)
    required_337 envelope_337 pivot_mem_337 child_required_sub_337 child_envelope_sub_337 ?_
  intro b hb
  exact common_sub_337 (mem_commonEnvelope childrenD_337 b hb)
def required_339 : Finset Cell := ⟨(([(0, 1), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_339 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 6), (4, 7), (4, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_339 : Fin 2 → Finset Cell := ![(placed21 7 (4, 4) required_35), (placed21 2 (4, 1) required_336)]
def childrenD_339 : Fin 2 → Finset Cell := ![(placed21 7 (4, 4) envelope_35), (placed21 2 (4, 1) envelope_336)]
theorem common_sub_339 : commonEnvelope childrenD_339 ⊆ insert (4, 2) required_339 := by decide +kernel
theorem child_required_sub_339 : ∀ j, childrenC_339 j ⊆ insert (4, 2) required_339 := by decide +kernel
theorem child_envelope_sub_339 : ∀ j, childrenD_339 j ⊆ envelope_339 := by decide +kernel
theorem pivot_mem_339 : (4, 2) ∈ envelope_339 := by decide +kernel
theorem children_work_339 : ∀ j, Template HasSnaky 6 (childrenC_339 j) (childrenD_339 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_35 7 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_336 2 (4, 1)).mono (by decide +kernel)
theorem row_works_339 : Template HasSnaky 7 required_339 envelope_339 := by
  refine compose HasSnaky 6 childrenC_339 childrenD_339 children_work_339 (4, 2)
    required_339 envelope_339 pivot_mem_339 child_required_sub_339 child_envelope_sub_339 ?_
  intro b hb
  exact common_sub_339 (mem_commonEnvelope childrenD_339 b hb)
def required_341 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_341 : Finset Cell := ⟨(([(0, 3), (0, 5), (1, 3), (1, 5), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 7), (4, 8), (4, 9), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_341 : Fin 3 → Finset Cell := ![(placed21 7 (6, 4) required_53), (placed21 5 (6, 2) required_57), (placed21 0 (2, 0) required_340)]
def childrenD_341 : Fin 3 → Finset Cell := ![(placed21 7 (6, 4) envelope_53), (placed21 5 (6, 2) envelope_57), (placed21 0 (2, 0) envelope_340)]
theorem common_sub_341 : commonEnvelope childrenD_341 ⊆ insert (4, 4) required_341 := by decide +kernel
theorem child_required_sub_341 : ∀ j, childrenC_341 j ⊆ insert (4, 4) required_341 := by decide +kernel
theorem child_envelope_sub_341 : ∀ j, childrenD_341 j ⊆ envelope_341 := by decide +kernel
theorem pivot_mem_341 : (4, 4) ∈ envelope_341 := by decide +kernel
theorem children_work_341 : ∀ j, Template HasSnaky 6 (childrenC_341 j) (childrenD_341 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_53 7 (6, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_57 5 (6, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_340 0 (2, 0)).mono (by decide +kernel)
theorem row_works_341 : Template HasSnaky 7 required_341 envelope_341 := by
  refine compose HasSnaky 6 childrenC_341 childrenD_341 children_work_341 (4, 4)
    required_341 envelope_341 pivot_mem_341 child_required_sub_341 child_envelope_sub_341 ?_
  intro b hb
  exact common_sub_341 (mem_commonEnvelope childrenD_341 b hb)
def required_344 : Finset Cell := ⟨(([(1, 2), (2, 2), (2, 3), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_344 : Finset Cell := ⟨(([(0, 3), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 3), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_344 : Fin 2 → Finset Cell := ![(placed21 2 (4, 2) required_5), (placed21 0 (1, 0) required_343)]
def childrenD_344 : Fin 2 → Finset Cell := ![(placed21 2 (4, 2) envelope_5), (placed21 0 (1, 0) envelope_343)]
theorem common_sub_344 : commonEnvelope childrenD_344 ⊆ insert (1, 3) required_344 := by decide +kernel
theorem child_required_sub_344 : ∀ j, childrenC_344 j ⊆ insert (1, 3) required_344 := by decide +kernel
theorem child_envelope_sub_344 : ∀ j, childrenD_344 j ⊆ envelope_344 := by decide +kernel
theorem pivot_mem_344 : (1, 3) ∈ envelope_344 := by decide +kernel
theorem children_work_344 : ∀ j, Template HasSnaky 6 (childrenC_344 j) (childrenD_344 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_343 0 (1, 0)).mono (by decide +kernel)
theorem row_works_344 : Template HasSnaky 7 required_344 envelope_344 := by
  refine compose HasSnaky 6 childrenC_344 childrenD_344 children_work_344 (1, 3)
    required_344 envelope_344 pivot_mem_344 child_required_sub_344 child_envelope_sub_344 ?_
  intro b hb
  exact common_sub_344 (mem_commonEnvelope childrenD_344 b hb)
def required_353 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (1, 5), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_353 : Finset Cell := ⟨(([(0, 6), (0, 7), (0, 8), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_353 : Fin 2 → Finset Cell := ![(placed21 6 (5, 9) required_95), (placed21 1 (0, 2) required_352)]
def childrenD_353 : Fin 2 → Finset Cell := ![(placed21 6 (5, 9) envelope_95), (placed21 1 (0, 2) envelope_352)]
theorem common_sub_353 : commonEnvelope childrenD_353 ⊆ insert (4, 6) required_353 := by decide +kernel
theorem child_required_sub_353 : ∀ j, childrenC_353 j ⊆ insert (4, 6) required_353 := by decide +kernel
theorem child_envelope_sub_353 : ∀ j, childrenD_353 j ⊆ envelope_353 := by decide +kernel
theorem pivot_mem_353 : (4, 6) ∈ envelope_353 := by decide +kernel
theorem children_work_353 : ∀ j, Template HasSnaky 6 (childrenC_353 j) (childrenD_353 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_95 6 (5, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_352 1 (0, 2)).mono (by decide +kernel)
theorem row_works_353 : Template HasSnaky 7 required_353 envelope_353 := by
  refine compose HasSnaky 6 childrenC_353 childrenD_353 children_work_353 (4, 6)
    required_353 envelope_353 pivot_mem_353 child_required_sub_353 child_envelope_sub_353 ?_
  intro b hb
  exact common_sub_353 (mem_commonEnvelope childrenD_353 b hb)
def height_116 : ℕ := 7
def childrenH_116 : Fin 3 → ℕ := ![height_7, height_9, height_115]
theorem height_exact_116 : height_116 = 1 + Finset.univ.sup childrenH_116 := by decide +kernel
theorem required_origin_116 : ∀ x ∈ required_116,
    (∃ j, x ∈ childrenC_116 j) ∨ ∀ j, x ∈ childrenD_116 j := by decide +kernel
theorem required_exact_116 : required_116 =
    ((Finset.univ.biUnion childrenC_116) ∪ commonEnvelope childrenD_116).erase (4, 3) := by
  exact required_eq_combination childrenC_116 childrenD_116 (4, 3) required_116
    (by decide +kernel) child_required_sub_116 common_sub_116 required_origin_116
theorem envelope_origin_116 : ∀ x ∈ envelope_116,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_116 j := by decide +kernel
theorem envelope_exact_116 : envelope_116 =
    insert (4, 3) (Finset.univ.biUnion childrenD_116) := by
  exact envelope_eq_combination childrenD_116 (4, 3) envelope_116
    pivot_mem_116 child_envelope_sub_116 envelope_origin_116
def checked_116 : CheckedCard where
  required := required_116
  envelope := envelope_116
  height := height_116
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_116
def height_117 : ℕ := 7
def childrenH_117 : Fin 3 → ℕ := ![height_7, height_9, height_115]
theorem height_exact_117 : height_117 = 1 + Finset.univ.sup childrenH_117 := by decide +kernel
theorem required_origin_117 : ∀ x ∈ required_117,
    (∃ j, x ∈ childrenC_117 j) ∨ ∀ j, x ∈ childrenD_117 j := by decide +kernel
theorem required_exact_117 : required_117 =
    ((Finset.univ.biUnion childrenC_117) ∪ commonEnvelope childrenD_117).erase (4, 3) := by
  exact required_eq_combination childrenC_117 childrenD_117 (4, 3) required_117
    (by decide +kernel) child_required_sub_117 common_sub_117 required_origin_117
theorem envelope_origin_117 : ∀ x ∈ envelope_117,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_117 j := by decide +kernel
theorem envelope_exact_117 : envelope_117 =
    insert (4, 3) (Finset.univ.biUnion childrenD_117) := by
  exact envelope_eq_combination childrenD_117 (4, 3) envelope_117
    pivot_mem_117 child_envelope_sub_117 envelope_origin_117
def checked_117 : CheckedCard where
  required := required_117
  envelope := envelope_117
  height := height_117
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_117
def height_118 : ℕ := 7
def childrenH_118 : Fin 3 → ℕ := ![height_7, height_9, height_115]
theorem height_exact_118 : height_118 = 1 + Finset.univ.sup childrenH_118 := by decide +kernel
theorem required_origin_118 : ∀ x ∈ required_118,
    (∃ j, x ∈ childrenC_118 j) ∨ ∀ j, x ∈ childrenD_118 j := by decide +kernel
theorem required_exact_118 : required_118 =
    ((Finset.univ.biUnion childrenC_118) ∪ commonEnvelope childrenD_118).erase (4, 3) := by
  exact required_eq_combination childrenC_118 childrenD_118 (4, 3) required_118
    (by decide +kernel) child_required_sub_118 common_sub_118 required_origin_118
theorem envelope_origin_118 : ∀ x ∈ envelope_118,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_118 j := by decide +kernel
theorem envelope_exact_118 : envelope_118 =
    insert (4, 3) (Finset.univ.biUnion childrenD_118) := by
  exact envelope_eq_combination childrenD_118 (4, 3) envelope_118
    pivot_mem_118 child_envelope_sub_118 envelope_origin_118
def checked_118 : CheckedCard where
  required := required_118
  envelope := envelope_118
  height := height_118
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_118
def height_204 : ℕ := 7
def childrenH_204 : Fin 2 → ℕ := ![height_52, height_203]
theorem height_exact_204 : height_204 = 1 + Finset.univ.sup childrenH_204 := by decide +kernel
theorem required_origin_204 : ∀ x ∈ required_204,
    (∃ j, x ∈ childrenC_204 j) ∨ ∀ j, x ∈ childrenD_204 j := by decide +kernel
theorem required_exact_204 : required_204 =
    ((Finset.univ.biUnion childrenC_204) ∪ commonEnvelope childrenD_204).erase (2, 3) := by
  exact required_eq_combination childrenC_204 childrenD_204 (2, 3) required_204
    (by decide +kernel) child_required_sub_204 common_sub_204 required_origin_204
theorem envelope_origin_204 : ∀ x ∈ envelope_204,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_204 j := by decide +kernel
theorem envelope_exact_204 : envelope_204 =
    insert (2, 3) (Finset.univ.biUnion childrenD_204) := by
  exact envelope_eq_combination childrenD_204 (2, 3) envelope_204
    pivot_mem_204 child_envelope_sub_204 envelope_origin_204
def checked_204 : CheckedCard where
  required := required_204
  envelope := envelope_204
  height := height_204
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_204
def height_256 : ℕ := 7
def childrenH_256 : Fin 2 → ℕ := ![height_5, height_255]
theorem height_exact_256 : height_256 = 1 + Finset.univ.sup childrenH_256 := by decide +kernel
theorem required_origin_256 : ∀ x ∈ required_256,
    (∃ j, x ∈ childrenC_256 j) ∨ ∀ j, x ∈ childrenD_256 j := by decide +kernel
theorem required_exact_256 : required_256 =
    ((Finset.univ.biUnion childrenC_256) ∪ commonEnvelope childrenD_256).erase (3, 4) := by
  exact required_eq_combination childrenC_256 childrenD_256 (3, 4) required_256
    (by decide +kernel) child_required_sub_256 common_sub_256 required_origin_256
theorem envelope_origin_256 : ∀ x ∈ envelope_256,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_256 j := by decide +kernel
theorem envelope_exact_256 : envelope_256 =
    insert (3, 4) (Finset.univ.biUnion childrenD_256) := by
  exact envelope_eq_combination childrenD_256 (3, 4) envelope_256
    pivot_mem_256 child_envelope_sub_256 envelope_origin_256
def checked_256 : CheckedCard where
  required := required_256
  envelope := envelope_256
  height := height_256
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_256
def height_276 : ℕ := 7
def childrenH_276 : Fin 4 → ℕ := ![height_44, height_52, height_155, height_275]
theorem height_exact_276 : height_276 = 1 + Finset.univ.sup childrenH_276 := by decide +kernel
theorem required_origin_276 : ∀ x ∈ required_276,
    (∃ j, x ∈ childrenC_276 j) ∨ ∀ j, x ∈ childrenD_276 j := by decide +kernel
theorem required_exact_276 : required_276 =
    ((Finset.univ.biUnion childrenC_276) ∪ commonEnvelope childrenD_276).erase (2, 4) := by
  exact required_eq_combination childrenC_276 childrenD_276 (2, 4) required_276
    (by decide +kernel) child_required_sub_276 common_sub_276 required_origin_276
theorem envelope_origin_276 : ∀ x ∈ envelope_276,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_276 j := by decide +kernel
theorem envelope_exact_276 : envelope_276 =
    insert (2, 4) (Finset.univ.biUnion childrenD_276) := by
  exact envelope_eq_combination childrenD_276 (2, 4) envelope_276
    pivot_mem_276 child_envelope_sub_276 envelope_origin_276
def checked_276 : CheckedCard where
  required := required_276
  envelope := envelope_276
  height := height_276
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_276
def height_286 : ℕ := 7
def childrenH_286 : Fin 2 → ℕ := ![height_35, height_253]
theorem height_exact_286 : height_286 = 1 + Finset.univ.sup childrenH_286 := by decide +kernel
theorem required_origin_286 : ∀ x ∈ required_286,
    (∃ j, x ∈ childrenC_286 j) ∨ ∀ j, x ∈ childrenD_286 j := by decide +kernel
theorem required_exact_286 : required_286 =
    ((Finset.univ.biUnion childrenC_286) ∪ commonEnvelope childrenD_286).erase (4, 2) := by
  exact required_eq_combination childrenC_286 childrenD_286 (4, 2) required_286
    (by decide +kernel) child_required_sub_286 common_sub_286 required_origin_286
theorem envelope_origin_286 : ∀ x ∈ envelope_286,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_286 j := by decide +kernel
theorem envelope_exact_286 : envelope_286 =
    insert (4, 2) (Finset.univ.biUnion childrenD_286) := by
  exact envelope_eq_combination childrenD_286 (4, 2) envelope_286
    pivot_mem_286 child_envelope_sub_286 envelope_origin_286
def checked_286 : CheckedCard where
  required := required_286
  envelope := envelope_286
  height := height_286
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_286
def height_290 : ℕ := 7
def childrenH_290 : Fin 2 → ℕ := ![height_5, height_203]
theorem height_exact_290 : height_290 = 1 + Finset.univ.sup childrenH_290 := by decide +kernel
theorem required_origin_290 : ∀ x ∈ required_290,
    (∃ j, x ∈ childrenC_290 j) ∨ ∀ j, x ∈ childrenD_290 j := by decide +kernel
theorem required_exact_290 : required_290 =
    ((Finset.univ.biUnion childrenC_290) ∪ commonEnvelope childrenD_290).erase (2, 1) := by
  exact required_eq_combination childrenC_290 childrenD_290 (2, 1) required_290
    (by decide +kernel) child_required_sub_290 common_sub_290 required_origin_290
theorem envelope_origin_290 : ∀ x ∈ envelope_290,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_290 j := by decide +kernel
theorem envelope_exact_290 : envelope_290 =
    insert (2, 1) (Finset.univ.biUnion childrenD_290) := by
  exact envelope_eq_combination childrenD_290 (2, 1) envelope_290
    pivot_mem_290 child_envelope_sub_290 envelope_origin_290
def checked_290 : CheckedCard where
  required := required_290
  envelope := envelope_290
  height := height_290
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_290
def height_295 : ℕ := 7
def childrenH_295 : Fin 2 → ℕ := ![height_34, height_180]
theorem height_exact_295 : height_295 = 1 + Finset.univ.sup childrenH_295 := by decide +kernel
theorem required_origin_295 : ∀ x ∈ required_295,
    (∃ j, x ∈ childrenC_295 j) ∨ ∀ j, x ∈ childrenD_295 j := by decide +kernel
theorem required_exact_295 : required_295 =
    ((Finset.univ.biUnion childrenC_295) ∪ commonEnvelope childrenD_295).erase (3, 1) := by
  exact required_eq_combination childrenC_295 childrenD_295 (3, 1) required_295
    (by decide +kernel) child_required_sub_295 common_sub_295 required_origin_295
theorem envelope_origin_295 : ∀ x ∈ envelope_295,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_295 j := by decide +kernel
theorem envelope_exact_295 : envelope_295 =
    insert (3, 1) (Finset.univ.biUnion childrenD_295) := by
  exact envelope_eq_combination childrenD_295 (3, 1) envelope_295
    pivot_mem_295 child_envelope_sub_295 envelope_origin_295
def checked_295 : CheckedCard where
  required := required_295
  envelope := envelope_295
  height := height_295
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_295
def height_297 : ℕ := 7
def childrenH_297 : Fin 3 → ℕ := ![height_9, height_142, height_162]
theorem height_exact_297 : height_297 = 1 + Finset.univ.sup childrenH_297 := by decide +kernel
theorem required_origin_297 : ∀ x ∈ required_297,
    (∃ j, x ∈ childrenC_297 j) ∨ ∀ j, x ∈ childrenD_297 j := by decide +kernel
theorem required_exact_297 : required_297 =
    ((Finset.univ.biUnion childrenC_297) ∪ commonEnvelope childrenD_297).erase (5, 3) := by
  exact required_eq_combination childrenC_297 childrenD_297 (5, 3) required_297
    (by decide +kernel) child_required_sub_297 common_sub_297 required_origin_297
theorem envelope_origin_297 : ∀ x ∈ envelope_297,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_297 j := by decide +kernel
theorem envelope_exact_297 : envelope_297 =
    insert (5, 3) (Finset.univ.biUnion childrenD_297) := by
  exact envelope_eq_combination childrenD_297 (5, 3) envelope_297
    pivot_mem_297 child_envelope_sub_297 envelope_origin_297
def checked_297 : CheckedCard where
  required := required_297
  envelope := envelope_297
  height := height_297
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_297
def height_298 : ℕ := 7
def childrenH_298 : Fin 3 → ℕ := ![height_7, height_142, height_161]
theorem height_exact_298 : height_298 = 1 + Finset.univ.sup childrenH_298 := by decide +kernel
theorem required_origin_298 : ∀ x ∈ required_298,
    (∃ j, x ∈ childrenC_298 j) ∨ ∀ j, x ∈ childrenD_298 j := by decide +kernel
theorem required_exact_298 : required_298 =
    ((Finset.univ.biUnion childrenC_298) ∪ commonEnvelope childrenD_298).erase (5, 3) := by
  exact required_eq_combination childrenC_298 childrenD_298 (5, 3) required_298
    (by decide +kernel) child_required_sub_298 common_sub_298 required_origin_298
theorem envelope_origin_298 : ∀ x ∈ envelope_298,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_298 j := by decide +kernel
theorem envelope_exact_298 : envelope_298 =
    insert (5, 3) (Finset.univ.biUnion childrenD_298) := by
  exact envelope_eq_combination childrenD_298 (5, 3) envelope_298
    pivot_mem_298 child_envelope_sub_298 envelope_origin_298
def checked_298 : CheckedCard where
  required := required_298
  envelope := envelope_298
  height := height_298
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_298
def height_309 : ℕ := 7
def childrenH_309 : Fin 3 → ℕ := ![height_19, height_19, height_115]
theorem height_exact_309 : height_309 = 1 + Finset.univ.sup childrenH_309 := by decide +kernel
theorem required_origin_309 : ∀ x ∈ required_309,
    (∃ j, x ∈ childrenC_309 j) ∨ ∀ j, x ∈ childrenD_309 j := by decide +kernel
theorem required_exact_309 : required_309 =
    ((Finset.univ.biUnion childrenC_309) ∪ commonEnvelope childrenD_309).erase (4, 3) := by
  exact required_eq_combination childrenC_309 childrenD_309 (4, 3) required_309
    (by decide +kernel) child_required_sub_309 common_sub_309 required_origin_309
theorem envelope_origin_309 : ∀ x ∈ envelope_309,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_309 j := by decide +kernel
theorem envelope_exact_309 : envelope_309 =
    insert (4, 3) (Finset.univ.biUnion childrenD_309) := by
  exact envelope_eq_combination childrenD_309 (4, 3) envelope_309
    pivot_mem_309 child_envelope_sub_309 envelope_origin_309
def checked_309 : CheckedCard where
  required := required_309
  envelope := envelope_309
  height := height_309
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_309
def height_317 : ℕ := 7
def childrenH_317 : Fin 3 → ℕ := ![height_44, height_60, height_316]
theorem height_exact_317 : height_317 = 1 + Finset.univ.sup childrenH_317 := by decide +kernel
theorem required_origin_317 : ∀ x ∈ required_317,
    (∃ j, x ∈ childrenC_317 j) ∨ ∀ j, x ∈ childrenD_317 j := by decide +kernel
theorem required_exact_317 : required_317 =
    ((Finset.univ.biUnion childrenC_317) ∪ commonEnvelope childrenD_317).erase (3, 5) := by
  exact required_eq_combination childrenC_317 childrenD_317 (3, 5) required_317
    (by decide +kernel) child_required_sub_317 common_sub_317 required_origin_317
theorem envelope_origin_317 : ∀ x ∈ envelope_317,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_317 j := by decide +kernel
theorem envelope_exact_317 : envelope_317 =
    insert (3, 5) (Finset.univ.biUnion childrenD_317) := by
  exact envelope_eq_combination childrenD_317 (3, 5) envelope_317
    pivot_mem_317 child_envelope_sub_317 envelope_origin_317
def checked_317 : CheckedCard where
  required := required_317
  envelope := envelope_317
  height := height_317
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_317
def height_318 : ℕ := 7
def childrenH_318 : Fin 4 → ℕ := ![height_10, height_52, height_52, height_315]
theorem height_exact_318 : height_318 = 1 + Finset.univ.sup childrenH_318 := by decide +kernel
theorem required_origin_318 : ∀ x ∈ required_318,
    (∃ j, x ∈ childrenC_318 j) ∨ ∀ j, x ∈ childrenD_318 j := by decide +kernel
theorem required_exact_318 : required_318 =
    ((Finset.univ.biUnion childrenC_318) ∪ commonEnvelope childrenD_318).erase (1, 3) := by
  exact required_eq_combination childrenC_318 childrenD_318 (1, 3) required_318
    (by decide +kernel) child_required_sub_318 common_sub_318 required_origin_318
theorem envelope_origin_318 : ∀ x ∈ envelope_318,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_318 j := by decide +kernel
theorem envelope_exact_318 : envelope_318 =
    insert (1, 3) (Finset.univ.biUnion childrenD_318) := by
  exact envelope_eq_combination childrenD_318 (1, 3) envelope_318
    pivot_mem_318 child_envelope_sub_318 envelope_origin_318
def checked_318 : CheckedCard where
  required := required_318
  envelope := envelope_318
  height := height_318
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_318
def height_320 : ℕ := 7
def childrenH_320 : Fin 2 → ℕ := ![height_5, height_316]
theorem height_exact_320 : height_320 = 1 + Finset.univ.sup childrenH_320 := by decide +kernel
theorem required_origin_320 : ∀ x ∈ required_320,
    (∃ j, x ∈ childrenC_320 j) ∨ ∀ j, x ∈ childrenD_320 j := by decide +kernel
theorem required_exact_320 : required_320 =
    ((Finset.univ.biUnion childrenC_320) ∪ commonEnvelope childrenD_320).erase (3, 5) := by
  exact required_eq_combination childrenC_320 childrenD_320 (3, 5) required_320
    (by decide +kernel) child_required_sub_320 common_sub_320 required_origin_320
theorem envelope_origin_320 : ∀ x ∈ envelope_320,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_320 j := by decide +kernel
theorem envelope_exact_320 : envelope_320 =
    insert (3, 5) (Finset.univ.biUnion childrenD_320) := by
  exact envelope_eq_combination childrenD_320 (3, 5) envelope_320
    pivot_mem_320 child_envelope_sub_320 envelope_origin_320
def checked_320 : CheckedCard where
  required := required_320
  envelope := envelope_320
  height := height_320
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_320
def height_324 : ℕ := 7
def childrenH_324 : Fin 4 → ℕ := ![height_60, height_237, height_307, height_316]
theorem height_exact_324 : height_324 = 1 + Finset.univ.sup childrenH_324 := by decide +kernel
theorem required_origin_324 : ∀ x ∈ required_324,
    (∃ j, x ∈ childrenC_324 j) ∨ ∀ j, x ∈ childrenD_324 j := by decide +kernel
theorem required_exact_324 : required_324 =
    ((Finset.univ.biUnion childrenC_324) ∪ commonEnvelope childrenD_324).erase (1, 3) := by
  exact required_eq_combination childrenC_324 childrenD_324 (1, 3) required_324
    (by decide +kernel) child_required_sub_324 common_sub_324 required_origin_324
theorem envelope_origin_324 : ∀ x ∈ envelope_324,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_324 j := by decide +kernel
theorem envelope_exact_324 : envelope_324 =
    insert (1, 3) (Finset.univ.biUnion childrenD_324) := by
  exact envelope_eq_combination childrenD_324 (1, 3) envelope_324
    pivot_mem_324 child_envelope_sub_324 envelope_origin_324
def checked_324 : CheckedCard where
  required := required_324
  envelope := envelope_324
  height := height_324
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_324
def height_329 : ℕ := 7
def childrenH_329 : Fin 4 → ℕ := ![height_10, height_52, height_52, height_315]
theorem height_exact_329 : height_329 = 1 + Finset.univ.sup childrenH_329 := by decide +kernel
theorem required_origin_329 : ∀ x ∈ required_329,
    (∃ j, x ∈ childrenC_329 j) ∨ ∀ j, x ∈ childrenD_329 j := by decide +kernel
theorem required_exact_329 : required_329 =
    ((Finset.univ.biUnion childrenC_329) ∪ commonEnvelope childrenD_329).erase (1, 4) := by
  exact required_eq_combination childrenC_329 childrenD_329 (1, 4) required_329
    (by decide +kernel) child_required_sub_329 common_sub_329 required_origin_329
theorem envelope_origin_329 : ∀ x ∈ envelope_329,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_329 j := by decide +kernel
theorem envelope_exact_329 : envelope_329 =
    insert (1, 4) (Finset.univ.biUnion childrenD_329) := by
  exact envelope_eq_combination childrenD_329 (1, 4) envelope_329
    pivot_mem_329 child_envelope_sub_329 envelope_origin_329
def checked_329 : CheckedCard where
  required := required_329
  envelope := envelope_329
  height := height_329
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_329
def height_332 : ℕ := 7
def childrenH_332 : Fin 3 → ℕ := ![height_9, height_11, height_331]
theorem height_exact_332 : height_332 = 1 + Finset.univ.sup childrenH_332 := by decide +kernel
theorem required_origin_332 : ∀ x ∈ required_332,
    (∃ j, x ∈ childrenC_332 j) ∨ ∀ j, x ∈ childrenD_332 j := by decide +kernel
theorem required_exact_332 : required_332 =
    ((Finset.univ.biUnion childrenC_332) ∪ commonEnvelope childrenD_332).erase (4, 3) := by
  exact required_eq_combination childrenC_332 childrenD_332 (4, 3) required_332
    (by decide +kernel) child_required_sub_332 common_sub_332 required_origin_332
theorem envelope_origin_332 : ∀ x ∈ envelope_332,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_332 j := by decide +kernel
theorem envelope_exact_332 : envelope_332 =
    insert (4, 3) (Finset.univ.biUnion childrenD_332) := by
  exact envelope_eq_combination childrenD_332 (4, 3) envelope_332
    pivot_mem_332 child_envelope_sub_332 envelope_origin_332
def checked_332 : CheckedCard where
  required := required_332
  envelope := envelope_332
  height := height_332
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_332
def height_337 : ℕ := 7
def childrenH_337 : Fin 3 → ℕ := ![height_7, height_143, height_336]
theorem height_exact_337 : height_337 = 1 + Finset.univ.sup childrenH_337 := by decide +kernel
theorem required_origin_337 : ∀ x ∈ required_337,
    (∃ j, x ∈ childrenC_337 j) ∨ ∀ j, x ∈ childrenD_337 j := by decide +kernel
theorem required_exact_337 : required_337 =
    ((Finset.univ.biUnion childrenC_337) ∪ commonEnvelope childrenD_337).erase (1, 2) := by
  exact required_eq_combination childrenC_337 childrenD_337 (1, 2) required_337
    (by decide +kernel) child_required_sub_337 common_sub_337 required_origin_337
theorem envelope_origin_337 : ∀ x ∈ envelope_337,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_337 j := by decide +kernel
theorem envelope_exact_337 : envelope_337 =
    insert (1, 2) (Finset.univ.biUnion childrenD_337) := by
  exact envelope_eq_combination childrenD_337 (1, 2) envelope_337
    pivot_mem_337 child_envelope_sub_337 envelope_origin_337
def checked_337 : CheckedCard where
  required := required_337
  envelope := envelope_337
  height := height_337
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_337
def height_339 : ℕ := 7
def childrenH_339 : Fin 2 → ℕ := ![height_35, height_336]
theorem height_exact_339 : height_339 = 1 + Finset.univ.sup childrenH_339 := by decide +kernel
theorem required_origin_339 : ∀ x ∈ required_339,
    (∃ j, x ∈ childrenC_339 j) ∨ ∀ j, x ∈ childrenD_339 j := by decide +kernel
theorem required_exact_339 : required_339 =
    ((Finset.univ.biUnion childrenC_339) ∪ commonEnvelope childrenD_339).erase (4, 2) := by
  exact required_eq_combination childrenC_339 childrenD_339 (4, 2) required_339
    (by decide +kernel) child_required_sub_339 common_sub_339 required_origin_339
theorem envelope_origin_339 : ∀ x ∈ envelope_339,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_339 j := by decide +kernel
theorem envelope_exact_339 : envelope_339 =
    insert (4, 2) (Finset.univ.biUnion childrenD_339) := by
  exact envelope_eq_combination childrenD_339 (4, 2) envelope_339
    pivot_mem_339 child_envelope_sub_339 envelope_origin_339
def checked_339 : CheckedCard where
  required := required_339
  envelope := envelope_339
  height := height_339
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_339
def height_341 : ℕ := 7
def childrenH_341 : Fin 3 → ℕ := ![height_53, height_57, height_340]
theorem height_exact_341 : height_341 = 1 + Finset.univ.sup childrenH_341 := by decide +kernel
theorem required_origin_341 : ∀ x ∈ required_341,
    (∃ j, x ∈ childrenC_341 j) ∨ ∀ j, x ∈ childrenD_341 j := by decide +kernel
theorem required_exact_341 : required_341 =
    ((Finset.univ.biUnion childrenC_341) ∪ commonEnvelope childrenD_341).erase (4, 4) := by
  exact required_eq_combination childrenC_341 childrenD_341 (4, 4) required_341
    (by decide +kernel) child_required_sub_341 common_sub_341 required_origin_341
theorem envelope_origin_341 : ∀ x ∈ envelope_341,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_341 j := by decide +kernel
theorem envelope_exact_341 : envelope_341 =
    insert (4, 4) (Finset.univ.biUnion childrenD_341) := by
  exact envelope_eq_combination childrenD_341 (4, 4) envelope_341
    pivot_mem_341 child_envelope_sub_341 envelope_origin_341
def checked_341 : CheckedCard where
  required := required_341
  envelope := envelope_341
  height := height_341
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_341
def height_344 : ℕ := 7
def childrenH_344 : Fin 2 → ℕ := ![height_5, height_343]
theorem height_exact_344 : height_344 = 1 + Finset.univ.sup childrenH_344 := by decide +kernel
theorem required_origin_344 : ∀ x ∈ required_344,
    (∃ j, x ∈ childrenC_344 j) ∨ ∀ j, x ∈ childrenD_344 j := by decide +kernel
theorem required_exact_344 : required_344 =
    ((Finset.univ.biUnion childrenC_344) ∪ commonEnvelope childrenD_344).erase (1, 3) := by
  exact required_eq_combination childrenC_344 childrenD_344 (1, 3) required_344
    (by decide +kernel) child_required_sub_344 common_sub_344 required_origin_344
theorem envelope_origin_344 : ∀ x ∈ envelope_344,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_344 j := by decide +kernel
theorem envelope_exact_344 : envelope_344 =
    insert (1, 3) (Finset.univ.biUnion childrenD_344) := by
  exact envelope_eq_combination childrenD_344 (1, 3) envelope_344
    pivot_mem_344 child_envelope_sub_344 envelope_origin_344
def checked_344 : CheckedCard where
  required := required_344
  envelope := envelope_344
  height := height_344
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_344
def height_353 : ℕ := 7
def childrenH_353 : Fin 2 → ℕ := ![height_95, height_352]
theorem height_exact_353 : height_353 = 1 + Finset.univ.sup childrenH_353 := by decide +kernel
theorem required_origin_353 : ∀ x ∈ required_353,
    (∃ j, x ∈ childrenC_353 j) ∨ ∀ j, x ∈ childrenD_353 j := by decide +kernel
theorem required_exact_353 : required_353 =
    ((Finset.univ.biUnion childrenC_353) ∪ commonEnvelope childrenD_353).erase (4, 6) := by
  exact required_eq_combination childrenC_353 childrenD_353 (4, 6) required_353
    (by decide +kernel) child_required_sub_353 common_sub_353 required_origin_353
theorem envelope_origin_353 : ∀ x ∈ envelope_353,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_353 j := by decide +kernel
theorem envelope_exact_353 : envelope_353 =
    insert (4, 6) (Finset.univ.biUnion childrenD_353) := by
  exact envelope_eq_combination childrenD_353 (4, 6) envelope_353
    pivot_mem_353 child_envelope_sub_353 envelope_origin_353
def checked_353 : CheckedCard where
  required := required_353
  envelope := envelope_353
  height := height_353
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_353
end SnakyPrototype.Certificate21

end OAI
