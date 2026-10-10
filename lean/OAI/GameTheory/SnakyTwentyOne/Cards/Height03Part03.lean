import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_221 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 0), (2, 1), (2, 2), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_221 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (3, 3), (3, 4), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_221 : Fin 2 → Finset Cell := ![(placed21 5 (2, 0) required_5), (placed21 4 (0, 4) required_220)]
def childrenD_221 : Fin 2 → Finset Cell := ![(placed21 5 (2, 0) envelope_5), (placed21 4 (0, 4) envelope_220)]
theorem common_sub_221 : commonEnvelope childrenD_221 ⊆ insert (1, 3) required_221 := by decide +kernel
theorem child_required_sub_221 : ∀ j, childrenC_221 j ⊆ insert (1, 3) required_221 := by decide +kernel
theorem child_envelope_sub_221 : ∀ j, childrenD_221 j ⊆ envelope_221 := by decide +kernel
theorem pivot_mem_221 : (1, 3) ∈ envelope_221 := by decide +kernel
theorem children_work_221 : ∀ j, Template HasSnaky 2 (childrenC_221 j) (childrenD_221 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (2, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_220 4 (0, 4)).mono (by decide +kernel)
theorem row_works_221 : Template HasSnaky 3 required_221 envelope_221 := by
  refine compose HasSnaky 2 childrenC_221 childrenD_221 children_work_221 (1, 3)
    required_221 envelope_221 pivot_mem_221 child_required_sub_221 child_envelope_sub_221 ?_
  intro b hb
  exact common_sub_221 (mem_commonEnvelope childrenD_221 b hb)
def required_222 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (1, 4), (2, 2), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_222 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_222 : Fin 2 → Finset Cell := ![(placed21 5 (2, 1) required_5), required_220]
def childrenD_222 : Fin 2 → Finset Cell := ![(placed21 5 (2, 1) envelope_5), envelope_220]
theorem common_sub_222 : commonEnvelope childrenD_222 ⊆ insert (2, 1) required_222 := by decide +kernel
theorem child_required_sub_222 : ∀ j, childrenC_222 j ⊆ insert (2, 1) required_222 := by decide +kernel
theorem child_envelope_sub_222 : ∀ j, childrenD_222 j ⊆ envelope_222 := by decide +kernel
theorem pivot_mem_222 : (2, 1) ∈ envelope_222 := by decide +kernel
theorem children_work_222 : ∀ j, Template HasSnaky 2 (childrenC_222 j) (childrenD_222 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (2, 1)).mono (by decide +kernel)
  · exact row_works_220.mono (by decide +kernel)
theorem row_works_222 : Template HasSnaky 3 required_222 envelope_222 := by
  refine compose HasSnaky 2 childrenC_222 childrenD_222 children_work_222 (2, 1)
    required_222 envelope_222 pivot_mem_222 child_required_sub_222 child_envelope_sub_222 ?_
  intro b hb
  exact common_sub_222 (mem_commonEnvelope childrenD_222 b hb)
def required_223 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_223 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_223 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) required_5), (placed21 0 (3, 0) required_6)]
def childrenD_223 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) envelope_5), (placed21 0 (3, 0) envelope_6)]
theorem common_sub_223 : commonEnvelope childrenD_223 ⊆ insert (3, 0) required_223 := by decide +kernel
theorem child_required_sub_223 : ∀ j, childrenC_223 j ⊆ insert (3, 0) required_223 := by decide +kernel
theorem child_envelope_sub_223 : ∀ j, childrenD_223 j ⊆ envelope_223 := by decide +kernel
theorem pivot_mem_223 : (3, 0) ∈ envelope_223 := by decide +kernel
theorem children_work_223 : ∀ j, Template HasSnaky 2 (childrenC_223 j) (childrenD_223 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_6 0 (3, 0)).mono (by decide +kernel)
theorem row_works_223 : Template HasSnaky 3 required_223 envelope_223 := by
  refine compose HasSnaky 2 childrenC_223 childrenD_223 children_work_223 (3, 0)
    required_223 envelope_223 pivot_mem_223 child_required_sub_223 child_envelope_sub_223 ?_
  intro b hb
  exact common_sub_223 (mem_commonEnvelope childrenD_223 b hb)
def required_226 : Finset Cell := ⟨(([(0, 2), (1, 1), (2, 1), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_226 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (2, 1), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (5, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_226 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) required_4), (placed21 0 (1, 0) required_32)]
def childrenD_226 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) envelope_4), (placed21 0 (1, 0) envelope_32)]
theorem common_sub_226 : commonEnvelope childrenD_226 ⊆ insert (4, 1) required_226 := by decide +kernel
theorem child_required_sub_226 : ∀ j, childrenC_226 j ⊆ insert (4, 1) required_226 := by decide +kernel
theorem child_envelope_sub_226 : ∀ j, childrenD_226 j ⊆ envelope_226 := by decide +kernel
theorem pivot_mem_226 : (4, 1) ∈ envelope_226 := by decide +kernel
theorem children_work_226 : ∀ j, Template HasSnaky 2 (childrenC_226 j) (childrenD_226 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 2 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_32 0 (1, 0)).mono (by decide +kernel)
theorem row_works_226 : Template HasSnaky 3 required_226 envelope_226 := by
  refine compose HasSnaky 2 childrenC_226 childrenD_226 children_work_226 (4, 1)
    required_226 envelope_226 pivot_mem_226 child_required_sub_226 child_envelope_sub_226 ?_
  intro b hb
  exact common_sub_226 (mem_commonEnvelope childrenD_226 b hb)
def required_236 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (2, 4), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_236 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 4), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_236 : Fin 2 → Finset Cell := ![(placed21 6 (1, 5) required_6), (placed21 1 (0, 2) required_32)]
def childrenD_236 : Fin 2 → Finset Cell := ![(placed21 6 (1, 5) envelope_6), (placed21 1 (0, 2) envelope_32)]
theorem common_sub_236 : commonEnvelope childrenD_236 ⊆ insert (1, 5) required_236 := by decide +kernel
theorem child_required_sub_236 : ∀ j, childrenC_236 j ⊆ insert (1, 5) required_236 := by decide +kernel
theorem child_envelope_sub_236 : ∀ j, childrenD_236 j ⊆ envelope_236 := by decide +kernel
theorem pivot_mem_236 : (1, 5) ∈ envelope_236 := by decide +kernel
theorem children_work_236 : ∀ j, Template HasSnaky 2 (childrenC_236 j) (childrenD_236 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 6 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_32 1 (0, 2)).mono (by decide +kernel)
theorem row_works_236 : Template HasSnaky 3 required_236 envelope_236 := by
  refine compose HasSnaky 2 childrenC_236 childrenD_236 children_work_236 (1, 5)
    required_236 envelope_236 pivot_mem_236 child_required_sub_236 child_envelope_sub_236 ?_
  intro b hb
  exact common_sub_236 (mem_commonEnvelope childrenD_236 b hb)
def required_239 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 3), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_239 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_239 : Fin 2 → Finset Cell := ![(placed21 6 (3, 5) required_11), (placed21 7 (4, 4) required_25)]
def childrenD_239 : Fin 2 → Finset Cell := ![(placed21 6 (3, 5) envelope_11), (placed21 7 (4, 4) envelope_25)]
theorem common_sub_239 : commonEnvelope childrenD_239 ⊆ insert (3, 1) required_239 := by decide +kernel
theorem child_required_sub_239 : ∀ j, childrenC_239 j ⊆ insert (3, 1) required_239 := by decide +kernel
theorem child_envelope_sub_239 : ∀ j, childrenD_239 j ⊆ envelope_239 := by decide +kernel
theorem pivot_mem_239 : (3, 1) ∈ envelope_239 := by decide +kernel
theorem children_work_239 : ∀ j, Template HasSnaky 2 (childrenC_239 j) (childrenD_239 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 6 (3, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_25 7 (4, 4)).mono (by decide +kernel)
theorem row_works_239 : Template HasSnaky 3 required_239 envelope_239 := by
  refine compose HasSnaky 2 childrenC_239 childrenD_239 children_work_239 (3, 1)
    required_239 envelope_239 pivot_mem_239 child_required_sub_239 child_envelope_sub_239 ?_
  intro b hb
  exact common_sub_239 (mem_commonEnvelope childrenD_239 b hb)
def required_245 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (2, 1), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_245 : Finset Cell := ⟨(([(0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_245 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) required_5), (placed21 1 (0, 1) required_32)]
def childrenD_245 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) envelope_5), (placed21 1 (0, 1) envelope_32)]
theorem common_sub_245 : commonEnvelope childrenD_245 ⊆ insert (1, 4) required_245 := by decide +kernel
theorem child_required_sub_245 : ∀ j, childrenC_245 j ⊆ insert (1, 4) required_245 := by decide +kernel
theorem child_envelope_sub_245 : ∀ j, childrenD_245 j ⊆ envelope_245 := by decide +kernel
theorem pivot_mem_245 : (1, 4) ∈ envelope_245 := by decide +kernel
theorem children_work_245 : ∀ j, Template HasSnaky 2 (childrenC_245 j) (childrenD_245 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_32 1 (0, 1)).mono (by decide +kernel)
theorem row_works_245 : Template HasSnaky 3 required_245 envelope_245 := by
  refine compose HasSnaky 2 childrenC_245 childrenD_245 children_work_245 (1, 4)
    required_245 envelope_245 pivot_mem_245 child_required_sub_245 child_envelope_sub_245 ?_
  intro b hb
  exact common_sub_245 (mem_commonEnvelope childrenD_245 b hb)
def required_246 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_246 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_246 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_5), (placed21 1 (0, 1) required_25)]
def childrenD_246 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_5), (placed21 1 (0, 1) envelope_25)]
theorem common_sub_246 : commonEnvelope childrenD_246 ⊆ insert (1, 4) required_246 := by decide +kernel
theorem child_required_sub_246 : ∀ j, childrenC_246 j ⊆ insert (1, 4) required_246 := by decide +kernel
theorem child_envelope_sub_246 : ∀ j, childrenD_246 j ⊆ envelope_246 := by decide +kernel
theorem pivot_mem_246 : (1, 4) ∈ envelope_246 := by decide +kernel
theorem children_work_246 : ∀ j, Template HasSnaky 2 (childrenC_246 j) (childrenD_246 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_25 1 (0, 1)).mono (by decide +kernel)
theorem row_works_246 : Template HasSnaky 3 required_246 envelope_246 := by
  refine compose HasSnaky 2 childrenC_246 childrenD_246 children_work_246 (1, 4)
    required_246 envelope_246 pivot_mem_246 child_required_sub_246 child_envelope_sub_246 ?_
  intro b hb
  exact common_sub_246 (mem_commonEnvelope childrenD_246 b hb)
def required_247 : Finset Cell := ⟨(([(0, 1), (3, 1), (3, 2), (3, 3), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_247 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_247 : Fin 2 → Finset Cell := ![(placed21 0 (3, 0) required_11), (placed21 7 (4, 4) required_35)]
def childrenD_247 : Fin 2 → Finset Cell := ![(placed21 0 (3, 0) envelope_11), (placed21 7 (4, 4) envelope_35)]
theorem common_sub_247 : commonEnvelope childrenD_247 ⊆ insert (3, 4) required_247 := by decide +kernel
theorem child_required_sub_247 : ∀ j, childrenC_247 j ⊆ insert (3, 4) required_247 := by decide +kernel
theorem child_envelope_sub_247 : ∀ j, childrenD_247 j ⊆ envelope_247 := by decide +kernel
theorem pivot_mem_247 : (3, 4) ∈ envelope_247 := by decide +kernel
theorem children_work_247 : ∀ j, Template HasSnaky 2 (childrenC_247 j) (childrenD_247 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 0 (3, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_35 7 (4, 4)).mono (by decide +kernel)
theorem row_works_247 : Template HasSnaky 3 required_247 envelope_247 := by
  refine compose HasSnaky 2 childrenC_247 childrenD_247 children_work_247 (3, 4)
    required_247 envelope_247 pivot_mem_247 child_required_sub_247 child_envelope_sub_247 ?_
  intro b hb
  exact common_sub_247 (mem_commonEnvelope childrenD_247 b hb)
def required_251 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_251 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 0), (3, 1), (3, 2), (4, 1), (4, 2), (4, 3), (4, 4), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_251 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_4), (placed21 0 (1, 0) required_224)]
def childrenD_251 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_4), (placed21 0 (1, 0) envelope_224)]
theorem common_sub_251 : commonEnvelope childrenD_251 ⊆ insert (4, 2) required_251 := by decide +kernel
theorem child_required_sub_251 : ∀ j, childrenC_251 j ⊆ insert (4, 2) required_251 := by decide +kernel
theorem child_envelope_sub_251 : ∀ j, childrenD_251 j ⊆ envelope_251 := by decide +kernel
theorem pivot_mem_251 : (4, 2) ∈ envelope_251 := by decide +kernel
theorem children_work_251 : ∀ j, Template HasSnaky 2 (childrenC_251 j) (childrenD_251 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_224 0 (1, 0)).mono (by decide +kernel)
theorem row_works_251 : Template HasSnaky 3 required_251 envelope_251 := by
  refine compose HasSnaky 2 childrenC_251 childrenD_251 children_work_251 (4, 2)
    required_251 envelope_251 pivot_mem_251 child_required_sub_251 child_envelope_sub_251 ?_
  intro b hb
  exact common_sub_251 (mem_commonEnvelope childrenD_251 b hb)
def required_261 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_261 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_261 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) required_3), required_129]
def childrenD_261 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) envelope_3), envelope_129]
theorem common_sub_261 : commonEnvelope childrenD_261 ⊆ insert (1, 3) required_261 := by decide +kernel
theorem child_required_sub_261 : ∀ j, childrenC_261 j ⊆ insert (1, 3) required_261 := by decide +kernel
theorem child_envelope_sub_261 : ∀ j, childrenD_261 j ⊆ envelope_261 := by decide +kernel
theorem pivot_mem_261 : (1, 3) ∈ envelope_261 := by decide +kernel
theorem children_work_261 : ∀ j, Template HasSnaky 2 (childrenC_261 j) (childrenD_261 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 1 (0, 0)).mono (by decide +kernel)
  · exact row_works_129.mono (by decide +kernel)
theorem row_works_261 : Template HasSnaky 3 required_261 envelope_261 := by
  refine compose HasSnaky 2 childrenC_261 childrenD_261 children_work_261 (1, 3)
    required_261 envelope_261 pivot_mem_261 child_required_sub_261 child_envelope_sub_261 ?_
  intro b hb
  exact common_sub_261 (mem_commonEnvelope childrenD_261 b hb)
def required_262 : Finset Cell := ⟨(([(1, 2), (1, 3), (2, 2), (2, 3), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_262 : Finset Cell := ⟨(([(0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4), (2, 5), (3, 2), (4, 2), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_262 : Fin 2 → Finset Cell := ![(placed21 0 (1, 0) required_15), (placed21 3 (0, 3) required_66)]
def childrenD_262 : Fin 2 → Finset Cell := ![(placed21 0 (1, 0) envelope_15), (placed21 3 (0, 3) envelope_66)]
theorem common_sub_262 : commonEnvelope childrenD_262 ⊆ insert (1, 1) required_262 := by decide +kernel
theorem child_required_sub_262 : ∀ j, childrenC_262 j ⊆ insert (1, 1) required_262 := by decide +kernel
theorem child_envelope_sub_262 : ∀ j, childrenD_262 j ⊆ envelope_262 := by decide +kernel
theorem pivot_mem_262 : (1, 1) ∈ envelope_262 := by decide +kernel
theorem children_work_262 : ∀ j, Template HasSnaky 2 (childrenC_262 j) (childrenD_262 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_15 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_66 3 (0, 3)).mono (by decide +kernel)
theorem row_works_262 : Template HasSnaky 3 required_262 envelope_262 := by
  refine compose HasSnaky 2 childrenC_262 childrenD_262 children_work_262 (1, 1)
    required_262 envelope_262 pivot_mem_262 child_required_sub_262 child_envelope_sub_262 ?_
  intro b hb
  exact common_sub_262 (mem_commonEnvelope childrenD_262 b hb)
def required_280 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 3), (1, 4), (1, 5), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_280 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 5), (2, 6), (2, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_280 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_3), (placed21 0 (1, 2) required_6)]
def childrenD_280 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_3), (placed21 0 (1, 2) envelope_6)]
theorem common_sub_280 : commonEnvelope childrenD_280 ⊆ insert (1, 2) required_280 := by decide +kernel
theorem child_required_sub_280 : ∀ j, childrenC_280 j ⊆ insert (1, 2) required_280 := by decide +kernel
theorem child_envelope_sub_280 : ∀ j, childrenD_280 j ⊆ envelope_280 := by decide +kernel
theorem pivot_mem_280 : (1, 2) ∈ envelope_280 := by decide +kernel
theorem children_work_280 : ∀ j, Template HasSnaky 2 (childrenC_280 j) (childrenD_280 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_6 0 (1, 2)).mono (by decide +kernel)
theorem row_works_280 : Template HasSnaky 3 required_280 envelope_280 := by
  refine compose HasSnaky 2 childrenC_280 childrenD_280 children_work_280 (1, 2)
    required_280 envelope_280 pivot_mem_280 child_required_sub_280 child_envelope_sub_280 ?_
  intro b hb
  exact common_sub_280 (mem_commonEnvelope childrenD_280 b hb)
def required_310 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 4), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_310 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_310 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_5), (placed21 0 (0, 1) required_76)]
def childrenD_310 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_5), (placed21 0 (0, 1) envelope_76)]
theorem common_sub_310 : commonEnvelope childrenD_310 ⊆ insert (1, 3) required_310 := by decide +kernel
theorem child_required_sub_310 : ∀ j, childrenC_310 j ⊆ insert (1, 3) required_310 := by decide +kernel
theorem child_envelope_sub_310 : ∀ j, childrenD_310 j ⊆ envelope_310 := by decide +kernel
theorem pivot_mem_310 : (1, 3) ∈ envelope_310 := by decide +kernel
theorem children_work_310 : ∀ j, Template HasSnaky 2 (childrenC_310 j) (childrenD_310 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_76 0 (0, 1)).mono (by decide +kernel)
theorem row_works_310 : Template HasSnaky 3 required_310 envelope_310 := by
  refine compose HasSnaky 2 childrenC_310 childrenD_310 children_work_310 (1, 3)
    required_310 envelope_310 pivot_mem_310 child_required_sub_310 child_envelope_sub_310 ?_
  intro b hb
  exact common_sub_310 (mem_commonEnvelope childrenD_310 b hb)
def required_333_i0 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_333_i0 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_333_i0 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) required_0), (placed21 1 (0, 0) required_3)]
def childrenD_333_i0 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) envelope_0), (placed21 1 (0, 0) envelope_3)]
theorem common_sub_333_i0 : commonEnvelope childrenD_333_i0 ⊆ insert (0, 2) required_333_i0 := by decide +kernel
theorem child_required_sub_333_i0 : ∀ j, childrenC_333_i0 j ⊆ insert (0, 2) required_333_i0 := by decide +kernel
theorem child_envelope_sub_333_i0 : ∀ j, childrenD_333_i0 j ⊆ envelope_333_i0 := by decide +kernel
theorem pivot_mem_333_i0 : (0, 2) ∈ envelope_333_i0 := by decide +kernel
theorem children_work_333_i0 : ∀ j, Template HasSnaky 1 (childrenC_333_i0 j) (childrenD_333_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_3 1 (0, 0)).mono (by decide +kernel)
theorem row_works_333_i0 : Template HasSnaky 2 required_333_i0 envelope_333_i0 := by
  refine compose HasSnaky 1 childrenC_333_i0 childrenD_333_i0 children_work_333_i0 (0, 2)
    required_333_i0 envelope_333_i0 pivot_mem_333_i0 child_required_sub_333_i0 child_envelope_sub_333_i0 ?_
  intro b hb
  exact common_sub_333_i0 (mem_commonEnvelope childrenD_333_i0 b hb)
def required_333 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_333 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_333 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_3), required_333_i0]
def childrenD_333 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_3), envelope_333_i0]
theorem common_sub_333 : commonEnvelope childrenD_333 ⊆ insert (1, 4) required_333 := by decide +kernel
theorem child_required_sub_333 : ∀ j, childrenC_333 j ⊆ insert (1, 4) required_333 := by decide +kernel
theorem child_envelope_sub_333 : ∀ j, childrenD_333 j ⊆ envelope_333 := by decide +kernel
theorem pivot_mem_333 : (1, 4) ∈ envelope_333 := by decide +kernel
theorem children_work_333 : ∀ j, Template HasSnaky 2 (childrenC_333 j) (childrenD_333 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 7 (1, 4)).mono (by decide +kernel)
  · exact row_works_333_i0.mono (by decide +kernel)
theorem row_works_333 : Template HasSnaky 3 required_333 envelope_333 := by
  refine compose HasSnaky 2 childrenC_333 childrenD_333 children_work_333 (1, 4)
    required_333 envelope_333 pivot_mem_333 child_required_sub_333 child_envelope_sub_333 ?_
  intro b hb
  exact common_sub_333 (mem_commonEnvelope childrenD_333 b hb)
def required_350_i0 : Finset Cell := ⟨(([(1, 1), (2, 1), (3, 1), (3, 2), (3, 4), (4, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_350_i0 : Finset Cell := ⟨(([(1, 1), (2, 1), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (5, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_350_i0 : Fin 2 → Finset Cell := ![(placed21 3 (3, 4) required_1), (placed21 4 (1, 1) required_5)]
def childrenD_350_i0 : Fin 2 → Finset Cell := ![(placed21 3 (3, 4) envelope_1), (placed21 4 (1, 1) envelope_5)]
theorem common_sub_350_i0 : commonEnvelope childrenD_350_i0 ⊆ insert (4, 1) required_350_i0 := by decide +kernel
theorem child_required_sub_350_i0 : ∀ j, childrenC_350_i0 j ⊆ insert (4, 1) required_350_i0 := by decide +kernel
theorem child_envelope_sub_350_i0 : ∀ j, childrenD_350_i0 j ⊆ envelope_350_i0 := by decide +kernel
theorem pivot_mem_350_i0 : (4, 1) ∈ envelope_350_i0 := by decide +kernel
theorem children_work_350_i0 : ∀ j, Template HasSnaky 1 (childrenC_350_i0 j) (childrenD_350_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 3 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 4 (1, 1)).mono (by decide +kernel)
theorem row_works_350_i0 : Template HasSnaky 2 required_350_i0 envelope_350_i0 := by
  refine compose HasSnaky 1 childrenC_350_i0 childrenD_350_i0 children_work_350_i0 (4, 1)
    required_350_i0 envelope_350_i0 pivot_mem_350_i0 child_required_sub_350_i0 child_envelope_sub_350_i0 ?_
  intro b hb
  exact common_sub_350_i0 (mem_commonEnvelope childrenD_350_i0 b hb)
def required_350 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1), (3, 2), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_350 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (5, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_350 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) required_4), required_350_i0]
def childrenD_350 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) envelope_4), envelope_350_i0]
theorem common_sub_350 : commonEnvelope childrenD_350 ⊆ insert (4, 0) required_350 := by decide +kernel
theorem child_required_sub_350 : ∀ j, childrenC_350 j ⊆ insert (4, 0) required_350 := by decide +kernel
theorem child_envelope_sub_350 : ∀ j, childrenD_350 j ⊆ envelope_350 := by decide +kernel
theorem pivot_mem_350 : (4, 0) ∈ envelope_350 := by decide +kernel
theorem children_work_350 : ∀ j, Template HasSnaky 2 (childrenC_350 j) (childrenD_350 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 4 (0, 1)).mono (by decide +kernel)
  · exact row_works_350_i0.mono (by decide +kernel)
theorem row_works_350 : Template HasSnaky 3 required_350 envelope_350 := by
  refine compose HasSnaky 2 childrenC_350 childrenD_350 children_work_350 (4, 0)
    required_350 envelope_350 pivot_mem_350 child_required_sub_350 child_envelope_sub_350 ?_
  intro b hb
  exact common_sub_350 (mem_commonEnvelope childrenD_350 b hb)
def required_374_i0 : Finset Cell := ⟨(([(1, 1), (2, 1), (3, 0), (3, 1), (4, 2), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_374_i0 : Finset Cell := ⟨(([(1, 1), (2, 1), (3, 0), (3, 1), (4, 1), (4, 2), (4, 3), (4, 4), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_374_i0 : Fin 2 → Finset Cell := ![(placed21 7 (4, 4) required_1), (placed21 0 (1, 1) required_5)]
def childrenD_374_i0 : Fin 2 → Finset Cell := ![(placed21 7 (4, 4) envelope_1), (placed21 0 (1, 1) envelope_5)]
theorem common_sub_374_i0 : commonEnvelope childrenD_374_i0 ⊆ insert (4, 1) required_374_i0 := by decide +kernel
theorem child_required_sub_374_i0 : ∀ j, childrenC_374_i0 j ⊆ insert (4, 1) required_374_i0 := by decide +kernel
theorem child_envelope_sub_374_i0 : ∀ j, childrenD_374_i0 j ⊆ envelope_374_i0 := by decide +kernel
theorem pivot_mem_374_i0 : (4, 1) ∈ envelope_374_i0 := by decide +kernel
theorem children_work_374_i0 : ∀ j, Template HasSnaky 1 (childrenC_374_i0 j) (childrenD_374_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 7 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 0 (1, 1)).mono (by decide +kernel)
theorem row_works_374_i0 : Template HasSnaky 2 required_374_i0 envelope_374_i0 := by
  refine compose HasSnaky 1 childrenC_374_i0 childrenD_374_i0 children_work_374_i0 (4, 1)
    required_374_i0 envelope_374_i0 pivot_mem_374_i0 child_required_sub_374_i0 child_envelope_sub_374_i0 ?_
  intro b hb
  exact common_sub_374_i0 (mem_commonEnvelope childrenD_374_i0 b hb)
def required_374 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 0), (3, 1), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_374 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 0), (3, 1), (3, 2), (4, 1), (4, 2), (4, 3), (4, 4), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_374 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_4), required_374_i0]
def childrenD_374 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_4), envelope_374_i0]
theorem common_sub_374 : commonEnvelope childrenD_374 ⊆ insert (4, 2) required_374 := by decide +kernel
theorem child_required_sub_374 : ∀ j, childrenC_374 j ⊆ insert (4, 2) required_374 := by decide +kernel
theorem child_envelope_sub_374 : ∀ j, childrenD_374 j ⊆ envelope_374 := by decide +kernel
theorem pivot_mem_374 : (4, 2) ∈ envelope_374 := by decide +kernel
theorem children_work_374 : ∀ j, Template HasSnaky 2 (childrenC_374 j) (childrenD_374 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_374_i0.mono (by decide +kernel)
theorem row_works_374 : Template HasSnaky 3 required_374 envelope_374 := by
  refine compose HasSnaky 2 childrenC_374 childrenD_374 children_work_374 (4, 2)
    required_374 envelope_374 pivot_mem_374 child_required_sub_374 child_envelope_sub_374 ?_
  intro b hb
  exact common_sub_374 (mem_commonEnvelope childrenD_374 b hb)
def required_402_i0 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (2, 3), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_402_i0 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_402_i0 : Fin 2 → Finset Cell := ![(placed21 5 (3, 0) required_0), (placed21 1 (1, 1) required_5)]
def childrenD_402_i0 : Fin 2 → Finset Cell := ![(placed21 5 (3, 0) envelope_0), (placed21 1 (1, 1) envelope_5)]
theorem common_sub_402_i0 : commonEnvelope childrenD_402_i0 ⊆ insert (2, 4) required_402_i0 := by decide +kernel
theorem child_required_sub_402_i0 : ∀ j, childrenC_402_i0 j ⊆ insert (2, 4) required_402_i0 := by decide +kernel
theorem child_envelope_sub_402_i0 : ∀ j, childrenD_402_i0 j ⊆ envelope_402_i0 := by decide +kernel
theorem pivot_mem_402_i0 : (2, 4) ∈ envelope_402_i0 := by decide +kernel
theorem children_work_402_i0 : ∀ j, Template HasSnaky 1 (childrenC_402_i0 j) (childrenD_402_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 5 (3, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 1 (1, 1)).mono (by decide +kernel)
theorem row_works_402_i0 : Template HasSnaky 2 required_402_i0 envelope_402_i0 := by
  refine compose HasSnaky 1 childrenC_402_i0 childrenD_402_i0 children_work_402_i0 (2, 4)
    required_402_i0 envelope_402_i0 pivot_mem_402_i0 child_required_sub_402_i0 child_envelope_sub_402_i0 ?_
  intro b hb
  exact common_sub_402_i0 (mem_commonEnvelope childrenD_402_i0 b hb)
def required_402 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (2, 3), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_402 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_402 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) required_38), required_402_i0]
def childrenD_402 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) envelope_38), envelope_402_i0]
theorem common_sub_402 : commonEnvelope childrenD_402 ⊆ insert (3, 1) required_402 := by decide +kernel
theorem child_required_sub_402 : ∀ j, childrenC_402 j ⊆ insert (3, 1) required_402 := by decide +kernel
theorem child_envelope_sub_402 : ∀ j, childrenD_402 j ⊆ envelope_402 := by decide +kernel
theorem pivot_mem_402 : (3, 1) ∈ envelope_402 := by decide +kernel
theorem children_work_402 : ∀ j, Template HasSnaky 2 (childrenC_402 j) (childrenD_402 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_38 3 (0, 4)).mono (by decide +kernel)
  · exact row_works_402_i0.mono (by decide +kernel)
theorem row_works_402 : Template HasSnaky 3 required_402 envelope_402 := by
  refine compose HasSnaky 2 childrenC_402 childrenD_402 children_work_402 (3, 1)
    required_402 envelope_402 pivot_mem_402 child_required_sub_402 child_envelope_sub_402 ?_
  intro b hb
  exact common_sub_402 (mem_commonEnvelope childrenD_402 b hb)
def height_221 : ℕ := 3
def childrenH_221 : Fin 2 → ℕ := ![height_5, height_220]
theorem height_exact_221 : height_221 = 1 + Finset.univ.sup childrenH_221 := by decide +kernel
theorem required_origin_221 : ∀ x ∈ required_221,
    (∃ j, x ∈ childrenC_221 j) ∨ ∀ j, x ∈ childrenD_221 j := by decide +kernel
theorem required_exact_221 : required_221 =
    ((Finset.univ.biUnion childrenC_221) ∪ commonEnvelope childrenD_221).erase (1, 3) := by
  exact required_eq_combination childrenC_221 childrenD_221 (1, 3) required_221
    (by decide +kernel) child_required_sub_221 common_sub_221 required_origin_221
theorem envelope_origin_221 : ∀ x ∈ envelope_221,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_221 j := by decide +kernel
theorem envelope_exact_221 : envelope_221 =
    insert (1, 3) (Finset.univ.biUnion childrenD_221) := by
  exact envelope_eq_combination childrenD_221 (1, 3) envelope_221
    pivot_mem_221 child_envelope_sub_221 envelope_origin_221
def checked_221 : CheckedCard where
  required := required_221
  envelope := envelope_221
  height := height_221
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_221
def height_222 : ℕ := 3
def childrenH_222 : Fin 2 → ℕ := ![height_5, height_220]
theorem height_exact_222 : height_222 = 1 + Finset.univ.sup childrenH_222 := by decide +kernel
theorem required_origin_222 : ∀ x ∈ required_222,
    (∃ j, x ∈ childrenC_222 j) ∨ ∀ j, x ∈ childrenD_222 j := by decide +kernel
theorem required_exact_222 : required_222 =
    ((Finset.univ.biUnion childrenC_222) ∪ commonEnvelope childrenD_222).erase (2, 1) := by
  exact required_eq_combination childrenC_222 childrenD_222 (2, 1) required_222
    (by decide +kernel) child_required_sub_222 common_sub_222 required_origin_222
theorem envelope_origin_222 : ∀ x ∈ envelope_222,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_222 j := by decide +kernel
theorem envelope_exact_222 : envelope_222 =
    insert (2, 1) (Finset.univ.biUnion childrenD_222) := by
  exact envelope_eq_combination childrenD_222 (2, 1) envelope_222
    pivot_mem_222 child_envelope_sub_222 envelope_origin_222
def checked_222 : CheckedCard where
  required := required_222
  envelope := envelope_222
  height := height_222
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_222
def height_223 : ℕ := 3
def childrenH_223 : Fin 2 → ℕ := ![height_5, height_6]
theorem height_exact_223 : height_223 = 1 + Finset.univ.sup childrenH_223 := by decide +kernel
theorem required_origin_223 : ∀ x ∈ required_223,
    (∃ j, x ∈ childrenC_223 j) ∨ ∀ j, x ∈ childrenD_223 j := by decide +kernel
theorem required_exact_223 : required_223 =
    ((Finset.univ.biUnion childrenC_223) ∪ commonEnvelope childrenD_223).erase (3, 0) := by
  exact required_eq_combination childrenC_223 childrenD_223 (3, 0) required_223
    (by decide +kernel) child_required_sub_223 common_sub_223 required_origin_223
theorem envelope_origin_223 : ∀ x ∈ envelope_223,
    x = (3, 0) ∨ ∃ j, x ∈ childrenD_223 j := by decide +kernel
theorem envelope_exact_223 : envelope_223 =
    insert (3, 0) (Finset.univ.biUnion childrenD_223) := by
  exact envelope_eq_combination childrenD_223 (3, 0) envelope_223
    pivot_mem_223 child_envelope_sub_223 envelope_origin_223
def checked_223 : CheckedCard where
  required := required_223
  envelope := envelope_223
  height := height_223
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_223
def height_226 : ℕ := 3
def childrenH_226 : Fin 2 → ℕ := ![height_4, height_32]
theorem height_exact_226 : height_226 = 1 + Finset.univ.sup childrenH_226 := by decide +kernel
theorem required_origin_226 : ∀ x ∈ required_226,
    (∃ j, x ∈ childrenC_226 j) ∨ ∀ j, x ∈ childrenD_226 j := by decide +kernel
theorem required_exact_226 : required_226 =
    ((Finset.univ.biUnion childrenC_226) ∪ commonEnvelope childrenD_226).erase (4, 1) := by
  exact required_eq_combination childrenC_226 childrenD_226 (4, 1) required_226
    (by decide +kernel) child_required_sub_226 common_sub_226 required_origin_226
theorem envelope_origin_226 : ∀ x ∈ envelope_226,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_226 j := by decide +kernel
theorem envelope_exact_226 : envelope_226 =
    insert (4, 1) (Finset.univ.biUnion childrenD_226) := by
  exact envelope_eq_combination childrenD_226 (4, 1) envelope_226
    pivot_mem_226 child_envelope_sub_226 envelope_origin_226
def checked_226 : CheckedCard where
  required := required_226
  envelope := envelope_226
  height := height_226
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_226
def height_236 : ℕ := 3
def childrenH_236 : Fin 2 → ℕ := ![height_6, height_32]
theorem height_exact_236 : height_236 = 1 + Finset.univ.sup childrenH_236 := by decide +kernel
theorem required_origin_236 : ∀ x ∈ required_236,
    (∃ j, x ∈ childrenC_236 j) ∨ ∀ j, x ∈ childrenD_236 j := by decide +kernel
theorem required_exact_236 : required_236 =
    ((Finset.univ.biUnion childrenC_236) ∪ commonEnvelope childrenD_236).erase (1, 5) := by
  exact required_eq_combination childrenC_236 childrenD_236 (1, 5) required_236
    (by decide +kernel) child_required_sub_236 common_sub_236 required_origin_236
theorem envelope_origin_236 : ∀ x ∈ envelope_236,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_236 j := by decide +kernel
theorem envelope_exact_236 : envelope_236 =
    insert (1, 5) (Finset.univ.biUnion childrenD_236) := by
  exact envelope_eq_combination childrenD_236 (1, 5) envelope_236
    pivot_mem_236 child_envelope_sub_236 envelope_origin_236
def checked_236 : CheckedCard where
  required := required_236
  envelope := envelope_236
  height := height_236
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_236
def height_239 : ℕ := 3
def childrenH_239 : Fin 2 → ℕ := ![height_11, height_25]
theorem height_exact_239 : height_239 = 1 + Finset.univ.sup childrenH_239 := by decide +kernel
theorem required_origin_239 : ∀ x ∈ required_239,
    (∃ j, x ∈ childrenC_239 j) ∨ ∀ j, x ∈ childrenD_239 j := by decide +kernel
theorem required_exact_239 : required_239 =
    ((Finset.univ.biUnion childrenC_239) ∪ commonEnvelope childrenD_239).erase (3, 1) := by
  exact required_eq_combination childrenC_239 childrenD_239 (3, 1) required_239
    (by decide +kernel) child_required_sub_239 common_sub_239 required_origin_239
theorem envelope_origin_239 : ∀ x ∈ envelope_239,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_239 j := by decide +kernel
theorem envelope_exact_239 : envelope_239 =
    insert (3, 1) (Finset.univ.biUnion childrenD_239) := by
  exact envelope_eq_combination childrenD_239 (3, 1) envelope_239
    pivot_mem_239 child_envelope_sub_239 envelope_origin_239
def checked_239 : CheckedCard where
  required := required_239
  envelope := envelope_239
  height := height_239
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_239
def height_245 : ℕ := 3
def childrenH_245 : Fin 2 → ℕ := ![height_5, height_32]
theorem height_exact_245 : height_245 = 1 + Finset.univ.sup childrenH_245 := by decide +kernel
theorem required_origin_245 : ∀ x ∈ required_245,
    (∃ j, x ∈ childrenC_245 j) ∨ ∀ j, x ∈ childrenD_245 j := by decide +kernel
theorem required_exact_245 : required_245 =
    ((Finset.univ.biUnion childrenC_245) ∪ commonEnvelope childrenD_245).erase (1, 4) := by
  exact required_eq_combination childrenC_245 childrenD_245 (1, 4) required_245
    (by decide +kernel) child_required_sub_245 common_sub_245 required_origin_245
theorem envelope_origin_245 : ∀ x ∈ envelope_245,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_245 j := by decide +kernel
theorem envelope_exact_245 : envelope_245 =
    insert (1, 4) (Finset.univ.biUnion childrenD_245) := by
  exact envelope_eq_combination childrenD_245 (1, 4) envelope_245
    pivot_mem_245 child_envelope_sub_245 envelope_origin_245
def checked_245 : CheckedCard where
  required := required_245
  envelope := envelope_245
  height := height_245
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_245
def height_246 : ℕ := 3
def childrenH_246 : Fin 2 → ℕ := ![height_5, height_25]
theorem height_exact_246 : height_246 = 1 + Finset.univ.sup childrenH_246 := by decide +kernel
theorem required_origin_246 : ∀ x ∈ required_246,
    (∃ j, x ∈ childrenC_246 j) ∨ ∀ j, x ∈ childrenD_246 j := by decide +kernel
theorem required_exact_246 : required_246 =
    ((Finset.univ.biUnion childrenC_246) ∪ commonEnvelope childrenD_246).erase (1, 4) := by
  exact required_eq_combination childrenC_246 childrenD_246 (1, 4) required_246
    (by decide +kernel) child_required_sub_246 common_sub_246 required_origin_246
theorem envelope_origin_246 : ∀ x ∈ envelope_246,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_246 j := by decide +kernel
theorem envelope_exact_246 : envelope_246 =
    insert (1, 4) (Finset.univ.biUnion childrenD_246) := by
  exact envelope_eq_combination childrenD_246 (1, 4) envelope_246
    pivot_mem_246 child_envelope_sub_246 envelope_origin_246
def checked_246 : CheckedCard where
  required := required_246
  envelope := envelope_246
  height := height_246
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_246
def height_247 : ℕ := 3
def childrenH_247 : Fin 2 → ℕ := ![height_11, height_35]
theorem height_exact_247 : height_247 = 1 + Finset.univ.sup childrenH_247 := by decide +kernel
theorem required_origin_247 : ∀ x ∈ required_247,
    (∃ j, x ∈ childrenC_247 j) ∨ ∀ j, x ∈ childrenD_247 j := by decide +kernel
theorem required_exact_247 : required_247 =
    ((Finset.univ.biUnion childrenC_247) ∪ commonEnvelope childrenD_247).erase (3, 4) := by
  exact required_eq_combination childrenC_247 childrenD_247 (3, 4) required_247
    (by decide +kernel) child_required_sub_247 common_sub_247 required_origin_247
theorem envelope_origin_247 : ∀ x ∈ envelope_247,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_247 j := by decide +kernel
theorem envelope_exact_247 : envelope_247 =
    insert (3, 4) (Finset.univ.biUnion childrenD_247) := by
  exact envelope_eq_combination childrenD_247 (3, 4) envelope_247
    pivot_mem_247 child_envelope_sub_247 envelope_origin_247
def checked_247 : CheckedCard where
  required := required_247
  envelope := envelope_247
  height := height_247
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_247
def height_251 : ℕ := 3
def childrenH_251 : Fin 2 → ℕ := ![height_4, height_224]
theorem height_exact_251 : height_251 = 1 + Finset.univ.sup childrenH_251 := by decide +kernel
theorem required_origin_251 : ∀ x ∈ required_251,
    (∃ j, x ∈ childrenC_251 j) ∨ ∀ j, x ∈ childrenD_251 j := by decide +kernel
theorem required_exact_251 : required_251 =
    ((Finset.univ.biUnion childrenC_251) ∪ commonEnvelope childrenD_251).erase (4, 2) := by
  exact required_eq_combination childrenC_251 childrenD_251 (4, 2) required_251
    (by decide +kernel) child_required_sub_251 common_sub_251 required_origin_251
theorem envelope_origin_251 : ∀ x ∈ envelope_251,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_251 j := by decide +kernel
theorem envelope_exact_251 : envelope_251 =
    insert (4, 2) (Finset.univ.biUnion childrenD_251) := by
  exact envelope_eq_combination childrenD_251 (4, 2) envelope_251
    pivot_mem_251 child_envelope_sub_251 envelope_origin_251
def checked_251 : CheckedCard where
  required := required_251
  envelope := envelope_251
  height := height_251
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_251
def height_261 : ℕ := 3
def childrenH_261 : Fin 2 → ℕ := ![height_3, height_129]
theorem height_exact_261 : height_261 = 1 + Finset.univ.sup childrenH_261 := by decide +kernel
theorem required_origin_261 : ∀ x ∈ required_261,
    (∃ j, x ∈ childrenC_261 j) ∨ ∀ j, x ∈ childrenD_261 j := by decide +kernel
theorem required_exact_261 : required_261 =
    ((Finset.univ.biUnion childrenC_261) ∪ commonEnvelope childrenD_261).erase (1, 3) := by
  exact required_eq_combination childrenC_261 childrenD_261 (1, 3) required_261
    (by decide +kernel) child_required_sub_261 common_sub_261 required_origin_261
theorem envelope_origin_261 : ∀ x ∈ envelope_261,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_261 j := by decide +kernel
theorem envelope_exact_261 : envelope_261 =
    insert (1, 3) (Finset.univ.biUnion childrenD_261) := by
  exact envelope_eq_combination childrenD_261 (1, 3) envelope_261
    pivot_mem_261 child_envelope_sub_261 envelope_origin_261
def checked_261 : CheckedCard where
  required := required_261
  envelope := envelope_261
  height := height_261
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_261
def height_262 : ℕ := 3
def childrenH_262 : Fin 2 → ℕ := ![height_15, height_66]
theorem height_exact_262 : height_262 = 1 + Finset.univ.sup childrenH_262 := by decide +kernel
theorem required_origin_262 : ∀ x ∈ required_262,
    (∃ j, x ∈ childrenC_262 j) ∨ ∀ j, x ∈ childrenD_262 j := by decide +kernel
theorem required_exact_262 : required_262 =
    ((Finset.univ.biUnion childrenC_262) ∪ commonEnvelope childrenD_262).erase (1, 1) := by
  exact required_eq_combination childrenC_262 childrenD_262 (1, 1) required_262
    (by decide +kernel) child_required_sub_262 common_sub_262 required_origin_262
theorem envelope_origin_262 : ∀ x ∈ envelope_262,
    x = (1, 1) ∨ ∃ j, x ∈ childrenD_262 j := by decide +kernel
theorem envelope_exact_262 : envelope_262 =
    insert (1, 1) (Finset.univ.biUnion childrenD_262) := by
  exact envelope_eq_combination childrenD_262 (1, 1) envelope_262
    pivot_mem_262 child_envelope_sub_262 envelope_origin_262
def checked_262 : CheckedCard where
  required := required_262
  envelope := envelope_262
  height := height_262
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_262
def height_280 : ℕ := 3
def childrenH_280 : Fin 2 → ℕ := ![height_3, height_6]
theorem height_exact_280 : height_280 = 1 + Finset.univ.sup childrenH_280 := by decide +kernel
theorem required_origin_280 : ∀ x ∈ required_280,
    (∃ j, x ∈ childrenC_280 j) ∨ ∀ j, x ∈ childrenD_280 j := by decide +kernel
theorem required_exact_280 : required_280 =
    ((Finset.univ.biUnion childrenC_280) ∪ commonEnvelope childrenD_280).erase (1, 2) := by
  exact required_eq_combination childrenC_280 childrenD_280 (1, 2) required_280
    (by decide +kernel) child_required_sub_280 common_sub_280 required_origin_280
theorem envelope_origin_280 : ∀ x ∈ envelope_280,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_280 j := by decide +kernel
theorem envelope_exact_280 : envelope_280 =
    insert (1, 2) (Finset.univ.biUnion childrenD_280) := by
  exact envelope_eq_combination childrenD_280 (1, 2) envelope_280
    pivot_mem_280 child_envelope_sub_280 envelope_origin_280
def checked_280 : CheckedCard where
  required := required_280
  envelope := envelope_280
  height := height_280
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_280
def height_310 : ℕ := 3
def childrenH_310 : Fin 2 → ℕ := ![height_5, height_76]
theorem height_exact_310 : height_310 = 1 + Finset.univ.sup childrenH_310 := by decide +kernel
theorem required_origin_310 : ∀ x ∈ required_310,
    (∃ j, x ∈ childrenC_310 j) ∨ ∀ j, x ∈ childrenD_310 j := by decide +kernel
theorem required_exact_310 : required_310 =
    ((Finset.univ.biUnion childrenC_310) ∪ commonEnvelope childrenD_310).erase (1, 3) := by
  exact required_eq_combination childrenC_310 childrenD_310 (1, 3) required_310
    (by decide +kernel) child_required_sub_310 common_sub_310 required_origin_310
theorem envelope_origin_310 : ∀ x ∈ envelope_310,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_310 j := by decide +kernel
theorem envelope_exact_310 : envelope_310 =
    insert (1, 3) (Finset.univ.biUnion childrenD_310) := by
  exact envelope_eq_combination childrenD_310 (1, 3) envelope_310
    pivot_mem_310 child_envelope_sub_310 envelope_origin_310
def checked_310 : CheckedCard where
  required := required_310
  envelope := envelope_310
  height := height_310
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_310
def height_333_i0 : ℕ := 2
def childrenH_333_i0 : Fin 2 → ℕ := ![height_0, height_3]
theorem height_exact_333_i0 : height_333_i0 = 1 + Finset.univ.sup childrenH_333_i0 := by decide +kernel
theorem required_origin_333_i0 : ∀ x ∈ required_333_i0,
    (∃ j, x ∈ childrenC_333_i0 j) ∨ ∀ j, x ∈ childrenD_333_i0 j := by decide +kernel
theorem required_exact_333_i0 : required_333_i0 =
    ((Finset.univ.biUnion childrenC_333_i0) ∪ commonEnvelope childrenD_333_i0).erase (0, 2) := by
  exact required_eq_combination childrenC_333_i0 childrenD_333_i0 (0, 2) required_333_i0
    (by decide +kernel) child_required_sub_333_i0 common_sub_333_i0 required_origin_333_i0
theorem envelope_origin_333_i0 : ∀ x ∈ envelope_333_i0,
    x = (0, 2) ∨ ∃ j, x ∈ childrenD_333_i0 j := by decide +kernel
theorem envelope_exact_333_i0 : envelope_333_i0 =
    insert (0, 2) (Finset.univ.biUnion childrenD_333_i0) := by
  exact envelope_eq_combination childrenD_333_i0 (0, 2) envelope_333_i0
    pivot_mem_333_i0 child_envelope_sub_333_i0 envelope_origin_333_i0
def checked_333_i0 : CheckedCard where
  required := required_333_i0
  envelope := envelope_333_i0
  height := height_333_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_333_i0
def height_333 : ℕ := 3
def childrenH_333 : Fin 2 → ℕ := ![height_3, height_333_i0]
theorem height_exact_333 : height_333 = 1 + Finset.univ.sup childrenH_333 := by decide +kernel
theorem required_origin_333 : ∀ x ∈ required_333,
    (∃ j, x ∈ childrenC_333 j) ∨ ∀ j, x ∈ childrenD_333 j := by decide +kernel
theorem required_exact_333 : required_333 =
    ((Finset.univ.biUnion childrenC_333) ∪ commonEnvelope childrenD_333).erase (1, 4) := by
  exact required_eq_combination childrenC_333 childrenD_333 (1, 4) required_333
    (by decide +kernel) child_required_sub_333 common_sub_333 required_origin_333
theorem envelope_origin_333 : ∀ x ∈ envelope_333,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_333 j := by decide +kernel
theorem envelope_exact_333 : envelope_333 =
    insert (1, 4) (Finset.univ.biUnion childrenD_333) := by
  exact envelope_eq_combination childrenD_333 (1, 4) envelope_333
    pivot_mem_333 child_envelope_sub_333 envelope_origin_333
def checked_333 : CheckedCard where
  required := required_333
  envelope := envelope_333
  height := height_333
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_333
def height_350_i0 : ℕ := 2
def childrenH_350_i0 : Fin 2 → ℕ := ![height_1, height_5]
theorem height_exact_350_i0 : height_350_i0 = 1 + Finset.univ.sup childrenH_350_i0 := by decide +kernel
theorem required_origin_350_i0 : ∀ x ∈ required_350_i0,
    (∃ j, x ∈ childrenC_350_i0 j) ∨ ∀ j, x ∈ childrenD_350_i0 j := by decide +kernel
theorem required_exact_350_i0 : required_350_i0 =
    ((Finset.univ.biUnion childrenC_350_i0) ∪ commonEnvelope childrenD_350_i0).erase (4, 1) := by
  exact required_eq_combination childrenC_350_i0 childrenD_350_i0 (4, 1) required_350_i0
    (by decide +kernel) child_required_sub_350_i0 common_sub_350_i0 required_origin_350_i0
theorem envelope_origin_350_i0 : ∀ x ∈ envelope_350_i0,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_350_i0 j := by decide +kernel
theorem envelope_exact_350_i0 : envelope_350_i0 =
    insert (4, 1) (Finset.univ.biUnion childrenD_350_i0) := by
  exact envelope_eq_combination childrenD_350_i0 (4, 1) envelope_350_i0
    pivot_mem_350_i0 child_envelope_sub_350_i0 envelope_origin_350_i0
def checked_350_i0 : CheckedCard where
  required := required_350_i0
  envelope := envelope_350_i0
  height := height_350_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_350_i0
def height_350 : ℕ := 3
def childrenH_350 : Fin 2 → ℕ := ![height_4, height_350_i0]
theorem height_exact_350 : height_350 = 1 + Finset.univ.sup childrenH_350 := by decide +kernel
theorem required_origin_350 : ∀ x ∈ required_350,
    (∃ j, x ∈ childrenC_350 j) ∨ ∀ j, x ∈ childrenD_350 j := by decide +kernel
theorem required_exact_350 : required_350 =
    ((Finset.univ.biUnion childrenC_350) ∪ commonEnvelope childrenD_350).erase (4, 0) := by
  exact required_eq_combination childrenC_350 childrenD_350 (4, 0) required_350
    (by decide +kernel) child_required_sub_350 common_sub_350 required_origin_350
theorem envelope_origin_350 : ∀ x ∈ envelope_350,
    x = (4, 0) ∨ ∃ j, x ∈ childrenD_350 j := by decide +kernel
theorem envelope_exact_350 : envelope_350 =
    insert (4, 0) (Finset.univ.biUnion childrenD_350) := by
  exact envelope_eq_combination childrenD_350 (4, 0) envelope_350
    pivot_mem_350 child_envelope_sub_350 envelope_origin_350
def checked_350 : CheckedCard where
  required := required_350
  envelope := envelope_350
  height := height_350
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_350
def height_374_i0 : ℕ := 2
def childrenH_374_i0 : Fin 2 → ℕ := ![height_1, height_5]
theorem height_exact_374_i0 : height_374_i0 = 1 + Finset.univ.sup childrenH_374_i0 := by decide +kernel
theorem required_origin_374_i0 : ∀ x ∈ required_374_i0,
    (∃ j, x ∈ childrenC_374_i0 j) ∨ ∀ j, x ∈ childrenD_374_i0 j := by decide +kernel
theorem required_exact_374_i0 : required_374_i0 =
    ((Finset.univ.biUnion childrenC_374_i0) ∪ commonEnvelope childrenD_374_i0).erase (4, 1) := by
  exact required_eq_combination childrenC_374_i0 childrenD_374_i0 (4, 1) required_374_i0
    (by decide +kernel) child_required_sub_374_i0 common_sub_374_i0 required_origin_374_i0
theorem envelope_origin_374_i0 : ∀ x ∈ envelope_374_i0,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_374_i0 j := by decide +kernel
theorem envelope_exact_374_i0 : envelope_374_i0 =
    insert (4, 1) (Finset.univ.biUnion childrenD_374_i0) := by
  exact envelope_eq_combination childrenD_374_i0 (4, 1) envelope_374_i0
    pivot_mem_374_i0 child_envelope_sub_374_i0 envelope_origin_374_i0
def checked_374_i0 : CheckedCard where
  required := required_374_i0
  envelope := envelope_374_i0
  height := height_374_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_374_i0
def height_374 : ℕ := 3
def childrenH_374 : Fin 2 → ℕ := ![height_4, height_374_i0]
theorem height_exact_374 : height_374 = 1 + Finset.univ.sup childrenH_374 := by decide +kernel
theorem required_origin_374 : ∀ x ∈ required_374,
    (∃ j, x ∈ childrenC_374 j) ∨ ∀ j, x ∈ childrenD_374 j := by decide +kernel
theorem required_exact_374 : required_374 =
    ((Finset.univ.biUnion childrenC_374) ∪ commonEnvelope childrenD_374).erase (4, 2) := by
  exact required_eq_combination childrenC_374 childrenD_374 (4, 2) required_374
    (by decide +kernel) child_required_sub_374 common_sub_374 required_origin_374
theorem envelope_origin_374 : ∀ x ∈ envelope_374,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_374 j := by decide +kernel
theorem envelope_exact_374 : envelope_374 =
    insert (4, 2) (Finset.univ.biUnion childrenD_374) := by
  exact envelope_eq_combination childrenD_374 (4, 2) envelope_374
    pivot_mem_374 child_envelope_sub_374 envelope_origin_374
def checked_374 : CheckedCard where
  required := required_374
  envelope := envelope_374
  height := height_374
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_374
def height_402_i0 : ℕ := 2
def childrenH_402_i0 : Fin 2 → ℕ := ![height_0, height_5]
theorem height_exact_402_i0 : height_402_i0 = 1 + Finset.univ.sup childrenH_402_i0 := by decide +kernel
theorem required_origin_402_i0 : ∀ x ∈ required_402_i0,
    (∃ j, x ∈ childrenC_402_i0 j) ∨ ∀ j, x ∈ childrenD_402_i0 j := by decide +kernel
theorem required_exact_402_i0 : required_402_i0 =
    ((Finset.univ.biUnion childrenC_402_i0) ∪ commonEnvelope childrenD_402_i0).erase (2, 4) := by
  exact required_eq_combination childrenC_402_i0 childrenD_402_i0 (2, 4) required_402_i0
    (by decide +kernel) child_required_sub_402_i0 common_sub_402_i0 required_origin_402_i0
theorem envelope_origin_402_i0 : ∀ x ∈ envelope_402_i0,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_402_i0 j := by decide +kernel
theorem envelope_exact_402_i0 : envelope_402_i0 =
    insert (2, 4) (Finset.univ.biUnion childrenD_402_i0) := by
  exact envelope_eq_combination childrenD_402_i0 (2, 4) envelope_402_i0
    pivot_mem_402_i0 child_envelope_sub_402_i0 envelope_origin_402_i0
def checked_402_i0 : CheckedCard where
  required := required_402_i0
  envelope := envelope_402_i0
  height := height_402_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_402_i0
def height_402 : ℕ := 3
def childrenH_402 : Fin 2 → ℕ := ![height_38, height_402_i0]
theorem height_exact_402 : height_402 = 1 + Finset.univ.sup childrenH_402 := by decide +kernel
theorem required_origin_402 : ∀ x ∈ required_402,
    (∃ j, x ∈ childrenC_402 j) ∨ ∀ j, x ∈ childrenD_402 j := by decide +kernel
theorem required_exact_402 : required_402 =
    ((Finset.univ.biUnion childrenC_402) ∪ commonEnvelope childrenD_402).erase (3, 1) := by
  exact required_eq_combination childrenC_402 childrenD_402 (3, 1) required_402
    (by decide +kernel) child_required_sub_402 common_sub_402 required_origin_402
theorem envelope_origin_402 : ∀ x ∈ envelope_402,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_402 j := by decide +kernel
theorem envelope_exact_402 : envelope_402 =
    insert (3, 1) (Finset.univ.biUnion childrenD_402) := by
  exact envelope_eq_combination childrenD_402 (3, 1) envelope_402
    pivot_mem_402 child_envelope_sub_402 envelope_origin_402
def checked_402 : CheckedCard where
  required := required_402
  envelope := envelope_402
  height := height_402
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_402
end SnakyPrototype.Certificate21

end OAI
