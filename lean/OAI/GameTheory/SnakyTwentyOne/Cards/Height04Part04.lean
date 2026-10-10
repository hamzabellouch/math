import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_268 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_268 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 4), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 4), (2, 5), (2, 6), (2, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_268 : Fin 3 → Finset Cell := ![(placed21 6 (1, 6) required_7), (placed21 1 (0, 2) required_8), (placed21 6 (2, 6) required_9)]
def childrenD_268 : Fin 3 → Finset Cell := ![(placed21 6 (1, 6) envelope_7), (placed21 1 (0, 2) envelope_8), (placed21 6 (2, 6) envelope_9)]
theorem common_sub_268 : commonEnvelope childrenD_268 ⊆ insert (1, 4) required_268 := by decide +kernel
theorem child_required_sub_268 : ∀ j, childrenC_268 j ⊆ insert (1, 4) required_268 := by decide +kernel
theorem child_envelope_sub_268 : ∀ j, childrenD_268 j ⊆ envelope_268 := by decide +kernel
theorem pivot_mem_268 : (1, 4) ∈ envelope_268 := by decide +kernel
theorem children_work_268 : ∀ j, Template HasSnaky 3 (childrenC_268 j) (childrenD_268 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 6 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 6 (2, 6)).mono (by decide +kernel)
theorem row_works_268 : Template HasSnaky 4 required_268 envelope_268 := by
  refine compose HasSnaky 3 childrenC_268 childrenD_268 children_work_268 (1, 4)
    required_268 envelope_268 pivot_mem_268 child_required_sub_268 child_envelope_sub_268 ?_
  intro b hb
  exact common_sub_268 (mem_commonEnvelope childrenD_268 b hb)
def required_269 : Finset Cell := ⟨(([(0, 3), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_269 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_269 : Fin 2 → Finset Cell := ![(placed21 4 (1, 6) required_7), (placed21 2 (1, 2) required_21)]
def childrenD_269 : Fin 2 → Finset Cell := ![(placed21 4 (1, 6) envelope_7), (placed21 2 (1, 2) envelope_21)]
theorem common_sub_269 : commonEnvelope childrenD_269 ⊆ insert (1, 5) required_269 := by decide +kernel
theorem child_required_sub_269 : ∀ j, childrenC_269 j ⊆ insert (1, 5) required_269 := by decide +kernel
theorem child_envelope_sub_269 : ∀ j, childrenD_269 j ⊆ envelope_269 := by decide +kernel
theorem pivot_mem_269 : (1, 5) ∈ envelope_269 := by decide +kernel
theorem children_work_269 : ∀ j, Template HasSnaky 3 (childrenC_269 j) (childrenD_269 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 4 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_21 2 (1, 2)).mono (by decide +kernel)
theorem row_works_269 : Template HasSnaky 4 required_269 envelope_269 := by
  refine compose HasSnaky 3 childrenC_269 childrenD_269 children_work_269 (1, 5)
    required_269 envelope_269 pivot_mem_269 child_required_sub_269 child_envelope_sub_269 ?_
  intro b hb
  exact common_sub_269 (mem_commonEnvelope childrenD_269 b hb)
def required_271 : Finset Cell := ⟨(([(0, 3), (1, 3), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_271 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_271 : Fin 2 → Finset Cell := ![(placed21 4 (0, 3) required_5), (placed21 2 (3, 0) required_52)]
def childrenD_271 : Fin 2 → Finset Cell := ![(placed21 4 (0, 3) envelope_5), (placed21 2 (3, 0) envelope_52)]
theorem common_sub_271 : commonEnvelope childrenD_271 ⊆ insert (2, 3) required_271 := by decide +kernel
theorem child_required_sub_271 : ∀ j, childrenC_271 j ⊆ insert (2, 3) required_271 := by decide +kernel
theorem child_envelope_sub_271 : ∀ j, childrenD_271 j ⊆ envelope_271 := by decide +kernel
theorem pivot_mem_271 : (2, 3) ∈ envelope_271 := by decide +kernel
theorem children_work_271 : ∀ j, Template HasSnaky 3 (childrenC_271 j) (childrenD_271 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 2 (3, 0)).mono (by decide +kernel)
theorem row_works_271 : Template HasSnaky 4 required_271 envelope_271 := by
  refine compose HasSnaky 3 childrenC_271 childrenD_271 children_work_271 (2, 3)
    required_271 envelope_271 pivot_mem_271 child_required_sub_271 child_envelope_sub_271 ?_
  intro b hb
  exact common_sub_271 (mem_commonEnvelope childrenD_271 b hb)
def required_277 : Finset Cell := ⟨(([(1, 2), (2, 2), (2, 3), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_277 : Finset Cell := ⟨(([(0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4), (2, 5), (3, 2), (4, 2), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_277 : Fin 2 → Finset Cell := ![(placed21 2 (5, 2) required_0), (placed21 2 (4, 0) required_69)]
def childrenD_277 : Fin 2 → Finset Cell := ![(placed21 2 (5, 2) envelope_0), (placed21 2 (4, 0) envelope_69)]
theorem common_sub_277 : commonEnvelope childrenD_277 ⊆ insert (1, 3) required_277 := by decide +kernel
theorem child_required_sub_277 : ∀ j, childrenC_277 j ⊆ insert (1, 3) required_277 := by decide +kernel
theorem child_envelope_sub_277 : ∀ j, childrenD_277 j ⊆ envelope_277 := by decide +kernel
theorem pivot_mem_277 : (1, 3) ∈ envelope_277 := by decide +kernel
theorem children_work_277 : ∀ j, Template HasSnaky 3 (childrenC_277 j) (childrenD_277 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 2 (5, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_69 2 (4, 0)).mono (by decide +kernel)
theorem row_works_277 : Template HasSnaky 4 required_277 envelope_277 := by
  refine compose HasSnaky 3 childrenC_277 childrenD_277 children_work_277 (1, 3)
    required_277 envelope_277 pivot_mem_277 child_required_sub_277 child_envelope_sub_277 ?_
  intro b hb
  exact common_sub_277 (mem_commonEnvelope childrenD_277 b hb)
def required_288 : Finset Cell := ⟨(([(0, 0), (0, 3), (1, 3), (1, 4), (3, 4), (3, 5), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_288 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 5), (1, 3), (1, 4), (1, 5), (1, 6), (2, 5), (3, 4), (3, 5), (4, 4), (4, 5), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_288 : Fin 2 → Finset Cell := ![(placed21 3 (0, 5) required_54), required_68]
def childrenD_288 : Fin 2 → Finset Cell := ![(placed21 3 (0, 5) envelope_54), envelope_68]
theorem common_sub_288 : commonEnvelope childrenD_288 ⊆ insert (1, 5) required_288 := by decide +kernel
theorem child_required_sub_288 : ∀ j, childrenC_288 j ⊆ insert (1, 5) required_288 := by decide +kernel
theorem child_envelope_sub_288 : ∀ j, childrenD_288 j ⊆ envelope_288 := by decide +kernel
theorem pivot_mem_288 : (1, 5) ∈ envelope_288 := by decide +kernel
theorem children_work_288 : ∀ j, Template HasSnaky 3 (childrenC_288 j) (childrenD_288 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_54 3 (0, 5)).mono (by decide +kernel)
  · exact row_works_68.mono (by decide +kernel)
theorem row_works_288 : Template HasSnaky 4 required_288 envelope_288 := by
  refine compose HasSnaky 3 childrenC_288 childrenD_288 children_work_288 (1, 5)
    required_288 envelope_288 pivot_mem_288 child_required_sub_288 child_envelope_sub_288 ?_
  intro b hb
  exact common_sub_288 (mem_commonEnvelope childrenD_288 b hb)
def required_289 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (1, 1), (1, 4), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_289 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_289 : Fin 3 → Finset Cell := ![required_22, (placed21 4 (0, 5) required_28), (placed21 6 (2, 5) required_126)]
def childrenD_289 : Fin 3 → Finset Cell := ![envelope_22, (placed21 4 (0, 5) envelope_28), (placed21 6 (2, 5) envelope_126)]
theorem common_sub_289 : commonEnvelope childrenD_289 ⊆ insert (1, 2) required_289 := by decide +kernel
theorem child_required_sub_289 : ∀ j, childrenC_289 j ⊆ insert (1, 2) required_289 := by decide +kernel
theorem child_envelope_sub_289 : ∀ j, childrenD_289 j ⊆ envelope_289 := by decide +kernel
theorem pivot_mem_289 : (1, 2) ∈ envelope_289 := by decide +kernel
theorem children_work_289 : ∀ j, Template HasSnaky 3 (childrenC_289 j) (childrenD_289 j) := by
  intro j
  fin_cases j
  · exact row_works_22.mono (by decide +kernel)
  · exact (placed21_template row_works_28 4 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_126 6 (2, 5)).mono (by decide +kernel)
theorem row_works_289 : Template HasSnaky 4 required_289 envelope_289 := by
  refine compose HasSnaky 3 childrenC_289 childrenD_289 children_work_289 (1, 2)
    required_289 envelope_289 pivot_mem_289 child_required_sub_289 child_envelope_sub_289 ?_
  intro b hb
  exact common_sub_289 (mem_commonEnvelope childrenD_289 b hb)
def required_291 : Finset Cell := ⟨(([(0, 3), (1, 3), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_291 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_291 : Fin 2 → Finset Cell := ![(placed21 2 (3, 0) required_7), (placed21 5 (4, 1) required_25)]
def childrenD_291 : Fin 2 → Finset Cell := ![(placed21 2 (3, 0) envelope_7), (placed21 5 (4, 1) envelope_25)]
theorem common_sub_291 : commonEnvelope childrenD_291 ⊆ insert (3, 4) required_291 := by decide +kernel
theorem child_required_sub_291 : ∀ j, childrenC_291 j ⊆ insert (3, 4) required_291 := by decide +kernel
theorem child_envelope_sub_291 : ∀ j, childrenD_291 j ⊆ envelope_291 := by decide +kernel
theorem pivot_mem_291 : (3, 4) ∈ envelope_291 := by decide +kernel
theorem children_work_291 : ∀ j, Template HasSnaky 3 (childrenC_291 j) (childrenD_291 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 2 (3, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_25 5 (4, 1)).mono (by decide +kernel)
theorem row_works_291 : Template HasSnaky 4 required_291 envelope_291 := by
  refine compose HasSnaky 3 childrenC_291 childrenD_291 children_work_291 (3, 4)
    required_291 envelope_291 pivot_mem_291 child_required_sub_291 child_envelope_sub_291 ?_
  intro b hb
  exact common_sub_291 (mem_commonEnvelope childrenD_291 b hb)
def required_304 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_304 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 4), (2, 5), (2, 6), (2, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_304 : Fin 3 → Finset Cell := ![(placed21 2 (1, 1) required_7), (placed21 1 (0, 2) required_8), (placed21 6 (2, 6) required_9)]
def childrenD_304 : Fin 3 → Finset Cell := ![(placed21 2 (1, 1) envelope_7), (placed21 1 (0, 2) envelope_8), (placed21 6 (2, 6) envelope_9)]
theorem common_sub_304 : commonEnvelope childrenD_304 ⊆ insert (1, 4) required_304 := by decide +kernel
theorem child_required_sub_304 : ∀ j, childrenC_304 j ⊆ insert (1, 4) required_304 := by decide +kernel
theorem child_envelope_sub_304 : ∀ j, childrenD_304 j ⊆ envelope_304 := by decide +kernel
theorem pivot_mem_304 : (1, 4) ∈ envelope_304 := by decide +kernel
theorem children_work_304 : ∀ j, Template HasSnaky 3 (childrenC_304 j) (childrenD_304 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 2 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 6 (2, 6)).mono (by decide +kernel)
theorem row_works_304 : Template HasSnaky 4 required_304 envelope_304 := by
  refine compose HasSnaky 3 childrenC_304 childrenD_304 children_work_304 (1, 4)
    required_304 envelope_304 pivot_mem_304 child_required_sub_304 child_envelope_sub_304 ?_
  intro b hb
  exact common_sub_304 (mem_commonEnvelope childrenD_304 b hb)
def required_305 : Finset Cell := ⟨(([(0, 1), (0, 4), (1, 1), (1, 2), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_305 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_305 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_5), (placed21 4 (0, 5) required_124)]
def childrenD_305 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_5), (placed21 4 (0, 5) envelope_124)]
theorem common_sub_305 : commonEnvelope childrenD_305 ⊆ insert (1, 3) required_305 := by decide +kernel
theorem child_required_sub_305 : ∀ j, childrenC_305 j ⊆ insert (1, 3) required_305 := by decide +kernel
theorem child_envelope_sub_305 : ∀ j, childrenD_305 j ⊆ envelope_305 := by decide +kernel
theorem pivot_mem_305 : (1, 3) ∈ envelope_305 := by decide +kernel
theorem children_work_305 : ∀ j, Template HasSnaky 3 (childrenC_305 j) (childrenD_305 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_124 4 (0, 5)).mono (by decide +kernel)
theorem row_works_305 : Template HasSnaky 4 required_305 envelope_305 := by
  refine compose HasSnaky 3 childrenC_305 childrenD_305 children_work_305 (1, 3)
    required_305 envelope_305 pivot_mem_305 child_required_sub_305 child_envelope_sub_305 ?_
  intro b hb
  exact common_sub_305 (mem_commonEnvelope childrenD_305 b hb)
def required_307 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (2, 2), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_307 : Finset Cell := ⟨(([(0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4), (2, 5), (3, 2), (4, 2), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_307 : Fin 2 → Finset Cell := ![(placed21 6 (4, 2) required_5), (placed21 0 (1, 0) required_131)]
def childrenD_307 : Fin 2 → Finset Cell := ![(placed21 6 (4, 2) envelope_5), (placed21 0 (1, 0) envelope_131)]
theorem common_sub_307 : commonEnvelope childrenD_307 ⊆ insert (4, 2) required_307 := by decide +kernel
theorem child_required_sub_307 : ∀ j, childrenC_307 j ⊆ insert (4, 2) required_307 := by decide +kernel
theorem child_envelope_sub_307 : ∀ j, childrenD_307 j ⊆ envelope_307 := by decide +kernel
theorem pivot_mem_307 : (4, 2) ∈ envelope_307 := by decide +kernel
theorem children_work_307 : ∀ j, Template HasSnaky 3 (childrenC_307 j) (childrenD_307 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 6 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_131 0 (1, 0)).mono (by decide +kernel)
theorem row_works_307 : Template HasSnaky 4 required_307 envelope_307 := by
  refine compose HasSnaky 3 childrenC_307 childrenD_307 children_work_307 (4, 2)
    required_307 envelope_307 pivot_mem_307 child_required_sub_307 child_envelope_sub_307 ?_
  intro b hb
  exact common_sub_307 (mem_commonEnvelope childrenD_307 b hb)
def required_311_i0 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1), (4, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_311_i0 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_311_i0 : Fin 2 → Finset Cell := ![(placed21 4 (1, 1) required_5), (placed21 1 (0, 1) required_6)]
def childrenD_311_i0 : Fin 2 → Finset Cell := ![(placed21 4 (1, 1) envelope_5), (placed21 1 (0, 1) envelope_6)]
theorem common_sub_311_i0 : commonEnvelope childrenD_311_i0 ⊆ insert (4, 1) required_311_i0 := by decide +kernel
theorem child_required_sub_311_i0 : ∀ j, childrenC_311_i0 j ⊆ insert (4, 1) required_311_i0 := by decide +kernel
theorem child_envelope_sub_311_i0 : ∀ j, childrenD_311_i0 j ⊆ envelope_311_i0 := by decide +kernel
theorem pivot_mem_311_i0 : (4, 1) ∈ envelope_311_i0 := by decide +kernel
theorem children_work_311_i0 : ∀ j, Template HasSnaky 2 (childrenC_311_i0 j) (childrenD_311_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_6 1 (0, 1)).mono (by decide +kernel)
theorem row_works_311_i0 : Template HasSnaky 3 required_311_i0 envelope_311_i0 := by
  refine compose HasSnaky 2 childrenC_311_i0 childrenD_311_i0 children_work_311_i0 (4, 1)
    required_311_i0 envelope_311_i0 pivot_mem_311_i0 child_required_sub_311_i0 child_envelope_sub_311_i0 ?_
  intro b hb
  exact common_sub_311_i0 (mem_commonEnvelope childrenD_311_i0 b hb)
def required_311 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (4, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_311 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_311 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) required_4), required_311_i0]
def childrenD_311 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) envelope_4), envelope_311_i0]
theorem common_sub_311 : commonEnvelope childrenD_311 ⊆ insert (3, 1) required_311 := by decide +kernel
theorem child_required_sub_311 : ∀ j, childrenC_311 j ⊆ insert (3, 1) required_311 := by decide +kernel
theorem child_envelope_sub_311 : ∀ j, childrenD_311 j ⊆ envelope_311 := by decide +kernel
theorem pivot_mem_311 : (3, 1) ∈ envelope_311 := by decide +kernel
theorem children_work_311 : ∀ j, Template HasSnaky 3 (childrenC_311 j) (childrenD_311 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 4 (0, 1)).mono (by decide +kernel)
  · exact row_works_311_i0.mono (by decide +kernel)
theorem row_works_311 : Template HasSnaky 4 required_311 envelope_311 := by
  refine compose HasSnaky 3 childrenC_311 childrenD_311 children_work_311 (3, 1)
    required_311 envelope_311 pivot_mem_311 child_required_sub_311 child_envelope_sub_311 ?_
  intro b hb
  exact common_sub_311 (mem_commonEnvelope childrenD_311 b hb)
def required_334 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_334 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_334 : Fin 4 → Finset Cell := ![(placed21 0 (0, 1) required_101), (placed21 6 (1, 6) required_101), (placed21 0 (0, 2) required_333), (placed21 6 (1, 5) required_333)]
def childrenD_334 : Fin 4 → Finset Cell := ![(placed21 0 (0, 1) envelope_101), (placed21 6 (1, 6) envelope_101), (placed21 0 (0, 2) envelope_333), (placed21 6 (1, 5) envelope_333)]
theorem common_sub_334 : commonEnvelope childrenD_334 ⊆ insert (1, 5) required_334 := by decide +kernel
theorem child_required_sub_334 : ∀ j, childrenC_334 j ⊆ insert (1, 5) required_334 := by decide +kernel
theorem child_envelope_sub_334 : ∀ j, childrenD_334 j ⊆ envelope_334 := by decide +kernel
theorem pivot_mem_334 : (1, 5) ∈ envelope_334 := by decide +kernel
theorem children_work_334 : ∀ j, Template HasSnaky 3 (childrenC_334 j) (childrenD_334 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_101 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_101 6 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_333 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_333 6 (1, 5)).mono (by decide +kernel)
theorem row_works_334 : Template HasSnaky 4 required_334 envelope_334 := by
  refine compose HasSnaky 3 childrenC_334 childrenD_334 children_work_334 (1, 5)
    required_334 envelope_334 pivot_mem_334 child_required_sub_334 child_envelope_sub_334 ?_
  intro b hb
  exact common_sub_334 (mem_commonEnvelope childrenD_334 b hb)
def required_351 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 2), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_351 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (5, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_351 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_5), required_350]
def childrenD_351 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_5), envelope_350]
theorem common_sub_351 : commonEnvelope childrenD_351 ⊆ insert (3, 1) required_351 := by decide +kernel
theorem child_required_sub_351 : ∀ j, childrenC_351 j ⊆ insert (3, 1) required_351 := by decide +kernel
theorem child_envelope_sub_351 : ∀ j, childrenD_351 j ⊆ envelope_351 := by decide +kernel
theorem pivot_mem_351 : (3, 1) ∈ envelope_351 := by decide +kernel
theorem children_work_351 : ∀ j, Template HasSnaky 3 (childrenC_351 j) (childrenD_351 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_350.mono (by decide +kernel)
theorem row_works_351 : Template HasSnaky 4 required_351 envelope_351 := by
  refine compose HasSnaky 3 childrenC_351 childrenD_351 children_work_351 (3, 1)
    required_351 envelope_351 pivot_mem_351 child_required_sub_351 child_envelope_sub_351 ?_
  intro b hb
  exact common_sub_351 (mem_commonEnvelope childrenD_351 b hb)
def required_354_i0 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 4), (3, 0), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_354_i0 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_354_i0 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_5), (placed21 2 (3, 0) required_70)]
def childrenD_354_i0 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_5), (placed21 2 (3, 0) envelope_70)]
theorem common_sub_354_i0 : commonEnvelope childrenD_354_i0 ⊆ insert (3, 2) required_354_i0 := by decide +kernel
theorem child_required_sub_354_i0 : ∀ j, childrenC_354_i0 j ⊆ insert (3, 2) required_354_i0 := by decide +kernel
theorem child_envelope_sub_354_i0 : ∀ j, childrenD_354_i0 j ⊆ envelope_354_i0 := by decide +kernel
theorem pivot_mem_354_i0 : (3, 2) ∈ envelope_354_i0 := by decide +kernel
theorem children_work_354_i0 : ∀ j, Template HasSnaky 2 (childrenC_354_i0 j) (childrenD_354_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_70 2 (3, 0)).mono (by decide +kernel)
theorem row_works_354_i0 : Template HasSnaky 3 required_354_i0 envelope_354_i0 := by
  refine compose HasSnaky 2 childrenC_354_i0 childrenD_354_i0 children_work_354_i0 (3, 2)
    required_354_i0 envelope_354_i0 pivot_mem_354_i0 child_required_sub_354_i0 child_envelope_sub_354_i0 ?_
  intro b hb
  exact common_sub_354_i0 (mem_commonEnvelope childrenD_354_i0 b hb)
def required_354 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 4), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_354 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_354 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) required_5), required_354_i0]
def childrenD_354 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) envelope_5), envelope_354_i0]
theorem common_sub_354 : commonEnvelope childrenD_354 ⊆ insert (3, 0) required_354 := by decide +kernel
theorem child_required_sub_354 : ∀ j, childrenC_354 j ⊆ insert (3, 0) required_354 := by decide +kernel
theorem child_envelope_sub_354 : ∀ j, childrenD_354 j ⊆ envelope_354 := by decide +kernel
theorem pivot_mem_354 : (3, 0) ∈ envelope_354 := by decide +kernel
theorem children_work_354 : ∀ j, Template HasSnaky 3 (childrenC_354 j) (childrenD_354 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact row_works_354_i0.mono (by decide +kernel)
theorem row_works_354 : Template HasSnaky 4 required_354 envelope_354 := by
  refine compose HasSnaky 3 childrenC_354 childrenD_354 children_work_354 (3, 0)
    required_354 envelope_354 pivot_mem_354 child_required_sub_354 child_envelope_sub_354 ?_
  intro b hb
  exact common_sub_354 (mem_commonEnvelope childrenD_354 b hb)
def required_365_i1 : Finset Cell := ⟨(([(0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_365_i1 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_365_i1 : Fin 2 → Finset Cell := ![(placed21 5 (1, 0) required_0), (placed21 7 (1, 7) required_0)]
def childrenD_365_i1 : Fin 2 → Finset Cell := ![(placed21 5 (1, 0) envelope_0), (placed21 7 (1, 7) envelope_0)]
theorem common_sub_365_i1 : commonEnvelope childrenD_365_i1 ⊆ insert (0, 4) required_365_i1 := by decide +kernel
theorem child_required_sub_365_i1 : ∀ j, childrenC_365_i1 j ⊆ insert (0, 4) required_365_i1 := by decide +kernel
theorem child_envelope_sub_365_i1 : ∀ j, childrenD_365_i1 j ⊆ envelope_365_i1 := by decide +kernel
theorem pivot_mem_365_i1 : (0, 4) ∈ envelope_365_i1 := by decide +kernel
theorem children_work_365_i1 : ∀ j, Template HasSnaky 1 (childrenC_365_i1 j) (childrenD_365_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 5 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_0 7 (1, 7)).mono (by decide +kernel)
theorem row_works_365_i1 : Template HasSnaky 2 required_365_i1 envelope_365_i1 := by
  refine compose HasSnaky 1 childrenC_365_i1 childrenD_365_i1 children_work_365_i1 (0, 4)
    required_365_i1 envelope_365_i1 pivot_mem_365_i1 child_required_sub_365_i1 child_envelope_sub_365_i1 ?_
  intro b hb
  exact common_sub_365_i1 (mem_commonEnvelope childrenD_365_i1 b hb)
def required_365_i0 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_365_i0 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_365_i0 : Fin 2 → Finset Cell := ![(placed21 7 (1, 6) required_5), required_365_i1]
def childrenD_365_i0 : Fin 2 → Finset Cell := ![(placed21 7 (1, 6) envelope_5), envelope_365_i1]
theorem common_sub_365_i0 : commonEnvelope childrenD_365_i0 ⊆ insert (0, 3) required_365_i0 := by decide +kernel
theorem child_required_sub_365_i0 : ∀ j, childrenC_365_i0 j ⊆ insert (0, 3) required_365_i0 := by decide +kernel
theorem child_envelope_sub_365_i0 : ∀ j, childrenD_365_i0 j ⊆ envelope_365_i0 := by decide +kernel
theorem pivot_mem_365_i0 : (0, 3) ∈ envelope_365_i0 := by decide +kernel
theorem children_work_365_i0 : ∀ j, Template HasSnaky 2 (childrenC_365_i0 j) (childrenD_365_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 6)).mono (by decide +kernel)
  · exact row_works_365_i1.mono (by decide +kernel)
theorem row_works_365_i0 : Template HasSnaky 3 required_365_i0 envelope_365_i0 := by
  refine compose HasSnaky 2 childrenC_365_i0 childrenD_365_i0 children_work_365_i0 (0, 3)
    required_365_i0 envelope_365_i0 pivot_mem_365_i0 child_required_sub_365_i0 child_envelope_sub_365_i0 ?_
  intro b hb
  exact common_sub_365_i0 (mem_commonEnvelope childrenD_365_i0 b hb)
def required_365 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_365 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 5), (2, 6), (2, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_365 : Fin 2 → Finset Cell := ![(placed21 0 (1, 2) required_6), required_365_i0]
def childrenD_365 : Fin 2 → Finset Cell := ![(placed21 0 (1, 2) envelope_6), envelope_365_i0]
theorem common_sub_365 : commonEnvelope childrenD_365 ⊆ insert (1, 6) required_365 := by decide +kernel
theorem child_required_sub_365 : ∀ j, childrenC_365 j ⊆ insert (1, 6) required_365 := by decide +kernel
theorem child_envelope_sub_365 : ∀ j, childrenD_365 j ⊆ envelope_365 := by decide +kernel
theorem pivot_mem_365 : (1, 6) ∈ envelope_365 := by decide +kernel
theorem children_work_365 : ∀ j, Template HasSnaky 3 (childrenC_365 j) (childrenD_365 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 0 (1, 2)).mono (by decide +kernel)
  · exact row_works_365_i0.mono (by decide +kernel)
theorem row_works_365 : Template HasSnaky 4 required_365 envelope_365 := by
  refine compose HasSnaky 3 childrenC_365 childrenD_365 children_work_365 (1, 6)
    required_365 envelope_365 pivot_mem_365 child_required_sub_365 child_envelope_sub_365 ?_
  intro b hb
  exact common_sub_365 (mem_commonEnvelope childrenD_365 b hb)
def required_375 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 0), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_375 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_375 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) required_5), required_374]
def childrenD_375 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) envelope_5), envelope_374]
theorem common_sub_375 : commonEnvelope childrenD_375 ⊆ insert (3, 1) required_375 := by decide +kernel
theorem child_required_sub_375 : ∀ j, childrenC_375 j ⊆ insert (3, 1) required_375 := by decide +kernel
theorem child_envelope_sub_375 : ∀ j, childrenD_375 j ⊆ envelope_375 := by decide +kernel
theorem pivot_mem_375 : (3, 1) ∈ envelope_375 := by decide +kernel
theorem children_work_375 : ∀ j, Template HasSnaky 3 (childrenC_375 j) (childrenD_375 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact row_works_374.mono (by decide +kernel)
theorem row_works_375 : Template HasSnaky 4 required_375 envelope_375 := by
  refine compose HasSnaky 3 childrenC_375 childrenD_375 children_work_375 (3, 1)
    required_375 envelope_375 pivot_mem_375 child_required_sub_375 child_envelope_sub_375 ?_
  intro b hb
  exact common_sub_375 (mem_commonEnvelope childrenD_375 b hb)
def required_376_i0 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 3), (3, 0), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_376_i0 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_376_i0 : Fin 2 → Finset Cell := ![(placed21 3 (2, 4) required_2), (placed21 5 (4, 0) required_77)]
def childrenD_376_i0 : Fin 2 → Finset Cell := ![(placed21 3 (2, 4) envelope_2), (placed21 5 (4, 0) envelope_77)]
theorem common_sub_376_i0 : commonEnvelope childrenD_376_i0 ⊆ insert (2, 4) required_376_i0 := by decide +kernel
theorem child_required_sub_376_i0 : ∀ j, childrenC_376_i0 j ⊆ insert (2, 4) required_376_i0 := by decide +kernel
theorem child_envelope_sub_376_i0 : ∀ j, childrenD_376_i0 j ⊆ envelope_376_i0 := by decide +kernel
theorem pivot_mem_376_i0 : (2, 4) ∈ envelope_376_i0 := by decide +kernel
theorem children_work_376_i0 : ∀ j, Template HasSnaky 2 (childrenC_376_i0 j) (childrenD_376_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 3 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_77 5 (4, 0)).mono (by decide +kernel)
theorem row_works_376_i0 : Template HasSnaky 3 required_376_i0 envelope_376_i0 := by
  refine compose HasSnaky 2 childrenC_376_i0 childrenD_376_i0 children_work_376_i0 (2, 4)
    required_376_i0 envelope_376_i0 pivot_mem_376_i0 child_required_sub_376_i0 child_envelope_sub_376_i0 ?_
  intro b hb
  exact common_sub_376_i0 (mem_commonEnvelope childrenD_376_i0 b hb)
def required_376 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 3), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_376 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_376 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) required_5), required_376_i0]
def childrenD_376 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) envelope_5), envelope_376_i0]
theorem common_sub_376 : commonEnvelope childrenD_376 ⊆ insert (3, 0) required_376 := by decide +kernel
theorem child_required_sub_376 : ∀ j, childrenC_376 j ⊆ insert (3, 0) required_376 := by decide +kernel
theorem child_envelope_sub_376 : ∀ j, childrenD_376 j ⊆ envelope_376 := by decide +kernel
theorem pivot_mem_376 : (3, 0) ∈ envelope_376 := by decide +kernel
theorem children_work_376 : ∀ j, Template HasSnaky 3 (childrenC_376 j) (childrenD_376 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact row_works_376_i0.mono (by decide +kernel)
theorem row_works_376 : Template HasSnaky 4 required_376 envelope_376 := by
  refine compose HasSnaky 3 childrenC_376 childrenD_376 children_work_376 (3, 0)
    required_376 envelope_376 pivot_mem_376 child_required_sub_376 child_envelope_sub_376 ?_
  intro b hb
  exact common_sub_376 (mem_commonEnvelope childrenD_376 b hb)
def height_268 : ℕ := 4
def childrenH_268 : Fin 3 → ℕ := ![height_7, height_8, height_9]
theorem height_exact_268 : height_268 = 1 + Finset.univ.sup childrenH_268 := by decide +kernel
theorem required_origin_268 : ∀ x ∈ required_268,
    (∃ j, x ∈ childrenC_268 j) ∨ ∀ j, x ∈ childrenD_268 j := by decide +kernel
theorem required_exact_268 : required_268 =
    ((Finset.univ.biUnion childrenC_268) ∪ commonEnvelope childrenD_268).erase (1, 4) := by
  exact required_eq_combination childrenC_268 childrenD_268 (1, 4) required_268
    (by decide +kernel) child_required_sub_268 common_sub_268 required_origin_268
theorem envelope_origin_268 : ∀ x ∈ envelope_268,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_268 j := by decide +kernel
theorem envelope_exact_268 : envelope_268 =
    insert (1, 4) (Finset.univ.biUnion childrenD_268) := by
  exact envelope_eq_combination childrenD_268 (1, 4) envelope_268
    pivot_mem_268 child_envelope_sub_268 envelope_origin_268
def checked_268 : CheckedCard where
  required := required_268
  envelope := envelope_268
  height := height_268
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_268
def height_269 : ℕ := 4
def childrenH_269 : Fin 2 → ℕ := ![height_7, height_21]
theorem height_exact_269 : height_269 = 1 + Finset.univ.sup childrenH_269 := by decide +kernel
theorem required_origin_269 : ∀ x ∈ required_269,
    (∃ j, x ∈ childrenC_269 j) ∨ ∀ j, x ∈ childrenD_269 j := by decide +kernel
theorem required_exact_269 : required_269 =
    ((Finset.univ.biUnion childrenC_269) ∪ commonEnvelope childrenD_269).erase (1, 5) := by
  exact required_eq_combination childrenC_269 childrenD_269 (1, 5) required_269
    (by decide +kernel) child_required_sub_269 common_sub_269 required_origin_269
theorem envelope_origin_269 : ∀ x ∈ envelope_269,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_269 j := by decide +kernel
theorem envelope_exact_269 : envelope_269 =
    insert (1, 5) (Finset.univ.biUnion childrenD_269) := by
  exact envelope_eq_combination childrenD_269 (1, 5) envelope_269
    pivot_mem_269 child_envelope_sub_269 envelope_origin_269
def checked_269 : CheckedCard where
  required := required_269
  envelope := envelope_269
  height := height_269
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_269
def height_271 : ℕ := 4
def childrenH_271 : Fin 2 → ℕ := ![height_5, height_52]
theorem height_exact_271 : height_271 = 1 + Finset.univ.sup childrenH_271 := by decide +kernel
theorem required_origin_271 : ∀ x ∈ required_271,
    (∃ j, x ∈ childrenC_271 j) ∨ ∀ j, x ∈ childrenD_271 j := by decide +kernel
theorem required_exact_271 : required_271 =
    ((Finset.univ.biUnion childrenC_271) ∪ commonEnvelope childrenD_271).erase (2, 3) := by
  exact required_eq_combination childrenC_271 childrenD_271 (2, 3) required_271
    (by decide +kernel) child_required_sub_271 common_sub_271 required_origin_271
theorem envelope_origin_271 : ∀ x ∈ envelope_271,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_271 j := by decide +kernel
theorem envelope_exact_271 : envelope_271 =
    insert (2, 3) (Finset.univ.biUnion childrenD_271) := by
  exact envelope_eq_combination childrenD_271 (2, 3) envelope_271
    pivot_mem_271 child_envelope_sub_271 envelope_origin_271
def checked_271 : CheckedCard where
  required := required_271
  envelope := envelope_271
  height := height_271
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_271
def height_277 : ℕ := 4
def childrenH_277 : Fin 2 → ℕ := ![height_0, height_69]
theorem height_exact_277 : height_277 = 1 + Finset.univ.sup childrenH_277 := by decide +kernel
theorem required_origin_277 : ∀ x ∈ required_277,
    (∃ j, x ∈ childrenC_277 j) ∨ ∀ j, x ∈ childrenD_277 j := by decide +kernel
theorem required_exact_277 : required_277 =
    ((Finset.univ.biUnion childrenC_277) ∪ commonEnvelope childrenD_277).erase (1, 3) := by
  exact required_eq_combination childrenC_277 childrenD_277 (1, 3) required_277
    (by decide +kernel) child_required_sub_277 common_sub_277 required_origin_277
theorem envelope_origin_277 : ∀ x ∈ envelope_277,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_277 j := by decide +kernel
theorem envelope_exact_277 : envelope_277 =
    insert (1, 3) (Finset.univ.biUnion childrenD_277) := by
  exact envelope_eq_combination childrenD_277 (1, 3) envelope_277
    pivot_mem_277 child_envelope_sub_277 envelope_origin_277
def checked_277 : CheckedCard where
  required := required_277
  envelope := envelope_277
  height := height_277
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_277
def height_288 : ℕ := 4
def childrenH_288 : Fin 2 → ℕ := ![height_54, height_68]
theorem height_exact_288 : height_288 = 1 + Finset.univ.sup childrenH_288 := by decide +kernel
theorem required_origin_288 : ∀ x ∈ required_288,
    (∃ j, x ∈ childrenC_288 j) ∨ ∀ j, x ∈ childrenD_288 j := by decide +kernel
theorem required_exact_288 : required_288 =
    ((Finset.univ.biUnion childrenC_288) ∪ commonEnvelope childrenD_288).erase (1, 5) := by
  exact required_eq_combination childrenC_288 childrenD_288 (1, 5) required_288
    (by decide +kernel) child_required_sub_288 common_sub_288 required_origin_288
theorem envelope_origin_288 : ∀ x ∈ envelope_288,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_288 j := by decide +kernel
theorem envelope_exact_288 : envelope_288 =
    insert (1, 5) (Finset.univ.biUnion childrenD_288) := by
  exact envelope_eq_combination childrenD_288 (1, 5) envelope_288
    pivot_mem_288 child_envelope_sub_288 envelope_origin_288
def checked_288 : CheckedCard where
  required := required_288
  envelope := envelope_288
  height := height_288
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_288
def height_289 : ℕ := 4
def childrenH_289 : Fin 3 → ℕ := ![height_22, height_28, height_126]
theorem height_exact_289 : height_289 = 1 + Finset.univ.sup childrenH_289 := by decide +kernel
theorem required_origin_289 : ∀ x ∈ required_289,
    (∃ j, x ∈ childrenC_289 j) ∨ ∀ j, x ∈ childrenD_289 j := by decide +kernel
theorem required_exact_289 : required_289 =
    ((Finset.univ.biUnion childrenC_289) ∪ commonEnvelope childrenD_289).erase (1, 2) := by
  exact required_eq_combination childrenC_289 childrenD_289 (1, 2) required_289
    (by decide +kernel) child_required_sub_289 common_sub_289 required_origin_289
theorem envelope_origin_289 : ∀ x ∈ envelope_289,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_289 j := by decide +kernel
theorem envelope_exact_289 : envelope_289 =
    insert (1, 2) (Finset.univ.biUnion childrenD_289) := by
  exact envelope_eq_combination childrenD_289 (1, 2) envelope_289
    pivot_mem_289 child_envelope_sub_289 envelope_origin_289
def checked_289 : CheckedCard where
  required := required_289
  envelope := envelope_289
  height := height_289
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_289
def height_291 : ℕ := 4
def childrenH_291 : Fin 2 → ℕ := ![height_7, height_25]
theorem height_exact_291 : height_291 = 1 + Finset.univ.sup childrenH_291 := by decide +kernel
theorem required_origin_291 : ∀ x ∈ required_291,
    (∃ j, x ∈ childrenC_291 j) ∨ ∀ j, x ∈ childrenD_291 j := by decide +kernel
theorem required_exact_291 : required_291 =
    ((Finset.univ.biUnion childrenC_291) ∪ commonEnvelope childrenD_291).erase (3, 4) := by
  exact required_eq_combination childrenC_291 childrenD_291 (3, 4) required_291
    (by decide +kernel) child_required_sub_291 common_sub_291 required_origin_291
theorem envelope_origin_291 : ∀ x ∈ envelope_291,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_291 j := by decide +kernel
theorem envelope_exact_291 : envelope_291 =
    insert (3, 4) (Finset.univ.biUnion childrenD_291) := by
  exact envelope_eq_combination childrenD_291 (3, 4) envelope_291
    pivot_mem_291 child_envelope_sub_291 envelope_origin_291
def checked_291 : CheckedCard where
  required := required_291
  envelope := envelope_291
  height := height_291
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_291
def height_304 : ℕ := 4
def childrenH_304 : Fin 3 → ℕ := ![height_7, height_8, height_9]
theorem height_exact_304 : height_304 = 1 + Finset.univ.sup childrenH_304 := by decide +kernel
theorem required_origin_304 : ∀ x ∈ required_304,
    (∃ j, x ∈ childrenC_304 j) ∨ ∀ j, x ∈ childrenD_304 j := by decide +kernel
theorem required_exact_304 : required_304 =
    ((Finset.univ.biUnion childrenC_304) ∪ commonEnvelope childrenD_304).erase (1, 4) := by
  exact required_eq_combination childrenC_304 childrenD_304 (1, 4) required_304
    (by decide +kernel) child_required_sub_304 common_sub_304 required_origin_304
theorem envelope_origin_304 : ∀ x ∈ envelope_304,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_304 j := by decide +kernel
theorem envelope_exact_304 : envelope_304 =
    insert (1, 4) (Finset.univ.biUnion childrenD_304) := by
  exact envelope_eq_combination childrenD_304 (1, 4) envelope_304
    pivot_mem_304 child_envelope_sub_304 envelope_origin_304
def checked_304 : CheckedCard where
  required := required_304
  envelope := envelope_304
  height := height_304
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_304
def height_305 : ℕ := 4
def childrenH_305 : Fin 2 → ℕ := ![height_5, height_124]
theorem height_exact_305 : height_305 = 1 + Finset.univ.sup childrenH_305 := by decide +kernel
theorem required_origin_305 : ∀ x ∈ required_305,
    (∃ j, x ∈ childrenC_305 j) ∨ ∀ j, x ∈ childrenD_305 j := by decide +kernel
theorem required_exact_305 : required_305 =
    ((Finset.univ.biUnion childrenC_305) ∪ commonEnvelope childrenD_305).erase (1, 3) := by
  exact required_eq_combination childrenC_305 childrenD_305 (1, 3) required_305
    (by decide +kernel) child_required_sub_305 common_sub_305 required_origin_305
theorem envelope_origin_305 : ∀ x ∈ envelope_305,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_305 j := by decide +kernel
theorem envelope_exact_305 : envelope_305 =
    insert (1, 3) (Finset.univ.biUnion childrenD_305) := by
  exact envelope_eq_combination childrenD_305 (1, 3) envelope_305
    pivot_mem_305 child_envelope_sub_305 envelope_origin_305
def checked_305 : CheckedCard where
  required := required_305
  envelope := envelope_305
  height := height_305
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_305
def height_307 : ℕ := 4
def childrenH_307 : Fin 2 → ℕ := ![height_5, height_131]
theorem height_exact_307 : height_307 = 1 + Finset.univ.sup childrenH_307 := by decide +kernel
theorem required_origin_307 : ∀ x ∈ required_307,
    (∃ j, x ∈ childrenC_307 j) ∨ ∀ j, x ∈ childrenD_307 j := by decide +kernel
theorem required_exact_307 : required_307 =
    ((Finset.univ.biUnion childrenC_307) ∪ commonEnvelope childrenD_307).erase (4, 2) := by
  exact required_eq_combination childrenC_307 childrenD_307 (4, 2) required_307
    (by decide +kernel) child_required_sub_307 common_sub_307 required_origin_307
theorem envelope_origin_307 : ∀ x ∈ envelope_307,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_307 j := by decide +kernel
theorem envelope_exact_307 : envelope_307 =
    insert (4, 2) (Finset.univ.biUnion childrenD_307) := by
  exact envelope_eq_combination childrenD_307 (4, 2) envelope_307
    pivot_mem_307 child_envelope_sub_307 envelope_origin_307
def checked_307 : CheckedCard where
  required := required_307
  envelope := envelope_307
  height := height_307
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_307
def height_311_i0 : ℕ := 3
def childrenH_311_i0 : Fin 2 → ℕ := ![height_5, height_6]
theorem height_exact_311_i0 : height_311_i0 = 1 + Finset.univ.sup childrenH_311_i0 := by decide +kernel
theorem required_origin_311_i0 : ∀ x ∈ required_311_i0,
    (∃ j, x ∈ childrenC_311_i0 j) ∨ ∀ j, x ∈ childrenD_311_i0 j := by decide +kernel
theorem required_exact_311_i0 : required_311_i0 =
    ((Finset.univ.biUnion childrenC_311_i0) ∪ commonEnvelope childrenD_311_i0).erase (4, 1) := by
  exact required_eq_combination childrenC_311_i0 childrenD_311_i0 (4, 1) required_311_i0
    (by decide +kernel) child_required_sub_311_i0 common_sub_311_i0 required_origin_311_i0
theorem envelope_origin_311_i0 : ∀ x ∈ envelope_311_i0,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_311_i0 j := by decide +kernel
theorem envelope_exact_311_i0 : envelope_311_i0 =
    insert (4, 1) (Finset.univ.biUnion childrenD_311_i0) := by
  exact envelope_eq_combination childrenD_311_i0 (4, 1) envelope_311_i0
    pivot_mem_311_i0 child_envelope_sub_311_i0 envelope_origin_311_i0
def checked_311_i0 : CheckedCard where
  required := required_311_i0
  envelope := envelope_311_i0
  height := height_311_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_311_i0
def height_311 : ℕ := 4
def childrenH_311 : Fin 2 → ℕ := ![height_4, height_311_i0]
theorem height_exact_311 : height_311 = 1 + Finset.univ.sup childrenH_311 := by decide +kernel
theorem required_origin_311 : ∀ x ∈ required_311,
    (∃ j, x ∈ childrenC_311 j) ∨ ∀ j, x ∈ childrenD_311 j := by decide +kernel
theorem required_exact_311 : required_311 =
    ((Finset.univ.biUnion childrenC_311) ∪ commonEnvelope childrenD_311).erase (3, 1) := by
  exact required_eq_combination childrenC_311 childrenD_311 (3, 1) required_311
    (by decide +kernel) child_required_sub_311 common_sub_311 required_origin_311
theorem envelope_origin_311 : ∀ x ∈ envelope_311,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_311 j := by decide +kernel
theorem envelope_exact_311 : envelope_311 =
    insert (3, 1) (Finset.univ.biUnion childrenD_311) := by
  exact envelope_eq_combination childrenD_311 (3, 1) envelope_311
    pivot_mem_311 child_envelope_sub_311 envelope_origin_311
def checked_311 : CheckedCard where
  required := required_311
  envelope := envelope_311
  height := height_311
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_311
def height_334 : ℕ := 4
def childrenH_334 : Fin 4 → ℕ := ![height_101, height_101, height_333, height_333]
theorem height_exact_334 : height_334 = 1 + Finset.univ.sup childrenH_334 := by decide +kernel
theorem required_origin_334 : ∀ x ∈ required_334,
    (∃ j, x ∈ childrenC_334 j) ∨ ∀ j, x ∈ childrenD_334 j := by decide +kernel
theorem required_exact_334 : required_334 =
    ((Finset.univ.biUnion childrenC_334) ∪ commonEnvelope childrenD_334).erase (1, 5) := by
  exact required_eq_combination childrenC_334 childrenD_334 (1, 5) required_334
    (by decide +kernel) child_required_sub_334 common_sub_334 required_origin_334
theorem envelope_origin_334 : ∀ x ∈ envelope_334,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_334 j := by decide +kernel
theorem envelope_exact_334 : envelope_334 =
    insert (1, 5) (Finset.univ.biUnion childrenD_334) := by
  exact envelope_eq_combination childrenD_334 (1, 5) envelope_334
    pivot_mem_334 child_envelope_sub_334 envelope_origin_334
def checked_334 : CheckedCard where
  required := required_334
  envelope := envelope_334
  height := height_334
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_334
def height_351 : ℕ := 4
def childrenH_351 : Fin 2 → ℕ := ![height_5, height_350]
theorem height_exact_351 : height_351 = 1 + Finset.univ.sup childrenH_351 := by decide +kernel
theorem required_origin_351 : ∀ x ∈ required_351,
    (∃ j, x ∈ childrenC_351 j) ∨ ∀ j, x ∈ childrenD_351 j := by decide +kernel
theorem required_exact_351 : required_351 =
    ((Finset.univ.biUnion childrenC_351) ∪ commonEnvelope childrenD_351).erase (3, 1) := by
  exact required_eq_combination childrenC_351 childrenD_351 (3, 1) required_351
    (by decide +kernel) child_required_sub_351 common_sub_351 required_origin_351
theorem envelope_origin_351 : ∀ x ∈ envelope_351,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_351 j := by decide +kernel
theorem envelope_exact_351 : envelope_351 =
    insert (3, 1) (Finset.univ.biUnion childrenD_351) := by
  exact envelope_eq_combination childrenD_351 (3, 1) envelope_351
    pivot_mem_351 child_envelope_sub_351 envelope_origin_351
def checked_351 : CheckedCard where
  required := required_351
  envelope := envelope_351
  height := height_351
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_351
def height_354_i0 : ℕ := 3
def childrenH_354_i0 : Fin 2 → ℕ := ![height_5, height_70]
theorem height_exact_354_i0 : height_354_i0 = 1 + Finset.univ.sup childrenH_354_i0 := by decide +kernel
theorem required_origin_354_i0 : ∀ x ∈ required_354_i0,
    (∃ j, x ∈ childrenC_354_i0 j) ∨ ∀ j, x ∈ childrenD_354_i0 j := by decide +kernel
theorem required_exact_354_i0 : required_354_i0 =
    ((Finset.univ.biUnion childrenC_354_i0) ∪ commonEnvelope childrenD_354_i0).erase (3, 2) := by
  exact required_eq_combination childrenC_354_i0 childrenD_354_i0 (3, 2) required_354_i0
    (by decide +kernel) child_required_sub_354_i0 common_sub_354_i0 required_origin_354_i0
theorem envelope_origin_354_i0 : ∀ x ∈ envelope_354_i0,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_354_i0 j := by decide +kernel
theorem envelope_exact_354_i0 : envelope_354_i0 =
    insert (3, 2) (Finset.univ.biUnion childrenD_354_i0) := by
  exact envelope_eq_combination childrenD_354_i0 (3, 2) envelope_354_i0
    pivot_mem_354_i0 child_envelope_sub_354_i0 envelope_origin_354_i0
def checked_354_i0 : CheckedCard where
  required := required_354_i0
  envelope := envelope_354_i0
  height := height_354_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_354_i0
def height_354 : ℕ := 4
def childrenH_354 : Fin 2 → ℕ := ![height_5, height_354_i0]
theorem height_exact_354 : height_354 = 1 + Finset.univ.sup childrenH_354 := by decide +kernel
theorem required_origin_354 : ∀ x ∈ required_354,
    (∃ j, x ∈ childrenC_354 j) ∨ ∀ j, x ∈ childrenD_354 j := by decide +kernel
theorem required_exact_354 : required_354 =
    ((Finset.univ.biUnion childrenC_354) ∪ commonEnvelope childrenD_354).erase (3, 0) := by
  exact required_eq_combination childrenC_354 childrenD_354 (3, 0) required_354
    (by decide +kernel) child_required_sub_354 common_sub_354 required_origin_354
theorem envelope_origin_354 : ∀ x ∈ envelope_354,
    x = (3, 0) ∨ ∃ j, x ∈ childrenD_354 j := by decide +kernel
theorem envelope_exact_354 : envelope_354 =
    insert (3, 0) (Finset.univ.biUnion childrenD_354) := by
  exact envelope_eq_combination childrenD_354 (3, 0) envelope_354
    pivot_mem_354 child_envelope_sub_354 envelope_origin_354
def checked_354 : CheckedCard where
  required := required_354
  envelope := envelope_354
  height := height_354
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_354
def height_365_i1 : ℕ := 2
def childrenH_365_i1 : Fin 2 → ℕ := ![height_0, height_0]
theorem height_exact_365_i1 : height_365_i1 = 1 + Finset.univ.sup childrenH_365_i1 := by decide +kernel
theorem required_origin_365_i1 : ∀ x ∈ required_365_i1,
    (∃ j, x ∈ childrenC_365_i1 j) ∨ ∀ j, x ∈ childrenD_365_i1 j := by decide +kernel
theorem required_exact_365_i1 : required_365_i1 =
    ((Finset.univ.biUnion childrenC_365_i1) ∪ commonEnvelope childrenD_365_i1).erase (0, 4) := by
  exact required_eq_combination childrenC_365_i1 childrenD_365_i1 (0, 4) required_365_i1
    (by decide +kernel) child_required_sub_365_i1 common_sub_365_i1 required_origin_365_i1
theorem envelope_origin_365_i1 : ∀ x ∈ envelope_365_i1,
    x = (0, 4) ∨ ∃ j, x ∈ childrenD_365_i1 j := by decide +kernel
theorem envelope_exact_365_i1 : envelope_365_i1 =
    insert (0, 4) (Finset.univ.biUnion childrenD_365_i1) := by
  exact envelope_eq_combination childrenD_365_i1 (0, 4) envelope_365_i1
    pivot_mem_365_i1 child_envelope_sub_365_i1 envelope_origin_365_i1
def checked_365_i1 : CheckedCard where
  required := required_365_i1
  envelope := envelope_365_i1
  height := height_365_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_365_i1
def height_365_i0 : ℕ := 3
def childrenH_365_i0 : Fin 2 → ℕ := ![height_5, height_365_i1]
theorem height_exact_365_i0 : height_365_i0 = 1 + Finset.univ.sup childrenH_365_i0 := by decide +kernel
theorem required_origin_365_i0 : ∀ x ∈ required_365_i0,
    (∃ j, x ∈ childrenC_365_i0 j) ∨ ∀ j, x ∈ childrenD_365_i0 j := by decide +kernel
theorem required_exact_365_i0 : required_365_i0 =
    ((Finset.univ.biUnion childrenC_365_i0) ∪ commonEnvelope childrenD_365_i0).erase (0, 3) := by
  exact required_eq_combination childrenC_365_i0 childrenD_365_i0 (0, 3) required_365_i0
    (by decide +kernel) child_required_sub_365_i0 common_sub_365_i0 required_origin_365_i0
theorem envelope_origin_365_i0 : ∀ x ∈ envelope_365_i0,
    x = (0, 3) ∨ ∃ j, x ∈ childrenD_365_i0 j := by decide +kernel
theorem envelope_exact_365_i0 : envelope_365_i0 =
    insert (0, 3) (Finset.univ.biUnion childrenD_365_i0) := by
  exact envelope_eq_combination childrenD_365_i0 (0, 3) envelope_365_i0
    pivot_mem_365_i0 child_envelope_sub_365_i0 envelope_origin_365_i0
def checked_365_i0 : CheckedCard where
  required := required_365_i0
  envelope := envelope_365_i0
  height := height_365_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_365_i0
def height_365 : ℕ := 4
def childrenH_365 : Fin 2 → ℕ := ![height_6, height_365_i0]
theorem height_exact_365 : height_365 = 1 + Finset.univ.sup childrenH_365 := by decide +kernel
theorem required_origin_365 : ∀ x ∈ required_365,
    (∃ j, x ∈ childrenC_365 j) ∨ ∀ j, x ∈ childrenD_365 j := by decide +kernel
theorem required_exact_365 : required_365 =
    ((Finset.univ.biUnion childrenC_365) ∪ commonEnvelope childrenD_365).erase (1, 6) := by
  exact required_eq_combination childrenC_365 childrenD_365 (1, 6) required_365
    (by decide +kernel) child_required_sub_365 common_sub_365 required_origin_365
theorem envelope_origin_365 : ∀ x ∈ envelope_365,
    x = (1, 6) ∨ ∃ j, x ∈ childrenD_365 j := by decide +kernel
theorem envelope_exact_365 : envelope_365 =
    insert (1, 6) (Finset.univ.biUnion childrenD_365) := by
  exact envelope_eq_combination childrenD_365 (1, 6) envelope_365
    pivot_mem_365 child_envelope_sub_365 envelope_origin_365
def checked_365 : CheckedCard where
  required := required_365
  envelope := envelope_365
  height := height_365
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_365
def height_375 : ℕ := 4
def childrenH_375 : Fin 2 → ℕ := ![height_5, height_374]
theorem height_exact_375 : height_375 = 1 + Finset.univ.sup childrenH_375 := by decide +kernel
theorem required_origin_375 : ∀ x ∈ required_375,
    (∃ j, x ∈ childrenC_375 j) ∨ ∀ j, x ∈ childrenD_375 j := by decide +kernel
theorem required_exact_375 : required_375 =
    ((Finset.univ.biUnion childrenC_375) ∪ commonEnvelope childrenD_375).erase (3, 1) := by
  exact required_eq_combination childrenC_375 childrenD_375 (3, 1) required_375
    (by decide +kernel) child_required_sub_375 common_sub_375 required_origin_375
theorem envelope_origin_375 : ∀ x ∈ envelope_375,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_375 j := by decide +kernel
theorem envelope_exact_375 : envelope_375 =
    insert (3, 1) (Finset.univ.biUnion childrenD_375) := by
  exact envelope_eq_combination childrenD_375 (3, 1) envelope_375
    pivot_mem_375 child_envelope_sub_375 envelope_origin_375
def checked_375 : CheckedCard where
  required := required_375
  envelope := envelope_375
  height := height_375
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_375
def height_376_i0 : ℕ := 3
def childrenH_376_i0 : Fin 2 → ℕ := ![height_2, height_77]
theorem height_exact_376_i0 : height_376_i0 = 1 + Finset.univ.sup childrenH_376_i0 := by decide +kernel
theorem required_origin_376_i0 : ∀ x ∈ required_376_i0,
    (∃ j, x ∈ childrenC_376_i0 j) ∨ ∀ j, x ∈ childrenD_376_i0 j := by decide +kernel
theorem required_exact_376_i0 : required_376_i0 =
    ((Finset.univ.biUnion childrenC_376_i0) ∪ commonEnvelope childrenD_376_i0).erase (2, 4) := by
  exact required_eq_combination childrenC_376_i0 childrenD_376_i0 (2, 4) required_376_i0
    (by decide +kernel) child_required_sub_376_i0 common_sub_376_i0 required_origin_376_i0
theorem envelope_origin_376_i0 : ∀ x ∈ envelope_376_i0,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_376_i0 j := by decide +kernel
theorem envelope_exact_376_i0 : envelope_376_i0 =
    insert (2, 4) (Finset.univ.biUnion childrenD_376_i0) := by
  exact envelope_eq_combination childrenD_376_i0 (2, 4) envelope_376_i0
    pivot_mem_376_i0 child_envelope_sub_376_i0 envelope_origin_376_i0
def checked_376_i0 : CheckedCard where
  required := required_376_i0
  envelope := envelope_376_i0
  height := height_376_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_376_i0
def height_376 : ℕ := 4
def childrenH_376 : Fin 2 → ℕ := ![height_5, height_376_i0]
theorem height_exact_376 : height_376 = 1 + Finset.univ.sup childrenH_376 := by decide +kernel
theorem required_origin_376 : ∀ x ∈ required_376,
    (∃ j, x ∈ childrenC_376 j) ∨ ∀ j, x ∈ childrenD_376 j := by decide +kernel
theorem required_exact_376 : required_376 =
    ((Finset.univ.biUnion childrenC_376) ∪ commonEnvelope childrenD_376).erase (3, 0) := by
  exact required_eq_combination childrenC_376 childrenD_376 (3, 0) required_376
    (by decide +kernel) child_required_sub_376 common_sub_376 required_origin_376
theorem envelope_origin_376 : ∀ x ∈ envelope_376,
    x = (3, 0) ∨ ∃ j, x ∈ childrenD_376 j := by decide +kernel
theorem envelope_exact_376 : envelope_376 =
    insert (3, 0) (Finset.univ.biUnion childrenD_376) := by
  exact envelope_eq_combination childrenD_376 (3, 0) envelope_376
    pivot_mem_376 child_envelope_sub_376 envelope_origin_376
def checked_376 : CheckedCard where
  required := required_376
  envelope := envelope_376
  height := height_376
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_376
end SnakyPrototype.Certificate21

end OAI
