import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_272 : Finset Cell := ⟨(([(0, 1), (1, 1), (3, 1), (3, 2), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_272 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 2), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_272 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_5), (placed21 0 (2, 0) required_39)]
def childrenD_272 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_5), (placed21 0 (2, 0) envelope_39)]
theorem common_sub_272 : commonEnvelope childrenD_272 ⊆ insert (2, 1) required_272 := by decide +kernel
theorem child_required_sub_272 : ∀ j, childrenC_272 j ⊆ insert (2, 1) required_272 := by decide +kernel
theorem child_envelope_sub_272 : ∀ j, childrenD_272 j ⊆ envelope_272 := by decide +kernel
theorem pivot_mem_272 : (2, 1) ∈ envelope_272 := by decide +kernel
theorem children_work_272 : ∀ j, Template HasSnaky 4 (childrenC_272 j) (childrenD_272 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_39 0 (2, 0)).mono (by decide +kernel)
theorem row_works_272 : Template HasSnaky 5 required_272 envelope_272 := by
  refine compose HasSnaky 4 childrenC_272 childrenD_272 children_work_272 (2, 1)
    required_272 envelope_272 pivot_mem_272 child_required_sub_272 child_envelope_sub_272 ?_
  intro b hb
  exact common_sub_272 (mem_commonEnvelope childrenD_272 b hb)
def required_273 : Finset Cell := ⟨(([(0, 3), (1, 3), (3, 4), (4, 2), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_273 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_273 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) required_2), (placed21 0 (3, 0) required_206)]
def childrenD_273 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) envelope_2), (placed21 0 (3, 0) envelope_206)]
theorem common_sub_273 : commonEnvelope childrenD_273 ⊆ insert (3, 3) required_273 := by decide +kernel
theorem child_required_sub_273 : ∀ j, childrenC_273 j ⊆ insert (3, 3) required_273 := by decide +kernel
theorem child_envelope_sub_273 : ∀ j, childrenD_273 j ⊆ envelope_273 := by decide +kernel
theorem pivot_mem_273 : (3, 3) ∈ envelope_273 := by decide +kernel
theorem children_work_273 : ∀ j, Template HasSnaky 4 (childrenC_273 j) (childrenD_273 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 0 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_206 0 (3, 0)).mono (by decide +kernel)
theorem row_works_273 : Template HasSnaky 5 required_273 envelope_273 := by
  refine compose HasSnaky 4 childrenC_273 childrenD_273 children_work_273 (3, 3)
    required_273 envelope_273 pivot_mem_273 child_required_sub_273 child_envelope_sub_273 ?_
  intro b hb
  exact common_sub_273 (mem_commonEnvelope childrenD_273 b hb)
def required_274 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_274 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_274 : Fin 3 → Finset Cell := ![(placed21 0 (2, 0) required_13), (placed21 3 (0, 3) required_44), (placed21 5 (4, 2) required_83)]
def childrenD_274 : Fin 3 → Finset Cell := ![(placed21 0 (2, 0) envelope_13), (placed21 3 (0, 3) envelope_44), (placed21 5 (4, 2) envelope_83)]
theorem common_sub_274 : commonEnvelope childrenD_274 ⊆ insert (3, 2) required_274 := by decide +kernel
theorem child_required_sub_274 : ∀ j, childrenC_274 j ⊆ insert (3, 2) required_274 := by decide +kernel
theorem child_envelope_sub_274 : ∀ j, childrenD_274 j ⊆ envelope_274 := by decide +kernel
theorem pivot_mem_274 : (3, 2) ∈ envelope_274 := by decide +kernel
theorem children_work_274 : ∀ j, Template HasSnaky 4 (childrenC_274 j) (childrenD_274 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 0 (2, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_44 3 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_83 5 (4, 2)).mono (by decide +kernel)
theorem row_works_274 : Template HasSnaky 5 required_274 envelope_274 := by
  refine compose HasSnaky 4 childrenC_274 childrenD_274 children_work_274 (3, 2)
    required_274 envelope_274 pivot_mem_274 child_required_sub_274 child_envelope_sub_274 ?_
  intro b hb
  exact common_sub_274 (mem_commonEnvelope childrenD_274 b hb)
def required_278 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (2, 3), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_278 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4), (2, 5), (3, 1), (3, 2), (4, 1), (4, 2), (5, 1), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_278 : Fin 2 → Finset Cell := ![(placed21 3 (0, 2) required_6), required_277]
def childrenD_278 : Fin 2 → Finset Cell := ![(placed21 3 (0, 2) envelope_6), envelope_277]
theorem common_sub_278 : commonEnvelope childrenD_278 ⊆ insert (4, 2) required_278 := by decide +kernel
theorem child_required_sub_278 : ∀ j, childrenC_278 j ⊆ insert (4, 2) required_278 := by decide +kernel
theorem child_envelope_sub_278 : ∀ j, childrenD_278 j ⊆ envelope_278 := by decide +kernel
theorem pivot_mem_278 : (4, 2) ∈ envelope_278 := by decide +kernel
theorem children_work_278 : ∀ j, Template HasSnaky 4 (childrenC_278 j) (childrenD_278 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 3 (0, 2)).mono (by decide +kernel)
  · exact row_works_277.mono (by decide +kernel)
theorem row_works_278 : Template HasSnaky 5 required_278 envelope_278 := by
  refine compose HasSnaky 4 childrenC_278 childrenD_278 children_work_278 (4, 2)
    required_278 envelope_278 pivot_mem_278 child_required_sub_278 child_envelope_sub_278 ?_
  intro b hb
  exact common_sub_278 (mem_commonEnvelope childrenD_278 b hb)
def required_279 : Finset Cell := ⟨(([(0, 3), (1, 2), (1, 3), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_279 : Finset Cell := ⟨(([(0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 2), (3, 3), (4, 2), (4, 3), (5, 2), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_279 : Fin 2 → Finset Cell := ![(placed21 3 (0, 3) required_6), (placed21 0 (1, 0) required_141)]
def childrenD_279 : Fin 2 → Finset Cell := ![(placed21 3 (0, 3) envelope_6), (placed21 0 (1, 0) envelope_141)]
theorem common_sub_279 : commonEnvelope childrenD_279 ⊆ insert (4, 3) required_279 := by decide +kernel
theorem child_required_sub_279 : ∀ j, childrenC_279 j ⊆ insert (4, 3) required_279 := by decide +kernel
theorem child_envelope_sub_279 : ∀ j, childrenD_279 j ⊆ envelope_279 := by decide +kernel
theorem pivot_mem_279 : (4, 3) ∈ envelope_279 := by decide +kernel
theorem children_work_279 : ∀ j, Template HasSnaky 4 (childrenC_279 j) (childrenD_279 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 3 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_141 0 (1, 0)).mono (by decide +kernel)
theorem row_works_279 : Template HasSnaky 5 required_279 envelope_279 := by
  refine compose HasSnaky 4 childrenC_279 childrenD_279 children_work_279 (4, 3)
    required_279 envelope_279 pivot_mem_279 child_required_sub_279 child_envelope_sub_279 ?_
  intro b hb
  exact common_sub_279 (mem_commonEnvelope childrenD_279 b hb)
def required_282 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 2), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_282 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (4, 1), (4, 2), (4, 3), (5, 1), (5, 2), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_282 : Fin 3 → Finset Cell := ![(placed21 3 (0, 3) required_20), (placed21 1 (0, 2) required_29), required_92]
def childrenD_282 : Fin 3 → Finset Cell := ![(placed21 3 (0, 3) envelope_20), (placed21 1 (0, 2) envelope_29), envelope_92]
theorem common_sub_282 : commonEnvelope childrenD_282 ⊆ insert (3, 2) required_282 := by decide +kernel
theorem child_required_sub_282 : ∀ j, childrenC_282 j ⊆ insert (3, 2) required_282 := by decide +kernel
theorem child_envelope_sub_282 : ∀ j, childrenD_282 j ⊆ envelope_282 := by decide +kernel
theorem pivot_mem_282 : (3, 2) ∈ envelope_282 := by decide +kernel
theorem children_work_282 : ∀ j, Template HasSnaky 4 (childrenC_282 j) (childrenD_282 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_20 3 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_29 1 (0, 2)).mono (by decide +kernel)
  · exact row_works_92.mono (by decide +kernel)
theorem row_works_282 : Template HasSnaky 5 required_282 envelope_282 := by
  refine compose HasSnaky 4 childrenC_282 childrenD_282 children_work_282 (3, 2)
    required_282 envelope_282 pivot_mem_282 child_required_sub_282 child_envelope_sub_282 ?_
  intro b hb
  exact common_sub_282 (mem_commonEnvelope childrenD_282 b hb)
def required_293 : Finset Cell := ⟨(([(1, 3), (2, 2), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_293 : Finset Cell := ⟨(([(0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (3, 2), (3, 3), (4, 3), (4, 4), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4), (7, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_293 : Fin 2 → Finset Cell := ![(placed21 1 (1, 2) required_17), (placed21 2 (4, 0) required_56)]
def childrenD_293 : Fin 2 → Finset Cell := ![(placed21 1 (1, 2) envelope_17), (placed21 2 (4, 0) envelope_56)]
theorem common_sub_293 : commonEnvelope childrenD_293 ⊆ insert (4, 3) required_293 := by decide +kernel
theorem child_required_sub_293 : ∀ j, childrenC_293 j ⊆ insert (4, 3) required_293 := by decide +kernel
theorem child_envelope_sub_293 : ∀ j, childrenD_293 j ⊆ envelope_293 := by decide +kernel
theorem pivot_mem_293 : (4, 3) ∈ envelope_293 := by decide +kernel
theorem children_work_293 : ∀ j, Template HasSnaky 4 (childrenC_293 j) (childrenD_293 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_17 1 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_56 2 (4, 0)).mono (by decide +kernel)
theorem row_works_293 : Template HasSnaky 5 required_293 envelope_293 := by
  refine compose HasSnaky 4 childrenC_293 childrenD_293 children_work_293 (4, 3)
    required_293 envelope_293 pivot_mem_293 child_required_sub_293 child_envelope_sub_293 ?_
  intro b hb
  exact common_sub_293 (mem_commonEnvelope childrenD_293 b hb)
def required_294 : Finset Cell := ⟨(([(1, 2), (1, 3), (2, 3), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_294 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4), (5, 2), (5, 3), (5, 4), (6, 2), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_294 : Fin 3 → Finset Cell := ![(placed21 1 (0, 2) required_10), (placed21 1 (0, 2) required_48), (placed21 3 (0, 6) required_165)]
def childrenD_294 : Fin 3 → Finset Cell := ![(placed21 1 (0, 2) envelope_10), (placed21 1 (0, 2) envelope_48), (placed21 3 (0, 6) envelope_165)]
theorem common_sub_294 : commonEnvelope childrenD_294 ⊆ insert (3, 3) required_294 := by decide +kernel
theorem child_required_sub_294 : ∀ j, childrenC_294 j ⊆ insert (3, 3) required_294 := by decide +kernel
theorem child_envelope_sub_294 : ∀ j, childrenD_294 j ⊆ envelope_294 := by decide +kernel
theorem pivot_mem_294 : (3, 3) ∈ envelope_294 := by decide +kernel
theorem children_work_294 : ∀ j, Template HasSnaky 4 (childrenC_294 j) (childrenD_294 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_48 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_165 3 (0, 6)).mono (by decide +kernel)
theorem row_works_294 : Template HasSnaky 5 required_294 envelope_294 := by
  refine compose HasSnaky 4 childrenC_294 childrenD_294 children_work_294 (3, 3)
    required_294 envelope_294 pivot_mem_294 child_required_sub_294 child_envelope_sub_294 ?_
  intro b hb
  exact common_sub_294 (mem_commonEnvelope childrenD_294 b hb)
def required_296 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 4), (2, 1), (2, 2), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_296 : Finset Cell := ⟨(([(0, 4), (1, 1), (1, 2), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 3), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_296 : Fin 2 → Finset Cell := ![(placed21 7 (2, 5) required_0), (placed21 3 (0, 5) required_132)]
def childrenD_296 : Fin 2 → Finset Cell := ![(placed21 7 (2, 5) envelope_0), (placed21 3 (0, 5) envelope_132)]
theorem common_sub_296 : commonEnvelope childrenD_296 ⊆ insert (2, 3) required_296 := by decide +kernel
theorem child_required_sub_296 : ∀ j, childrenC_296 j ⊆ insert (2, 3) required_296 := by decide +kernel
theorem child_envelope_sub_296 : ∀ j, childrenD_296 j ⊆ envelope_296 := by decide +kernel
theorem pivot_mem_296 : (2, 3) ∈ envelope_296 := by decide +kernel
theorem children_work_296 : ∀ j, Template HasSnaky 4 (childrenC_296 j) (childrenD_296 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (2, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_132 3 (0, 5)).mono (by decide +kernel)
theorem row_works_296 : Template HasSnaky 5 required_296 envelope_296 := by
  refine compose HasSnaky 4 childrenC_296 childrenD_296 children_work_296 (2, 3)
    required_296 envelope_296 pivot_mem_296 child_required_sub_296 child_envelope_sub_296 ?_
  intro b hb
  exact common_sub_296 (mem_commonEnvelope childrenD_296 b hb)
def required_299 : Finset Cell := ⟨(([(1, 3), (1, 4), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_299 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_299 : Fin 3 → Finset Cell := ![(placed21 4 (2, 7) required_12), (placed21 0 (0, 2) required_165), (placed21 2 (4, 2) required_264)]
def childrenD_299 : Fin 3 → Finset Cell := ![(placed21 4 (2, 7) envelope_12), (placed21 0 (0, 2) envelope_165), (placed21 2 (4, 2) envelope_264)]
theorem common_sub_299 : commonEnvelope childrenD_299 ⊆ insert (3, 5) required_299 := by decide +kernel
theorem child_required_sub_299 : ∀ j, childrenC_299 j ⊆ insert (3, 5) required_299 := by decide +kernel
theorem child_envelope_sub_299 : ∀ j, childrenD_299 j ⊆ envelope_299 := by decide +kernel
theorem pivot_mem_299 : (3, 5) ∈ envelope_299 := by decide +kernel
theorem children_work_299 : ∀ j, Template HasSnaky 4 (childrenC_299 j) (childrenD_299 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 4 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_165 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_264 2 (4, 2)).mono (by decide +kernel)
theorem row_works_299 : Template HasSnaky 5 required_299 envelope_299 := by
  refine compose HasSnaky 4 childrenC_299 childrenD_299 children_work_299 (3, 5)
    required_299 envelope_299 pivot_mem_299 child_required_sub_299 child_envelope_sub_299 ?_
  intro b hb
  exact common_sub_299 (mem_commonEnvelope childrenD_299 b hb)
def required_301 : Finset Cell := ⟨(([(0, 3), (1, 2), (1, 3), (2, 2), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_301 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 3), (3, 4), (3, 5), (3, 6), (4, 3), (4, 4), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_301 : Fin 2 → Finset Cell := ![(placed21 3 (0, 3) required_23), required_55]
def childrenD_301 : Fin 2 → Finset Cell := ![(placed21 3 (0, 3) envelope_23), envelope_55]
theorem common_sub_301 : commonEnvelope childrenD_301 ⊆ insert (3, 3) required_301 := by decide +kernel
theorem child_required_sub_301 : ∀ j, childrenC_301 j ⊆ insert (3, 3) required_301 := by decide +kernel
theorem child_envelope_sub_301 : ∀ j, childrenD_301 j ⊆ envelope_301 := by decide +kernel
theorem pivot_mem_301 : (3, 3) ∈ envelope_301 := by decide +kernel
theorem children_work_301 : ∀ j, Template HasSnaky 4 (childrenC_301 j) (childrenD_301 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_23 3 (0, 3)).mono (by decide +kernel)
  · exact row_works_55.mono (by decide +kernel)
theorem row_works_301 : Template HasSnaky 5 required_301 envelope_301 := by
  refine compose HasSnaky 4 childrenC_301 childrenD_301 children_work_301 (3, 3)
    required_301 envelope_301 pivot_mem_301 child_required_sub_301 child_envelope_sub_301 ?_
  intro b hb
  exact common_sub_301 (mem_commonEnvelope childrenD_301 b hb)
def required_306 : Finset Cell := ⟨(([(0, 2), (1, 2), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_306 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (2, 0), (2, 1), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 5), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_306 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) required_18), (placed21 7 (4, 4) required_207)]
def childrenD_306 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) envelope_18), (placed21 7 (4, 4) envelope_207)]
theorem common_sub_306 : commonEnvelope childrenD_306 ⊆ insert (4, 1) required_306 := by decide +kernel
theorem child_required_sub_306 : ∀ j, childrenC_306 j ⊆ insert (4, 1) required_306 := by decide +kernel
theorem child_envelope_sub_306 : ∀ j, childrenD_306 j ⊆ envelope_306 := by decide +kernel
theorem pivot_mem_306 : (4, 1) ∈ envelope_306 := by decide +kernel
theorem children_work_306 : ∀ j, Template HasSnaky 4 (childrenC_306 j) (childrenD_306 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_18 2 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_207 7 (4, 4)).mono (by decide +kernel)
theorem row_works_306 : Template HasSnaky 5 required_306 envelope_306 := by
  refine compose HasSnaky 4 childrenC_306 childrenD_306 children_work_306 (4, 1)
    required_306 envelope_306 pivot_mem_306 child_required_sub_306 child_envelope_sub_306 ?_
  intro b hb
  exact common_sub_306 (mem_commonEnvelope childrenD_306 b hb)
def required_308 : Finset Cell := ⟨(([(0, 3), (1, 1), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_308 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 5), (2, 6), (2, 7), (2, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_308 : Fin 4 → Finset Cell := ![(placed21 6 (1, 6) required_44), (placed21 6 (1, 6) required_52), (placed21 0 (0, 2) required_63), (placed21 6 (1, 6) required_158)]
def childrenD_308 : Fin 4 → Finset Cell := ![(placed21 6 (1, 6) envelope_44), (placed21 6 (1, 6) envelope_52), (placed21 0 (0, 2) envelope_63), (placed21 6 (1, 6) envelope_158)]
theorem common_sub_308 : commonEnvelope childrenD_308 ⊆ insert (1, 5) required_308 := by decide +kernel
theorem child_required_sub_308 : ∀ j, childrenC_308 j ⊆ insert (1, 5) required_308 := by decide +kernel
theorem child_envelope_sub_308 : ∀ j, childrenD_308 j ⊆ envelope_308 := by decide +kernel
theorem pivot_mem_308 : (1, 5) ∈ envelope_308 := by decide +kernel
theorem children_work_308 : ∀ j, Template HasSnaky 4 (childrenC_308 j) (childrenD_308 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 6 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 6 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_63 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_158 6 (1, 6)).mono (by decide +kernel)
theorem row_works_308 : Template HasSnaky 5 required_308 envelope_308 := by
  refine compose HasSnaky 4 childrenC_308 childrenD_308 children_work_308 (1, 5)
    required_308 envelope_308 pivot_mem_308 child_required_sub_308 child_envelope_sub_308 ?_
  intro b hb
  exact common_sub_308 (mem_commonEnvelope childrenD_308 b hb)
def required_312 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_312 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_312 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) required_5), (placed21 4 (0, 2) required_311)]
def childrenD_312 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) envelope_5), (placed21 4 (0, 2) envelope_311)]
theorem common_sub_312 : commonEnvelope childrenD_312 ⊆ insert (2, 1) required_312 := by decide +kernel
theorem child_required_sub_312 : ∀ j, childrenC_312 j ⊆ insert (2, 1) required_312 := by decide +kernel
theorem child_envelope_sub_312 : ∀ j, childrenD_312 j ⊆ envelope_312 := by decide +kernel
theorem pivot_mem_312 : (2, 1) ∈ envelope_312 := by decide +kernel
theorem children_work_312 : ∀ j, Template HasSnaky 4 (childrenC_312 j) (childrenD_312 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_311 4 (0, 2)).mono (by decide +kernel)
theorem row_works_312 : Template HasSnaky 5 required_312 envelope_312 := by
  refine compose HasSnaky 4 childrenC_312 childrenD_312 children_work_312 (2, 1)
    required_312 envelope_312 pivot_mem_312 child_required_sub_312 child_envelope_sub_312 ?_
  intro b hb
  exact common_sub_312 (mem_commonEnvelope childrenD_312 b hb)
def required_314_i0 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_314_i0 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (4, 2), (5, 1), (5, 2), (6, 1), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_314_i0 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) required_5), (placed21 1 (1, 0) required_20)]
def childrenD_314_i0 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) envelope_5), (placed21 1 (1, 0) envelope_20)]
theorem common_sub_314_i0 : commonEnvelope childrenD_314_i0 ⊆ insert (3, 0) required_314_i0 := by decide +kernel
theorem child_required_sub_314_i0 : ∀ j, childrenC_314_i0 j ⊆ insert (3, 0) required_314_i0 := by decide +kernel
theorem child_envelope_sub_314_i0 : ∀ j, childrenD_314_i0 j ⊆ envelope_314_i0 := by decide +kernel
theorem pivot_mem_314_i0 : (3, 0) ∈ envelope_314_i0 := by decide +kernel
theorem children_work_314_i0 : ∀ j, Template HasSnaky 3 (childrenC_314_i0 j) (childrenD_314_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_20 1 (1, 0)).mono (by decide +kernel)
theorem row_works_314_i0 : Template HasSnaky 4 required_314_i0 envelope_314_i0 := by
  refine compose HasSnaky 3 childrenC_314_i0 childrenD_314_i0 children_work_314_i0 (3, 0)
    required_314_i0 envelope_314_i0 pivot_mem_314_i0 child_required_sub_314_i0 child_envelope_sub_314_i0 ?_
  intro b hb
  exact common_sub_314_i0 (mem_commonEnvelope childrenD_314_i0 b hb)
def required_314 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_314 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1), (6, 2), (7, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_314 : Fin 4 → Finset Cell := ![(placed21 3 (0, 1) required_6), (placed21 0 (1, 0) required_8), (placed21 1 (1, 0) required_17), required_314_i0]
def childrenD_314 : Fin 4 → Finset Cell := ![(placed21 3 (0, 1) envelope_6), (placed21 0 (1, 0) envelope_8), (placed21 1 (1, 0) envelope_17), envelope_314_i0]
theorem common_sub_314 : commonEnvelope childrenD_314 ⊆ insert (4, 1) required_314 := by decide +kernel
theorem child_required_sub_314 : ∀ j, childrenC_314 j ⊆ insert (4, 1) required_314 := by decide +kernel
theorem child_envelope_sub_314 : ∀ j, childrenD_314 j ⊆ envelope_314 := by decide +kernel
theorem pivot_mem_314 : (4, 1) ∈ envelope_314 := by decide +kernel
theorem children_work_314 : ∀ j, Template HasSnaky 4 (childrenC_314 j) (childrenD_314 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 3 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_17 1 (1, 0)).mono (by decide +kernel)
  · exact row_works_314_i0.mono (by decide +kernel)
theorem row_works_314 : Template HasSnaky 5 required_314 envelope_314 := by
  refine compose HasSnaky 4 childrenC_314 childrenD_314 children_work_314 (4, 1)
    required_314 envelope_314 pivot_mem_314 child_required_sub_314 child_envelope_sub_314 ?_
  intro b hb
  exact common_sub_314 (mem_commonEnvelope childrenD_314 b hb)
def required_335 : Finset Cell := ⟨(([(1, 2), (2, 2), (2, 4), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_335 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 2), (4, 3), (5, 3), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_335 : Fin 2 → Finset Cell := ![(placed21 1 (0, 2) required_52), (placed21 2 (3, 0) required_334)]
def childrenD_335 : Fin 2 → Finset Cell := ![(placed21 1 (0, 2) envelope_52), (placed21 2 (3, 0) envelope_334)]
theorem common_sub_335 : commonEnvelope childrenD_335 ⊆ insert (3, 3) required_335 := by decide +kernel
theorem child_required_sub_335 : ∀ j, childrenC_335 j ⊆ insert (3, 3) required_335 := by decide +kernel
theorem child_envelope_sub_335 : ∀ j, childrenD_335 j ⊆ envelope_335 := by decide +kernel
theorem pivot_mem_335 : (3, 3) ∈ envelope_335 := by decide +kernel
theorem children_work_335 : ∀ j, Template HasSnaky 4 (childrenC_335 j) (childrenD_335 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_334 2 (3, 0)).mono (by decide +kernel)
theorem row_works_335 : Template HasSnaky 5 required_335 envelope_335 := by
  refine compose HasSnaky 4 childrenC_335 childrenD_335 children_work_335 (3, 3)
    required_335 envelope_335 pivot_mem_335 child_required_sub_335 child_envelope_sub_335 ?_
  intro b hb
  exact common_sub_335 (mem_commonEnvelope childrenD_335 b hb)
def required_342_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 2), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_342_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_342_i0 : Fin 2 → Finset Cell := ![(placed21 2 (3, 0) required_11), (placed21 5 (4, 1) required_78)]
def childrenD_342_i0 : Fin 2 → Finset Cell := ![(placed21 2 (3, 0) envelope_11), (placed21 5 (4, 1) envelope_78)]
theorem common_sub_342_i0 : commonEnvelope childrenD_342_i0 ⊆ insert (3, 4) required_342_i0 := by decide +kernel
theorem child_required_sub_342_i0 : ∀ j, childrenC_342_i0 j ⊆ insert (3, 4) required_342_i0 := by decide +kernel
theorem child_envelope_sub_342_i0 : ∀ j, childrenD_342_i0 j ⊆ envelope_342_i0 := by decide +kernel
theorem pivot_mem_342_i0 : (3, 4) ∈ envelope_342_i0 := by decide +kernel
theorem children_work_342_i0 : ∀ j, Template HasSnaky 3 (childrenC_342_i0 j) (childrenD_342_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 2 (3, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_78 5 (4, 1)).mono (by decide +kernel)
theorem row_works_342_i0 : Template HasSnaky 4 required_342_i0 envelope_342_i0 := by
  refine compose HasSnaky 3 childrenC_342_i0 childrenD_342_i0 children_work_342_i0 (3, 4)
    required_342_i0 envelope_342_i0 pivot_mem_342_i0 child_required_sub_342_i0 child_envelope_sub_342_i0 ?_
  intro b hb
  exact common_sub_342_i0 (mem_commonEnvelope childrenD_342_i0 b hb)
def required_342 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 2), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_342 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_342 : Fin 2 → Finset Cell := ![(placed21 4 (0, 2) required_5), required_342_i0]
def childrenD_342 : Fin 2 → Finset Cell := ![(placed21 4 (0, 2) envelope_5), envelope_342_i0]
theorem common_sub_342 : commonEnvelope childrenD_342 ⊆ insert (3, 1) required_342 := by decide +kernel
theorem child_required_sub_342 : ∀ j, childrenC_342 j ⊆ insert (3, 1) required_342 := by decide +kernel
theorem child_envelope_sub_342 : ∀ j, childrenD_342 j ⊆ envelope_342 := by decide +kernel
theorem pivot_mem_342 : (3, 1) ∈ envelope_342 := by decide +kernel
theorem children_work_342 : ∀ j, Template HasSnaky 4 (childrenC_342 j) (childrenD_342 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 2)).mono (by decide +kernel)
  · exact row_works_342_i0.mono (by decide +kernel)
theorem row_works_342 : Template HasSnaky 5 required_342 envelope_342 := by
  refine compose HasSnaky 4 childrenC_342 childrenD_342 children_work_342 (3, 1)
    required_342 envelope_342 pivot_mem_342 child_required_sub_342 child_envelope_sub_342 ?_
  intro b hb
  exact common_sub_342 (mem_commonEnvelope childrenD_342 b hb)
def required_347_i1 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_347_i1 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (2, 3), (2, 4), (3, 2), (3, 3), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_347_i1 : Fin 2 → Finset Cell := ![(placed21 1 (1, 0) required_5), (placed21 3 (0, 3) required_94)]
def childrenD_347_i1 : Fin 2 → Finset Cell := ![(placed21 1 (1, 0) envelope_5), (placed21 3 (0, 3) envelope_94)]
theorem common_sub_347_i1 : commonEnvelope childrenD_347_i1 ⊆ insert (2, 3) required_347_i1 := by decide +kernel
theorem child_required_sub_347_i1 : ∀ j, childrenC_347_i1 j ⊆ insert (2, 3) required_347_i1 := by decide +kernel
theorem child_envelope_sub_347_i1 : ∀ j, childrenD_347_i1 j ⊆ envelope_347_i1 := by decide +kernel
theorem pivot_mem_347_i1 : (2, 3) ∈ envelope_347_i1 := by decide +kernel
theorem children_work_347_i1 : ∀ j, Template HasSnaky 2 (childrenC_347_i1 j) (childrenD_347_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_94 3 (0, 3)).mono (by decide +kernel)
theorem row_works_347_i1 : Template HasSnaky 3 required_347_i1 envelope_347_i1 := by
  refine compose HasSnaky 2 childrenC_347_i1 childrenD_347_i1 children_work_347_i1 (2, 3)
    required_347_i1 envelope_347_i1 pivot_mem_347_i1 child_required_sub_347_i1 child_envelope_sub_347_i1 ?_
  intro b hb
  exact common_sub_347_i1 (mem_commonEnvelope childrenD_347_i1 b hb)
def required_347_i0 : Finset Cell := ⟨(([(0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_347_i0 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (2, 3), (2, 4), (3, 2), (3, 3), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_347_i0 : Fin 2 → Finset Cell := ![(placed21 5 (1, 0) required_5), required_347_i1]
def childrenD_347_i0 : Fin 2 → Finset Cell := ![(placed21 5 (1, 0) envelope_5), envelope_347_i1]
theorem common_sub_347_i0 : commonEnvelope childrenD_347_i0 ⊆ insert (0, 3) required_347_i0 := by decide +kernel
theorem child_required_sub_347_i0 : ∀ j, childrenC_347_i0 j ⊆ insert (0, 3) required_347_i0 := by decide +kernel
theorem child_envelope_sub_347_i0 : ∀ j, childrenD_347_i0 j ⊆ envelope_347_i0 := by decide +kernel
theorem pivot_mem_347_i0 : (0, 3) ∈ envelope_347_i0 := by decide +kernel
theorem children_work_347_i0 : ∀ j, Template HasSnaky 3 (childrenC_347_i0 j) (childrenD_347_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (1, 0)).mono (by decide +kernel)
  · exact row_works_347_i1.mono (by decide +kernel)
theorem row_works_347_i0 : Template HasSnaky 4 required_347_i0 envelope_347_i0 := by
  refine compose HasSnaky 3 childrenC_347_i0 childrenD_347_i0 children_work_347_i0 (0, 3)
    required_347_i0 envelope_347_i0 pivot_mem_347_i0 child_required_sub_347_i0 child_envelope_sub_347_i0 ?_
  intro b hb
  exact common_sub_347_i0 (mem_commonEnvelope childrenD_347_i0 b hb)
def required_347 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_347 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 2), (3, 3), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_347 : Fin 3 → Finset Cell := ![required_20, (placed21 2 (1, 0) required_29), required_347_i0]
def childrenD_347 : Fin 3 → Finset Cell := ![envelope_20, (placed21 2 (1, 0) envelope_29), envelope_347_i0]
theorem common_sub_347 : commonEnvelope childrenD_347 ⊆ insert (1, 3) required_347 := by decide +kernel
theorem child_required_sub_347 : ∀ j, childrenC_347 j ⊆ insert (1, 3) required_347 := by decide +kernel
theorem child_envelope_sub_347 : ∀ j, childrenD_347 j ⊆ envelope_347 := by decide +kernel
theorem pivot_mem_347 : (1, 3) ∈ envelope_347 := by decide +kernel
theorem children_work_347 : ∀ j, Template HasSnaky 4 (childrenC_347 j) (childrenD_347 j) := by
  intro j
  fin_cases j
  · exact row_works_20.mono (by decide +kernel)
  · exact (placed21_template row_works_29 2 (1, 0)).mono (by decide +kernel)
  · exact row_works_347_i0.mono (by decide +kernel)
theorem row_works_347 : Template HasSnaky 5 required_347 envelope_347 := by
  refine compose HasSnaky 4 childrenC_347 childrenD_347 children_work_347 (1, 3)
    required_347 envelope_347 pivot_mem_347 child_required_sub_347 child_envelope_sub_347 ?_
  intro b hb
  exact common_sub_347 (mem_commonEnvelope childrenD_347 b hb)
def required_352 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_352 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 0), (5, 1), (5, 2), (6, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_352 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_4), (placed21 0 (1, 0) required_351)]
def childrenD_352 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_4), (placed21 0 (1, 0) envelope_351)]
theorem common_sub_352 : commonEnvelope childrenD_352 ⊆ insert (4, 2) required_352 := by decide +kernel
theorem child_required_sub_352 : ∀ j, childrenC_352 j ⊆ insert (4, 2) required_352 := by decide +kernel
theorem child_envelope_sub_352 : ∀ j, childrenD_352 j ⊆ envelope_352 := by decide +kernel
theorem pivot_mem_352 : (4, 2) ∈ envelope_352 := by decide +kernel
theorem children_work_352 : ∀ j, Template HasSnaky 4 (childrenC_352 j) (childrenD_352 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_351 0 (1, 0)).mono (by decide +kernel)
theorem row_works_352 : Template HasSnaky 5 required_352 envelope_352 := by
  refine compose HasSnaky 4 childrenC_352 childrenD_352 children_work_352 (4, 2)
    required_352 envelope_352 pivot_mem_352 child_required_sub_352 child_envelope_sub_352 ?_
  intro b hb
  exact common_sub_352 (mem_commonEnvelope childrenD_352 b hb)
def required_355 : Finset Cell := ⟨(([(0, 2), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_355 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_355 : Fin 2 → Finset Cell := ![(placed21 1 (2, 1) required_8), (placed21 7 (4, 4) required_354)]
def childrenD_355 : Fin 2 → Finset Cell := ![(placed21 1 (2, 1) envelope_8), (placed21 7 (4, 4) envelope_354)]
theorem common_sub_355 : commonEnvelope childrenD_355 ⊆ insert (3, 4) required_355 := by decide +kernel
theorem child_required_sub_355 : ∀ j, childrenC_355 j ⊆ insert (3, 4) required_355 := by decide +kernel
theorem child_envelope_sub_355 : ∀ j, childrenD_355 j ⊆ envelope_355 := by decide +kernel
theorem pivot_mem_355 : (3, 4) ∈ envelope_355 := by decide +kernel
theorem children_work_355 : ∀ j, Template HasSnaky 4 (childrenC_355 j) (childrenD_355 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 1 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_354 7 (4, 4)).mono (by decide +kernel)
theorem row_works_355 : Template HasSnaky 5 required_355 envelope_355 := by
  refine compose HasSnaky 4 childrenC_355 childrenD_355 children_work_355 (3, 4)
    required_355 envelope_355 pivot_mem_355 child_required_sub_355 child_envelope_sub_355 ?_
  intro b hb
  exact common_sub_355 (mem_commonEnvelope childrenD_355 b hb)
def height_272 : ℕ := 5
def childrenH_272 : Fin 2 → ℕ := ![height_5, height_39]
theorem height_exact_272 : height_272 = 1 + Finset.univ.sup childrenH_272 := by decide +kernel
theorem required_origin_272 : ∀ x ∈ required_272,
    (∃ j, x ∈ childrenC_272 j) ∨ ∀ j, x ∈ childrenD_272 j := by decide +kernel
theorem required_exact_272 : required_272 =
    ((Finset.univ.biUnion childrenC_272) ∪ commonEnvelope childrenD_272).erase (2, 1) := by
  exact required_eq_combination childrenC_272 childrenD_272 (2, 1) required_272
    (by decide +kernel) child_required_sub_272 common_sub_272 required_origin_272
theorem envelope_origin_272 : ∀ x ∈ envelope_272,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_272 j := by decide +kernel
theorem envelope_exact_272 : envelope_272 =
    insert (2, 1) (Finset.univ.biUnion childrenD_272) := by
  exact envelope_eq_combination childrenD_272 (2, 1) envelope_272
    pivot_mem_272 child_envelope_sub_272 envelope_origin_272
def checked_272 : CheckedCard where
  required := required_272
  envelope := envelope_272
  height := height_272
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_272
def height_273 : ℕ := 5
def childrenH_273 : Fin 2 → ℕ := ![height_2, height_206]
theorem height_exact_273 : height_273 = 1 + Finset.univ.sup childrenH_273 := by decide +kernel
theorem required_origin_273 : ∀ x ∈ required_273,
    (∃ j, x ∈ childrenC_273 j) ∨ ∀ j, x ∈ childrenD_273 j := by decide +kernel
theorem required_exact_273 : required_273 =
    ((Finset.univ.biUnion childrenC_273) ∪ commonEnvelope childrenD_273).erase (3, 3) := by
  exact required_eq_combination childrenC_273 childrenD_273 (3, 3) required_273
    (by decide +kernel) child_required_sub_273 common_sub_273 required_origin_273
theorem envelope_origin_273 : ∀ x ∈ envelope_273,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_273 j := by decide +kernel
theorem envelope_exact_273 : envelope_273 =
    insert (3, 3) (Finset.univ.biUnion childrenD_273) := by
  exact envelope_eq_combination childrenD_273 (3, 3) envelope_273
    pivot_mem_273 child_envelope_sub_273 envelope_origin_273
def checked_273 : CheckedCard where
  required := required_273
  envelope := envelope_273
  height := height_273
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_273
def height_274 : ℕ := 5
def childrenH_274 : Fin 3 → ℕ := ![height_13, height_44, height_83]
theorem height_exact_274 : height_274 = 1 + Finset.univ.sup childrenH_274 := by decide +kernel
theorem required_origin_274 : ∀ x ∈ required_274,
    (∃ j, x ∈ childrenC_274 j) ∨ ∀ j, x ∈ childrenD_274 j := by decide +kernel
theorem required_exact_274 : required_274 =
    ((Finset.univ.biUnion childrenC_274) ∪ commonEnvelope childrenD_274).erase (3, 2) := by
  exact required_eq_combination childrenC_274 childrenD_274 (3, 2) required_274
    (by decide +kernel) child_required_sub_274 common_sub_274 required_origin_274
theorem envelope_origin_274 : ∀ x ∈ envelope_274,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_274 j := by decide +kernel
theorem envelope_exact_274 : envelope_274 =
    insert (3, 2) (Finset.univ.biUnion childrenD_274) := by
  exact envelope_eq_combination childrenD_274 (3, 2) envelope_274
    pivot_mem_274 child_envelope_sub_274 envelope_origin_274
def checked_274 : CheckedCard where
  required := required_274
  envelope := envelope_274
  height := height_274
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_274
def height_278 : ℕ := 5
def childrenH_278 : Fin 2 → ℕ := ![height_6, height_277]
theorem height_exact_278 : height_278 = 1 + Finset.univ.sup childrenH_278 := by decide +kernel
theorem required_origin_278 : ∀ x ∈ required_278,
    (∃ j, x ∈ childrenC_278 j) ∨ ∀ j, x ∈ childrenD_278 j := by decide +kernel
theorem required_exact_278 : required_278 =
    ((Finset.univ.biUnion childrenC_278) ∪ commonEnvelope childrenD_278).erase (4, 2) := by
  exact required_eq_combination childrenC_278 childrenD_278 (4, 2) required_278
    (by decide +kernel) child_required_sub_278 common_sub_278 required_origin_278
theorem envelope_origin_278 : ∀ x ∈ envelope_278,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_278 j := by decide +kernel
theorem envelope_exact_278 : envelope_278 =
    insert (4, 2) (Finset.univ.biUnion childrenD_278) := by
  exact envelope_eq_combination childrenD_278 (4, 2) envelope_278
    pivot_mem_278 child_envelope_sub_278 envelope_origin_278
def checked_278 : CheckedCard where
  required := required_278
  envelope := envelope_278
  height := height_278
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_278
def height_279 : ℕ := 5
def childrenH_279 : Fin 2 → ℕ := ![height_6, height_141]
theorem height_exact_279 : height_279 = 1 + Finset.univ.sup childrenH_279 := by decide +kernel
theorem required_origin_279 : ∀ x ∈ required_279,
    (∃ j, x ∈ childrenC_279 j) ∨ ∀ j, x ∈ childrenD_279 j := by decide +kernel
theorem required_exact_279 : required_279 =
    ((Finset.univ.biUnion childrenC_279) ∪ commonEnvelope childrenD_279).erase (4, 3) := by
  exact required_eq_combination childrenC_279 childrenD_279 (4, 3) required_279
    (by decide +kernel) child_required_sub_279 common_sub_279 required_origin_279
theorem envelope_origin_279 : ∀ x ∈ envelope_279,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_279 j := by decide +kernel
theorem envelope_exact_279 : envelope_279 =
    insert (4, 3) (Finset.univ.biUnion childrenD_279) := by
  exact envelope_eq_combination childrenD_279 (4, 3) envelope_279
    pivot_mem_279 child_envelope_sub_279 envelope_origin_279
def checked_279 : CheckedCard where
  required := required_279
  envelope := envelope_279
  height := height_279
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_279
def height_282 : ℕ := 5
def childrenH_282 : Fin 3 → ℕ := ![height_20, height_29, height_92]
theorem height_exact_282 : height_282 = 1 + Finset.univ.sup childrenH_282 := by decide +kernel
theorem required_origin_282 : ∀ x ∈ required_282,
    (∃ j, x ∈ childrenC_282 j) ∨ ∀ j, x ∈ childrenD_282 j := by decide +kernel
theorem required_exact_282 : required_282 =
    ((Finset.univ.biUnion childrenC_282) ∪ commonEnvelope childrenD_282).erase (3, 2) := by
  exact required_eq_combination childrenC_282 childrenD_282 (3, 2) required_282
    (by decide +kernel) child_required_sub_282 common_sub_282 required_origin_282
theorem envelope_origin_282 : ∀ x ∈ envelope_282,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_282 j := by decide +kernel
theorem envelope_exact_282 : envelope_282 =
    insert (3, 2) (Finset.univ.biUnion childrenD_282) := by
  exact envelope_eq_combination childrenD_282 (3, 2) envelope_282
    pivot_mem_282 child_envelope_sub_282 envelope_origin_282
def checked_282 : CheckedCard where
  required := required_282
  envelope := envelope_282
  height := height_282
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_282
def height_293 : ℕ := 5
def childrenH_293 : Fin 2 → ℕ := ![height_17, height_56]
theorem height_exact_293 : height_293 = 1 + Finset.univ.sup childrenH_293 := by decide +kernel
theorem required_origin_293 : ∀ x ∈ required_293,
    (∃ j, x ∈ childrenC_293 j) ∨ ∀ j, x ∈ childrenD_293 j := by decide +kernel
theorem required_exact_293 : required_293 =
    ((Finset.univ.biUnion childrenC_293) ∪ commonEnvelope childrenD_293).erase (4, 3) := by
  exact required_eq_combination childrenC_293 childrenD_293 (4, 3) required_293
    (by decide +kernel) child_required_sub_293 common_sub_293 required_origin_293
theorem envelope_origin_293 : ∀ x ∈ envelope_293,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_293 j := by decide +kernel
theorem envelope_exact_293 : envelope_293 =
    insert (4, 3) (Finset.univ.biUnion childrenD_293) := by
  exact envelope_eq_combination childrenD_293 (4, 3) envelope_293
    pivot_mem_293 child_envelope_sub_293 envelope_origin_293
def checked_293 : CheckedCard where
  required := required_293
  envelope := envelope_293
  height := height_293
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_293
def height_294 : ℕ := 5
def childrenH_294 : Fin 3 → ℕ := ![height_10, height_48, height_165]
theorem height_exact_294 : height_294 = 1 + Finset.univ.sup childrenH_294 := by decide +kernel
theorem required_origin_294 : ∀ x ∈ required_294,
    (∃ j, x ∈ childrenC_294 j) ∨ ∀ j, x ∈ childrenD_294 j := by decide +kernel
theorem required_exact_294 : required_294 =
    ((Finset.univ.biUnion childrenC_294) ∪ commonEnvelope childrenD_294).erase (3, 3) := by
  exact required_eq_combination childrenC_294 childrenD_294 (3, 3) required_294
    (by decide +kernel) child_required_sub_294 common_sub_294 required_origin_294
theorem envelope_origin_294 : ∀ x ∈ envelope_294,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_294 j := by decide +kernel
theorem envelope_exact_294 : envelope_294 =
    insert (3, 3) (Finset.univ.biUnion childrenD_294) := by
  exact envelope_eq_combination childrenD_294 (3, 3) envelope_294
    pivot_mem_294 child_envelope_sub_294 envelope_origin_294
def checked_294 : CheckedCard where
  required := required_294
  envelope := envelope_294
  height := height_294
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_294
def height_296 : ℕ := 5
def childrenH_296 : Fin 2 → ℕ := ![height_0, height_132]
theorem height_exact_296 : height_296 = 1 + Finset.univ.sup childrenH_296 := by decide +kernel
theorem required_origin_296 : ∀ x ∈ required_296,
    (∃ j, x ∈ childrenC_296 j) ∨ ∀ j, x ∈ childrenD_296 j := by decide +kernel
theorem required_exact_296 : required_296 =
    ((Finset.univ.biUnion childrenC_296) ∪ commonEnvelope childrenD_296).erase (2, 3) := by
  exact required_eq_combination childrenC_296 childrenD_296 (2, 3) required_296
    (by decide +kernel) child_required_sub_296 common_sub_296 required_origin_296
theorem envelope_origin_296 : ∀ x ∈ envelope_296,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_296 j := by decide +kernel
theorem envelope_exact_296 : envelope_296 =
    insert (2, 3) (Finset.univ.biUnion childrenD_296) := by
  exact envelope_eq_combination childrenD_296 (2, 3) envelope_296
    pivot_mem_296 child_envelope_sub_296 envelope_origin_296
def checked_296 : CheckedCard where
  required := required_296
  envelope := envelope_296
  height := height_296
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_296
def height_299 : ℕ := 5
def childrenH_299 : Fin 3 → ℕ := ![height_12, height_165, height_264]
theorem height_exact_299 : height_299 = 1 + Finset.univ.sup childrenH_299 := by decide +kernel
theorem required_origin_299 : ∀ x ∈ required_299,
    (∃ j, x ∈ childrenC_299 j) ∨ ∀ j, x ∈ childrenD_299 j := by decide +kernel
theorem required_exact_299 : required_299 =
    ((Finset.univ.biUnion childrenC_299) ∪ commonEnvelope childrenD_299).erase (3, 5) := by
  exact required_eq_combination childrenC_299 childrenD_299 (3, 5) required_299
    (by decide +kernel) child_required_sub_299 common_sub_299 required_origin_299
theorem envelope_origin_299 : ∀ x ∈ envelope_299,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_299 j := by decide +kernel
theorem envelope_exact_299 : envelope_299 =
    insert (3, 5) (Finset.univ.biUnion childrenD_299) := by
  exact envelope_eq_combination childrenD_299 (3, 5) envelope_299
    pivot_mem_299 child_envelope_sub_299 envelope_origin_299
def checked_299 : CheckedCard where
  required := required_299
  envelope := envelope_299
  height := height_299
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_299
def height_301 : ℕ := 5
def childrenH_301 : Fin 2 → ℕ := ![height_23, height_55]
theorem height_exact_301 : height_301 = 1 + Finset.univ.sup childrenH_301 := by decide +kernel
theorem required_origin_301 : ∀ x ∈ required_301,
    (∃ j, x ∈ childrenC_301 j) ∨ ∀ j, x ∈ childrenD_301 j := by decide +kernel
theorem required_exact_301 : required_301 =
    ((Finset.univ.biUnion childrenC_301) ∪ commonEnvelope childrenD_301).erase (3, 3) := by
  exact required_eq_combination childrenC_301 childrenD_301 (3, 3) required_301
    (by decide +kernel) child_required_sub_301 common_sub_301 required_origin_301
theorem envelope_origin_301 : ∀ x ∈ envelope_301,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_301 j := by decide +kernel
theorem envelope_exact_301 : envelope_301 =
    insert (3, 3) (Finset.univ.biUnion childrenD_301) := by
  exact envelope_eq_combination childrenD_301 (3, 3) envelope_301
    pivot_mem_301 child_envelope_sub_301 envelope_origin_301
def checked_301 : CheckedCard where
  required := required_301
  envelope := envelope_301
  height := height_301
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_301
def height_306 : ℕ := 5
def childrenH_306 : Fin 2 → ℕ := ![height_18, height_207]
theorem height_exact_306 : height_306 = 1 + Finset.univ.sup childrenH_306 := by decide +kernel
theorem required_origin_306 : ∀ x ∈ required_306,
    (∃ j, x ∈ childrenC_306 j) ∨ ∀ j, x ∈ childrenD_306 j := by decide +kernel
theorem required_exact_306 : required_306 =
    ((Finset.univ.biUnion childrenC_306) ∪ commonEnvelope childrenD_306).erase (4, 1) := by
  exact required_eq_combination childrenC_306 childrenD_306 (4, 1) required_306
    (by decide +kernel) child_required_sub_306 common_sub_306 required_origin_306
theorem envelope_origin_306 : ∀ x ∈ envelope_306,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_306 j := by decide +kernel
theorem envelope_exact_306 : envelope_306 =
    insert (4, 1) (Finset.univ.biUnion childrenD_306) := by
  exact envelope_eq_combination childrenD_306 (4, 1) envelope_306
    pivot_mem_306 child_envelope_sub_306 envelope_origin_306
def checked_306 : CheckedCard where
  required := required_306
  envelope := envelope_306
  height := height_306
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_306
def height_308 : ℕ := 5
def childrenH_308 : Fin 4 → ℕ := ![height_44, height_52, height_63, height_158]
theorem height_exact_308 : height_308 = 1 + Finset.univ.sup childrenH_308 := by decide +kernel
theorem required_origin_308 : ∀ x ∈ required_308,
    (∃ j, x ∈ childrenC_308 j) ∨ ∀ j, x ∈ childrenD_308 j := by decide +kernel
theorem required_exact_308 : required_308 =
    ((Finset.univ.biUnion childrenC_308) ∪ commonEnvelope childrenD_308).erase (1, 5) := by
  exact required_eq_combination childrenC_308 childrenD_308 (1, 5) required_308
    (by decide +kernel) child_required_sub_308 common_sub_308 required_origin_308
theorem envelope_origin_308 : ∀ x ∈ envelope_308,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_308 j := by decide +kernel
theorem envelope_exact_308 : envelope_308 =
    insert (1, 5) (Finset.univ.biUnion childrenD_308) := by
  exact envelope_eq_combination childrenD_308 (1, 5) envelope_308
    pivot_mem_308 child_envelope_sub_308 envelope_origin_308
def checked_308 : CheckedCard where
  required := required_308
  envelope := envelope_308
  height := height_308
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_308
def height_312 : ℕ := 5
def childrenH_312 : Fin 2 → ℕ := ![height_5, height_311]
theorem height_exact_312 : height_312 = 1 + Finset.univ.sup childrenH_312 := by decide +kernel
theorem required_origin_312 : ∀ x ∈ required_312,
    (∃ j, x ∈ childrenC_312 j) ∨ ∀ j, x ∈ childrenD_312 j := by decide +kernel
theorem required_exact_312 : required_312 =
    ((Finset.univ.biUnion childrenC_312) ∪ commonEnvelope childrenD_312).erase (2, 1) := by
  exact required_eq_combination childrenC_312 childrenD_312 (2, 1) required_312
    (by decide +kernel) child_required_sub_312 common_sub_312 required_origin_312
theorem envelope_origin_312 : ∀ x ∈ envelope_312,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_312 j := by decide +kernel
theorem envelope_exact_312 : envelope_312 =
    insert (2, 1) (Finset.univ.biUnion childrenD_312) := by
  exact envelope_eq_combination childrenD_312 (2, 1) envelope_312
    pivot_mem_312 child_envelope_sub_312 envelope_origin_312
def checked_312 : CheckedCard where
  required := required_312
  envelope := envelope_312
  height := height_312
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_312
def height_314_i0 : ℕ := 4
def childrenH_314_i0 : Fin 2 → ℕ := ![height_5, height_20]
theorem height_exact_314_i0 : height_314_i0 = 1 + Finset.univ.sup childrenH_314_i0 := by decide +kernel
theorem required_origin_314_i0 : ∀ x ∈ required_314_i0,
    (∃ j, x ∈ childrenC_314_i0 j) ∨ ∀ j, x ∈ childrenD_314_i0 j := by decide +kernel
theorem required_exact_314_i0 : required_314_i0 =
    ((Finset.univ.biUnion childrenC_314_i0) ∪ commonEnvelope childrenD_314_i0).erase (3, 0) := by
  exact required_eq_combination childrenC_314_i0 childrenD_314_i0 (3, 0) required_314_i0
    (by decide +kernel) child_required_sub_314_i0 common_sub_314_i0 required_origin_314_i0
theorem envelope_origin_314_i0 : ∀ x ∈ envelope_314_i0,
    x = (3, 0) ∨ ∃ j, x ∈ childrenD_314_i0 j := by decide +kernel
theorem envelope_exact_314_i0 : envelope_314_i0 =
    insert (3, 0) (Finset.univ.biUnion childrenD_314_i0) := by
  exact envelope_eq_combination childrenD_314_i0 (3, 0) envelope_314_i0
    pivot_mem_314_i0 child_envelope_sub_314_i0 envelope_origin_314_i0
def checked_314_i0 : CheckedCard where
  required := required_314_i0
  envelope := envelope_314_i0
  height := height_314_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_314_i0
def height_314 : ℕ := 5
def childrenH_314 : Fin 4 → ℕ := ![height_6, height_8, height_17, height_314_i0]
theorem height_exact_314 : height_314 = 1 + Finset.univ.sup childrenH_314 := by decide +kernel
theorem required_origin_314 : ∀ x ∈ required_314,
    (∃ j, x ∈ childrenC_314 j) ∨ ∀ j, x ∈ childrenD_314 j := by decide +kernel
theorem required_exact_314 : required_314 =
    ((Finset.univ.biUnion childrenC_314) ∪ commonEnvelope childrenD_314).erase (4, 1) := by
  exact required_eq_combination childrenC_314 childrenD_314 (4, 1) required_314
    (by decide +kernel) child_required_sub_314 common_sub_314 required_origin_314
theorem envelope_origin_314 : ∀ x ∈ envelope_314,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_314 j := by decide +kernel
theorem envelope_exact_314 : envelope_314 =
    insert (4, 1) (Finset.univ.biUnion childrenD_314) := by
  exact envelope_eq_combination childrenD_314 (4, 1) envelope_314
    pivot_mem_314 child_envelope_sub_314 envelope_origin_314
def checked_314 : CheckedCard where
  required := required_314
  envelope := envelope_314
  height := height_314
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_314
def height_335 : ℕ := 5
def childrenH_335 : Fin 2 → ℕ := ![height_52, height_334]
theorem height_exact_335 : height_335 = 1 + Finset.univ.sup childrenH_335 := by decide +kernel
theorem required_origin_335 : ∀ x ∈ required_335,
    (∃ j, x ∈ childrenC_335 j) ∨ ∀ j, x ∈ childrenD_335 j := by decide +kernel
theorem required_exact_335 : required_335 =
    ((Finset.univ.biUnion childrenC_335) ∪ commonEnvelope childrenD_335).erase (3, 3) := by
  exact required_eq_combination childrenC_335 childrenD_335 (3, 3) required_335
    (by decide +kernel) child_required_sub_335 common_sub_335 required_origin_335
theorem envelope_origin_335 : ∀ x ∈ envelope_335,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_335 j := by decide +kernel
theorem envelope_exact_335 : envelope_335 =
    insert (3, 3) (Finset.univ.biUnion childrenD_335) := by
  exact envelope_eq_combination childrenD_335 (3, 3) envelope_335
    pivot_mem_335 child_envelope_sub_335 envelope_origin_335
def checked_335 : CheckedCard where
  required := required_335
  envelope := envelope_335
  height := height_335
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_335
def height_342_i0 : ℕ := 4
def childrenH_342_i0 : Fin 2 → ℕ := ![height_11, height_78]
theorem height_exact_342_i0 : height_342_i0 = 1 + Finset.univ.sup childrenH_342_i0 := by decide +kernel
theorem required_origin_342_i0 : ∀ x ∈ required_342_i0,
    (∃ j, x ∈ childrenC_342_i0 j) ∨ ∀ j, x ∈ childrenD_342_i0 j := by decide +kernel
theorem required_exact_342_i0 : required_342_i0 =
    ((Finset.univ.biUnion childrenC_342_i0) ∪ commonEnvelope childrenD_342_i0).erase (3, 4) := by
  exact required_eq_combination childrenC_342_i0 childrenD_342_i0 (3, 4) required_342_i0
    (by decide +kernel) child_required_sub_342_i0 common_sub_342_i0 required_origin_342_i0
theorem envelope_origin_342_i0 : ∀ x ∈ envelope_342_i0,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_342_i0 j := by decide +kernel
theorem envelope_exact_342_i0 : envelope_342_i0 =
    insert (3, 4) (Finset.univ.biUnion childrenD_342_i0) := by
  exact envelope_eq_combination childrenD_342_i0 (3, 4) envelope_342_i0
    pivot_mem_342_i0 child_envelope_sub_342_i0 envelope_origin_342_i0
def checked_342_i0 : CheckedCard where
  required := required_342_i0
  envelope := envelope_342_i0
  height := height_342_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_342_i0
def height_342 : ℕ := 5
def childrenH_342 : Fin 2 → ℕ := ![height_5, height_342_i0]
theorem height_exact_342 : height_342 = 1 + Finset.univ.sup childrenH_342 := by decide +kernel
theorem required_origin_342 : ∀ x ∈ required_342,
    (∃ j, x ∈ childrenC_342 j) ∨ ∀ j, x ∈ childrenD_342 j := by decide +kernel
theorem required_exact_342 : required_342 =
    ((Finset.univ.biUnion childrenC_342) ∪ commonEnvelope childrenD_342).erase (3, 1) := by
  exact required_eq_combination childrenC_342 childrenD_342 (3, 1) required_342
    (by decide +kernel) child_required_sub_342 common_sub_342 required_origin_342
theorem envelope_origin_342 : ∀ x ∈ envelope_342,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_342 j := by decide +kernel
theorem envelope_exact_342 : envelope_342 =
    insert (3, 1) (Finset.univ.biUnion childrenD_342) := by
  exact envelope_eq_combination childrenD_342 (3, 1) envelope_342
    pivot_mem_342 child_envelope_sub_342 envelope_origin_342
def checked_342 : CheckedCard where
  required := required_342
  envelope := envelope_342
  height := height_342
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_342
def height_347_i1 : ℕ := 3
def childrenH_347_i1 : Fin 2 → ℕ := ![height_5, height_94]
theorem height_exact_347_i1 : height_347_i1 = 1 + Finset.univ.sup childrenH_347_i1 := by decide +kernel
theorem required_origin_347_i1 : ∀ x ∈ required_347_i1,
    (∃ j, x ∈ childrenC_347_i1 j) ∨ ∀ j, x ∈ childrenD_347_i1 j := by decide +kernel
theorem required_exact_347_i1 : required_347_i1 =
    ((Finset.univ.biUnion childrenC_347_i1) ∪ commonEnvelope childrenD_347_i1).erase (2, 3) := by
  exact required_eq_combination childrenC_347_i1 childrenD_347_i1 (2, 3) required_347_i1
    (by decide +kernel) child_required_sub_347_i1 common_sub_347_i1 required_origin_347_i1
theorem envelope_origin_347_i1 : ∀ x ∈ envelope_347_i1,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_347_i1 j := by decide +kernel
theorem envelope_exact_347_i1 : envelope_347_i1 =
    insert (2, 3) (Finset.univ.biUnion childrenD_347_i1) := by
  exact envelope_eq_combination childrenD_347_i1 (2, 3) envelope_347_i1
    pivot_mem_347_i1 child_envelope_sub_347_i1 envelope_origin_347_i1
def checked_347_i1 : CheckedCard where
  required := required_347_i1
  envelope := envelope_347_i1
  height := height_347_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_347_i1
def height_347_i0 : ℕ := 4
def childrenH_347_i0 : Fin 2 → ℕ := ![height_5, height_347_i1]
theorem height_exact_347_i0 : height_347_i0 = 1 + Finset.univ.sup childrenH_347_i0 := by decide +kernel
theorem required_origin_347_i0 : ∀ x ∈ required_347_i0,
    (∃ j, x ∈ childrenC_347_i0 j) ∨ ∀ j, x ∈ childrenD_347_i0 j := by decide +kernel
theorem required_exact_347_i0 : required_347_i0 =
    ((Finset.univ.biUnion childrenC_347_i0) ∪ commonEnvelope childrenD_347_i0).erase (0, 3) := by
  exact required_eq_combination childrenC_347_i0 childrenD_347_i0 (0, 3) required_347_i0
    (by decide +kernel) child_required_sub_347_i0 common_sub_347_i0 required_origin_347_i0
theorem envelope_origin_347_i0 : ∀ x ∈ envelope_347_i0,
    x = (0, 3) ∨ ∃ j, x ∈ childrenD_347_i0 j := by decide +kernel
theorem envelope_exact_347_i0 : envelope_347_i0 =
    insert (0, 3) (Finset.univ.biUnion childrenD_347_i0) := by
  exact envelope_eq_combination childrenD_347_i0 (0, 3) envelope_347_i0
    pivot_mem_347_i0 child_envelope_sub_347_i0 envelope_origin_347_i0
def checked_347_i0 : CheckedCard where
  required := required_347_i0
  envelope := envelope_347_i0
  height := height_347_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_347_i0
def height_347 : ℕ := 5
def childrenH_347 : Fin 3 → ℕ := ![height_20, height_29, height_347_i0]
theorem height_exact_347 : height_347 = 1 + Finset.univ.sup childrenH_347 := by decide +kernel
theorem required_origin_347 : ∀ x ∈ required_347,
    (∃ j, x ∈ childrenC_347 j) ∨ ∀ j, x ∈ childrenD_347 j := by decide +kernel
theorem required_exact_347 : required_347 =
    ((Finset.univ.biUnion childrenC_347) ∪ commonEnvelope childrenD_347).erase (1, 3) := by
  exact required_eq_combination childrenC_347 childrenD_347 (1, 3) required_347
    (by decide +kernel) child_required_sub_347 common_sub_347 required_origin_347
theorem envelope_origin_347 : ∀ x ∈ envelope_347,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_347 j := by decide +kernel
theorem envelope_exact_347 : envelope_347 =
    insert (1, 3) (Finset.univ.biUnion childrenD_347) := by
  exact envelope_eq_combination childrenD_347 (1, 3) envelope_347
    pivot_mem_347 child_envelope_sub_347 envelope_origin_347
def checked_347 : CheckedCard where
  required := required_347
  envelope := envelope_347
  height := height_347
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_347
def height_352 : ℕ := 5
def childrenH_352 : Fin 2 → ℕ := ![height_4, height_351]
theorem height_exact_352 : height_352 = 1 + Finset.univ.sup childrenH_352 := by decide +kernel
theorem required_origin_352 : ∀ x ∈ required_352,
    (∃ j, x ∈ childrenC_352 j) ∨ ∀ j, x ∈ childrenD_352 j := by decide +kernel
theorem required_exact_352 : required_352 =
    ((Finset.univ.biUnion childrenC_352) ∪ commonEnvelope childrenD_352).erase (4, 2) := by
  exact required_eq_combination childrenC_352 childrenD_352 (4, 2) required_352
    (by decide +kernel) child_required_sub_352 common_sub_352 required_origin_352
theorem envelope_origin_352 : ∀ x ∈ envelope_352,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_352 j := by decide +kernel
theorem envelope_exact_352 : envelope_352 =
    insert (4, 2) (Finset.univ.biUnion childrenD_352) := by
  exact envelope_eq_combination childrenD_352 (4, 2) envelope_352
    pivot_mem_352 child_envelope_sub_352 envelope_origin_352
def checked_352 : CheckedCard where
  required := required_352
  envelope := envelope_352
  height := height_352
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_352
def height_355 : ℕ := 5
def childrenH_355 : Fin 2 → ℕ := ![height_8, height_354]
theorem height_exact_355 : height_355 = 1 + Finset.univ.sup childrenH_355 := by decide +kernel
theorem required_origin_355 : ∀ x ∈ required_355,
    (∃ j, x ∈ childrenC_355 j) ∨ ∀ j, x ∈ childrenD_355 j := by decide +kernel
theorem required_exact_355 : required_355 =
    ((Finset.univ.biUnion childrenC_355) ∪ commonEnvelope childrenD_355).erase (3, 4) := by
  exact required_eq_combination childrenC_355 childrenD_355 (3, 4) required_355
    (by decide +kernel) child_required_sub_355 common_sub_355 required_origin_355
theorem envelope_origin_355 : ∀ x ∈ envelope_355,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_355 j := by decide +kernel
theorem envelope_exact_355 : envelope_355 =
    insert (3, 4) (Finset.univ.biUnion childrenD_355) := by
  exact envelope_eq_combination childrenD_355 (3, 4) envelope_355
    pivot_mem_355 child_envelope_sub_355 envelope_origin_355
def checked_355 : CheckedCard where
  required := required_355
  envelope := envelope_355
  height := height_355
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_355
end SnakyPrototype.Certificate21

end OAI
