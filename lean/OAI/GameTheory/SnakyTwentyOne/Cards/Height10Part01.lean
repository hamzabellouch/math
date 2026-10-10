import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part03
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_399 : Finset Cell := ⟨(([(2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_399 : Finset Cell := ⟨(([(0, 3), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 2), (6, 4), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_399 : Fin 5 → Finset Cell := ![(placed21 0 (1, 1) required_12), (placed21 0 (0, 1) required_135), (placed21 1 (0, 2) required_181), required_396, (placed21 4 (0, 8) required_396)]
def childrenD_399 : Fin 5 → Finset Cell := ![(placed21 0 (1, 1) envelope_12), (placed21 0 (0, 1) envelope_135), (placed21 1 (0, 2) envelope_181), envelope_396, (placed21 4 (0, 8) envelope_396)]
theorem common_sub_399 : commonEnvelope childrenD_399 ⊆ insert (2, 5) required_399 := by decide +kernel
theorem child_required_sub_399 : ∀ j, childrenC_399 j ⊆ insert (2, 5) required_399 := by decide +kernel
theorem child_envelope_sub_399 : ∀ j, childrenD_399 j ⊆ envelope_399 := by decide +kernel
theorem pivot_mem_399 : (2, 5) ∈ envelope_399 := by decide +kernel
theorem children_work_399 : ∀ j, Template HasSnaky 9 (childrenC_399 j) (childrenD_399 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_135 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_181 1 (0, 2)).mono (by decide +kernel)
  · exact row_works_396.mono (by decide +kernel)
  · exact (placed21_template row_works_396 4 (0, 8)).mono (by decide +kernel)
theorem row_works_399 : Template HasSnaky 10 required_399 envelope_399 := by
  refine compose HasSnaky 9 childrenC_399 childrenD_399 children_work_399 (2, 5)
    required_399 envelope_399 pivot_mem_399 child_required_sub_399 child_envelope_sub_399 ?_
  intro b hb
  exact common_sub_399 (mem_commonEnvelope childrenD_399 b hb)
def required_401 : Finset Cell := ⟨(([(0, 3), (1, 3), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_401 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 2), (7, 3), (7, 4), (7, 5), (8, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_401 : Fin 2 → Finset Cell := ![(placed21 6 (4, 4) required_3), (placed21 4 (2, 7) required_397)]
def childrenD_401 : Fin 2 → Finset Cell := ![(placed21 6 (4, 4) envelope_3), (placed21 4 (2, 7) envelope_397)]
theorem common_sub_401 : commonEnvelope childrenD_401 ⊆ insert (2, 4) required_401 := by decide +kernel
theorem child_required_sub_401 : ∀ j, childrenC_401 j ⊆ insert (2, 4) required_401 := by decide +kernel
theorem child_envelope_sub_401 : ∀ j, childrenD_401 j ⊆ envelope_401 := by decide +kernel
theorem pivot_mem_401 : (2, 4) ∈ envelope_401 := by decide +kernel
theorem children_work_401 : ∀ j, Template HasSnaky 9 (childrenC_401 j) (childrenD_401 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 6 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_397 4 (2, 7)).mono (by decide +kernel)
theorem row_works_401 : Template HasSnaky 10 required_401 envelope_401 := by
  refine compose HasSnaky 9 childrenC_401 childrenD_401 children_work_401 (2, 4)
    required_401 envelope_401 pivot_mem_401 child_required_sub_401 child_envelope_sub_401 ?_
  intro b hb
  exact common_sub_401 (mem_commonEnvelope childrenD_401 b hb)
def required_408 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_408 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_408 : Fin 3 → Finset Cell := ![(placed21 6 (1, 6) required_44), (placed21 0 (0, 1) required_127), (placed21 4 (0, 6) required_407)]
def childrenD_408 : Fin 3 → Finset Cell := ![(placed21 6 (1, 6) envelope_44), (placed21 0 (0, 1) envelope_127), (placed21 4 (0, 6) envelope_407)]
theorem common_sub_408 : commonEnvelope childrenD_408 ⊆ insert (1, 5) required_408 := by decide +kernel
theorem child_required_sub_408 : ∀ j, childrenC_408 j ⊆ insert (1, 5) required_408 := by decide +kernel
theorem child_envelope_sub_408 : ∀ j, childrenD_408 j ⊆ envelope_408 := by decide +kernel
theorem pivot_mem_408 : (1, 5) ∈ envelope_408 := by decide +kernel
theorem children_work_408 : ∀ j, Template HasSnaky 9 (childrenC_408 j) (childrenD_408 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 6 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_127 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_407 4 (0, 6)).mono (by decide +kernel)
theorem row_works_408 : Template HasSnaky 10 required_408 envelope_408 := by
  refine compose HasSnaky 9 childrenC_408 childrenD_408 children_work_408 (1, 5)
    required_408 envelope_408 pivot_mem_408 child_required_sub_408 child_envelope_sub_408 ?_
  intro b hb
  exact common_sub_408 (mem_commonEnvelope childrenD_408 b hb)
def required_409 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_409 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_409 : Fin 3 → Finset Cell := ![(placed21 6 (1, 6) required_44), (placed21 0 (0, 1) required_127), (placed21 4 (0, 6) required_407)]
def childrenD_409 : Fin 3 → Finset Cell := ![(placed21 6 (1, 6) envelope_44), (placed21 0 (0, 1) envelope_127), (placed21 4 (0, 6) envelope_407)]
theorem common_sub_409 : commonEnvelope childrenD_409 ⊆ insert (1, 4) required_409 := by decide +kernel
theorem child_required_sub_409 : ∀ j, childrenC_409 j ⊆ insert (1, 4) required_409 := by decide +kernel
theorem child_envelope_sub_409 : ∀ j, childrenD_409 j ⊆ envelope_409 := by decide +kernel
theorem pivot_mem_409 : (1, 4) ∈ envelope_409 := by decide +kernel
theorem children_work_409 : ∀ j, Template HasSnaky 9 (childrenC_409 j) (childrenD_409 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 6 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_127 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_407 4 (0, 6)).mono (by decide +kernel)
theorem row_works_409 : Template HasSnaky 10 required_409 envelope_409 := by
  refine compose HasSnaky 9 childrenC_409 childrenD_409 children_work_409 (1, 4)
    required_409 envelope_409 pivot_mem_409 child_required_sub_409 child_envelope_sub_409 ?_
  intro b hb
  exact common_sub_409 (mem_commonEnvelope childrenD_409 b hb)
def required_410 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_410 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (0, 7), (0, 8), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_410 : Fin 4 → Finset Cell := ![(placed21 0 (0, 2) required_10), (placed21 2 (2, 1) required_12), (placed21 4 (0, 7) required_12), (placed21 4 (0, 6) required_407)]
def childrenD_410 : Fin 4 → Finset Cell := ![(placed21 0 (0, 2) envelope_10), (placed21 2 (2, 1) envelope_12), (placed21 4 (0, 7) envelope_12), (placed21 4 (0, 6) envelope_407)]
theorem common_sub_410 : commonEnvelope childrenD_410 ⊆ insert (1, 5) required_410 := by decide +kernel
theorem child_required_sub_410 : ∀ j, childrenC_410 j ⊆ insert (1, 5) required_410 := by decide +kernel
theorem child_envelope_sub_410 : ∀ j, childrenD_410 j ⊆ envelope_410 := by decide +kernel
theorem pivot_mem_410 : (1, 5) ∈ envelope_410 := by decide +kernel
theorem children_work_410 : ∀ j, Template HasSnaky 9 (childrenC_410 j) (childrenD_410 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_12 2 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_12 4 (0, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_407 4 (0, 6)).mono (by decide +kernel)
theorem row_works_410 : Template HasSnaky 10 required_410 envelope_410 := by
  refine compose HasSnaky 9 childrenC_410 childrenD_410 children_work_410 (1, 5)
    required_410 envelope_410 pivot_mem_410 child_required_sub_410 child_envelope_sub_410 ?_
  intro b hb
  exact common_sub_410 (mem_commonEnvelope childrenD_410 b hb)
def required_411 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_411 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_411 : Fin 3 → Finset Cell := ![(placed21 6 (1, 6) required_15), (placed21 4 (0, 7) required_65), (placed21 4 (0, 6) required_407)]
def childrenD_411 : Fin 3 → Finset Cell := ![(placed21 6 (1, 6) envelope_15), (placed21 4 (0, 7) envelope_65), (placed21 4 (0, 6) envelope_407)]
theorem common_sub_411 : commonEnvelope childrenD_411 ⊆ insert (1, 5) required_411 := by decide +kernel
theorem child_required_sub_411 : ∀ j, childrenC_411 j ⊆ insert (1, 5) required_411 := by decide +kernel
theorem child_envelope_sub_411 : ∀ j, childrenD_411 j ⊆ envelope_411 := by decide +kernel
theorem pivot_mem_411 : (1, 5) ∈ envelope_411 := by decide +kernel
theorem children_work_411 : ∀ j, Template HasSnaky 9 (childrenC_411 j) (childrenD_411 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_15 6 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_65 4 (0, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_407 4 (0, 6)).mono (by decide +kernel)
theorem row_works_411 : Template HasSnaky 10 required_411 envelope_411 := by
  refine compose HasSnaky 9 childrenC_411 childrenD_411 children_work_411 (1, 5)
    required_411 envelope_411 pivot_mem_411 child_required_sub_411 child_envelope_sub_411 ?_
  intro b hb
  exact common_sub_411 (mem_commonEnvelope childrenD_411 b hb)
def required_444 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_444 : Finset Cell := ⟨(([(0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_444 : Fin 4 → Finset Cell := ![(placed21 0 (1, 0) required_7), (placed21 1 (0, 1) required_8), (placed21 2 (2, 0) required_9), (placed21 4 (0, 5) required_443)]
def childrenD_444 : Fin 4 → Finset Cell := ![(placed21 0 (1, 0) envelope_7), (placed21 1 (0, 1) envelope_8), (placed21 2 (2, 0) envelope_9), (placed21 4 (0, 5) envelope_443)]
theorem common_sub_444 : commonEnvelope childrenD_444 ⊆ insert (1, 4) required_444 := by decide +kernel
theorem child_required_sub_444 : ∀ j, childrenC_444 j ⊆ insert (1, 4) required_444 := by decide +kernel
theorem child_envelope_sub_444 : ∀ j, childrenD_444 j ⊆ envelope_444 := by decide +kernel
theorem pivot_mem_444 : (1, 4) ∈ envelope_444 := by decide +kernel
theorem children_work_444 : ∀ j, Template HasSnaky 9 (childrenC_444 j) (childrenD_444 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 2 (2, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_443 4 (0, 5)).mono (by decide +kernel)
theorem row_works_444 : Template HasSnaky 10 required_444 envelope_444 := by
  refine compose HasSnaky 9 childrenC_444 childrenD_444 children_work_444 (1, 4)
    required_444 envelope_444 pivot_mem_444 child_required_sub_444 child_envelope_sub_444 ?_
  intro b hb
  exact common_sub_444 (mem_commonEnvelope childrenD_444 b hb)
def required_459 : Finset Cell := ⟨(([(1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_459 : Finset Cell := ⟨(([(0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 5), (4, 6), (4, 7), (4, 8), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_459 : Fin 8 → Finset Cell := ![(placed21 2 (2, 2) required_12), (placed21 2 (2, 2) required_13), (placed21 6 (2, 8) required_33), (placed21 2 (2, 2) required_189), (placed21 4 (0, 8) required_192), (placed21 2 (2, 1) required_369), (placed21 0 (0, 3) required_457), (placed21 4 (0, 7) required_458)]
def childrenD_459 : Fin 8 → Finset Cell := ![(placed21 2 (2, 2) envelope_12), (placed21 2 (2, 2) envelope_13), (placed21 6 (2, 8) envelope_33), (placed21 2 (2, 2) envelope_189), (placed21 4 (0, 8) envelope_192), (placed21 2 (2, 1) envelope_369), (placed21 0 (0, 3) envelope_457), (placed21 4 (0, 7) envelope_458)]
theorem common_sub_459 : commonEnvelope childrenD_459 ⊆ insert (1, 6) required_459 := by decide +kernel
theorem child_required_sub_459 : ∀ j, childrenC_459 j ⊆ insert (1, 6) required_459 := by decide +kernel
theorem child_envelope_sub_459 : ∀ j, childrenD_459 j ⊆ envelope_459 := by decide +kernel
theorem pivot_mem_459 : (1, 6) ∈ envelope_459 := by decide +kernel
theorem children_work_459 : ∀ j, Template HasSnaky 9 (childrenC_459 j) (childrenD_459 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 2 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_13 2 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_33 6 (2, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_189 2 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_192 4 (0, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_369 2 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_457 0 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_458 4 (0, 7)).mono (by decide +kernel)
theorem row_works_459 : Template HasSnaky 10 required_459 envelope_459 := by
  refine compose HasSnaky 9 childrenC_459 childrenD_459 children_work_459 (1, 6)
    required_459 envelope_459 pivot_mem_459 child_required_sub_459 child_envelope_sub_459 ?_
  intro b hb
  exact common_sub_459 (mem_commonEnvelope childrenD_459 b hb)
def required_460 : Finset Cell := ⟨(([(1, 3), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_460 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 6), (0, 7), (0, 8), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (5, 1), (5, 2), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_460 : Fin 5 → Finset Cell := ![(placed21 0 (0, 1) required_13), (placed21 2 (2, 1) required_14), (placed21 0 (0, 1) required_33), (placed21 4 (0, 6) required_457), (placed21 0 (0, 2) required_458)]
def childrenD_460 : Fin 5 → Finset Cell := ![(placed21 0 (0, 1) envelope_13), (placed21 2 (2, 1) envelope_14), (placed21 0 (0, 1) envelope_33), (placed21 4 (0, 6) envelope_457), (placed21 0 (0, 2) envelope_458)]
theorem common_sub_460 : commonEnvelope childrenD_460 ⊆ insert (1, 4) required_460 := by decide +kernel
theorem child_required_sub_460 : ∀ j, childrenC_460 j ⊆ insert (1, 4) required_460 := by decide +kernel
theorem child_envelope_sub_460 : ∀ j, childrenD_460 j ⊆ envelope_460 := by decide +kernel
theorem pivot_mem_460 : (1, 4) ∈ envelope_460 := by decide +kernel
theorem children_work_460 : ∀ j, Template HasSnaky 9 (childrenC_460 j) (childrenD_460 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_14 2 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_33 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_457 4 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_458 0 (0, 2)).mono (by decide +kernel)
theorem row_works_460 : Template HasSnaky 10 required_460 envelope_460 := by
  refine compose HasSnaky 9 childrenC_460 childrenD_460 children_work_460 (1, 4)
    required_460 envelope_460 pivot_mem_460 child_required_sub_460 child_envelope_sub_460 ?_
  intro b hb
  exact common_sub_460 (mem_commonEnvelope childrenD_460 b hb)
def required_461 : Finset Cell := ⟨(([(0, 2), (1, 2), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_461 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 2), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 2), (5, 3), (5, 4), (5, 5), (6, 3), (6, 4), (6, 5), (7, 3), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_461 : Fin 4 → Finset Cell := ![(placed21 5 (4, 1) required_28), required_100, required_429, (placed21 0 (2, 0) required_457)]
def childrenD_461 : Fin 4 → Finset Cell := ![(placed21 5 (4, 1) envelope_28), envelope_100, envelope_429, (placed21 0 (2, 0) envelope_457)]
theorem common_sub_461 : commonEnvelope childrenD_461 ⊆ insert (3, 3) required_461 := by decide +kernel
theorem child_required_sub_461 : ∀ j, childrenC_461 j ⊆ insert (3, 3) required_461 := by decide +kernel
theorem child_envelope_sub_461 : ∀ j, childrenD_461 j ⊆ envelope_461 := by decide +kernel
theorem pivot_mem_461 : (3, 3) ∈ envelope_461 := by decide +kernel
theorem children_work_461 : ∀ j, Template HasSnaky 9 (childrenC_461 j) (childrenD_461 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_28 5 (4, 1)).mono (by decide +kernel)
  · exact row_works_100.mono (by decide +kernel)
  · exact row_works_429.mono (by decide +kernel)
  · exact (placed21_template row_works_457 0 (2, 0)).mono (by decide +kernel)
theorem row_works_461 : Template HasSnaky 10 required_461 envelope_461 := by
  refine compose HasSnaky 9 childrenC_461 childrenD_461 children_work_461 (3, 3)
    required_461 envelope_461 pivot_mem_461 child_required_sub_461 child_envelope_sub_461 ?_
  intro b hb
  exact common_sub_461 (mem_commonEnvelope childrenD_461 b hb)
def required_475 : Finset Cell := ⟨(([(2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_475 : Finset Cell := ⟨(([(0, 5), (1, 0), (1, 1), (1, 2), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 4), (5, 5), (5, 6), (5, 7), (6, 4), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_475 : Fin 5 → Finset Cell := ![(placed21 4 (1, 7) required_13), (placed21 6 (3, 7) required_14), (placed21 4 (1, 7) required_31), (placed21 4 (0, 8) required_396), (placed21 1 (0, 2) required_474)]
def childrenD_475 : Fin 5 → Finset Cell := ![(placed21 4 (1, 7) envelope_13), (placed21 6 (3, 7) envelope_14), (placed21 4 (1, 7) envelope_31), (placed21 4 (0, 8) envelope_396), (placed21 1 (0, 2) envelope_474)]
theorem common_sub_475 : commonEnvelope childrenD_475 ⊆ insert (2, 5) required_475 := by decide +kernel
theorem child_required_sub_475 : ∀ j, childrenC_475 j ⊆ insert (2, 5) required_475 := by decide +kernel
theorem child_envelope_sub_475 : ∀ j, childrenD_475 j ⊆ envelope_475 := by decide +kernel
theorem pivot_mem_475 : (2, 5) ∈ envelope_475 := by decide +kernel
theorem children_work_475 : ∀ j, Template HasSnaky 9 (childrenC_475 j) (childrenD_475 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 4 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_14 6 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_31 4 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_396 4 (0, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_474 1 (0, 2)).mono (by decide +kernel)
theorem row_works_475 : Template HasSnaky 10 required_475 envelope_475 := by
  refine compose HasSnaky 9 childrenC_475 childrenD_475 children_work_475 (2, 5)
    required_475 envelope_475 pivot_mem_475 child_required_sub_475 child_envelope_sub_475 ?_
  intro b hb
  exact common_sub_475 (mem_commonEnvelope childrenD_475 b hb)
def required_476 : Finset Cell := ⟨(([(1, 3), (1, 4), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_476 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_476 : Fin 5 → Finset Cell := ![(placed21 0 (2, 1) required_12), (placed21 2 (4, 1) required_12), (placed21 4 (2, 7) required_12), (placed21 2 (4, 2) required_264), (placed21 3 (1, 6) required_474)]
def childrenD_476 : Fin 5 → Finset Cell := ![(placed21 0 (2, 1) envelope_12), (placed21 2 (4, 1) envelope_12), (placed21 4 (2, 7) envelope_12), (placed21 2 (4, 2) envelope_264), (placed21 3 (1, 6) envelope_474)]
theorem common_sub_476 : commonEnvelope childrenD_476 ⊆ insert (3, 5) required_476 := by decide +kernel
theorem child_required_sub_476 : ∀ j, childrenC_476 j ⊆ insert (3, 5) required_476 := by decide +kernel
theorem child_envelope_sub_476 : ∀ j, childrenD_476 j ⊆ envelope_476 := by decide +kernel
theorem pivot_mem_476 : (3, 5) ∈ envelope_476 := by decide +kernel
theorem children_work_476 : ∀ j, Template HasSnaky 9 (childrenC_476 j) (childrenD_476 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 0 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_12 2 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_12 4 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_264 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_474 3 (1, 6)).mono (by decide +kernel)
theorem row_works_476 : Template HasSnaky 10 required_476 envelope_476 := by
  refine compose HasSnaky 9 childrenC_476 childrenD_476 children_work_476 (3, 5)
    required_476 envelope_476 pivot_mem_476 child_required_sub_476 child_envelope_sub_476 ?_
  intro b hb
  exact common_sub_476 (mem_commonEnvelope childrenD_476 b hb)
def required_479_i0 : Finset Cell := ⟨(([(1, 4), (3, 3), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_479_i0 : Finset Cell := ⟨(([(0, 4), (0, 5), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_479_i0 : Fin 2 → Finset Cell := ![(placed21 7 (4, 5) required_8), (placed21 5 (5, 2) required_386)]
def childrenD_479_i0 : Fin 2 → Finset Cell := ![(placed21 7 (4, 5) envelope_8), (placed21 5 (5, 2) envelope_386)]
theorem common_sub_479_i0 : commonEnvelope childrenD_479_i0 ⊆ insert (3, 2) required_479_i0 := by decide +kernel
theorem child_required_sub_479_i0 : ∀ j, childrenC_479_i0 j ⊆ insert (3, 2) required_479_i0 := by decide +kernel
theorem child_envelope_sub_479_i0 : ∀ j, childrenD_479_i0 j ⊆ envelope_479_i0 := by decide +kernel
theorem pivot_mem_479_i0 : (3, 2) ∈ envelope_479_i0 := by decide +kernel
theorem children_work_479_i0 : ∀ j, Template HasSnaky 5 (childrenC_479_i0 j) (childrenD_479_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 7 (4, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_386 5 (5, 2)).mono (by decide +kernel)
theorem row_works_479_i0 : Template HasSnaky 6 required_479_i0 envelope_479_i0 := by
  refine compose HasSnaky 5 childrenC_479_i0 childrenD_479_i0 children_work_479_i0 (3, 2)
    required_479_i0 envelope_479_i0 pivot_mem_479_i0 child_required_sub_479_i0 child_envelope_sub_479_i0 ?_
  intro b hb
  exact common_sub_479_i0 (mem_commonEnvelope childrenD_479_i0 b hb)
def required_479 : Finset Cell := ⟨(([(1, 4), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_479 : Finset Cell := ⟨(([(0, 4), (0, 5), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 5), (2, 6), (2, 7), (2, 8), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 4), (5, 5), (5, 6), (5, 7), (6, 5), (6, 6), (6, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_479 : Fin 7 → Finset Cell := ![(placed21 6 (4, 7) required_14), (placed21 4 (2, 7) required_31), (placed21 1 (1, 2) required_181), (placed21 4 (2, 7) required_367), required_479_i0, (placed21 5 (6, 2) required_435), (placed21 1 (1, 2) required_474)]
def childrenD_479 : Fin 7 → Finset Cell := ![(placed21 6 (4, 7) envelope_14), (placed21 4 (2, 7) envelope_31), (placed21 1 (1, 2) envelope_181), (placed21 4 (2, 7) envelope_367), envelope_479_i0, (placed21 5 (6, 2) envelope_435), (placed21 1 (1, 2) envelope_474)]
theorem common_sub_479 : commonEnvelope childrenD_479 ⊆ insert (3, 5) required_479 := by decide +kernel
theorem child_required_sub_479 : ∀ j, childrenC_479 j ⊆ insert (3, 5) required_479 := by decide +kernel
theorem child_envelope_sub_479 : ∀ j, childrenD_479 j ⊆ envelope_479 := by decide +kernel
theorem pivot_mem_479 : (3, 5) ∈ envelope_479 := by decide +kernel
theorem children_work_479 : ∀ j, Template HasSnaky 9 (childrenC_479 j) (childrenD_479 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_14 6 (4, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_31 4 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_181 1 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_367 4 (2, 7)).mono (by decide +kernel)
  · exact row_works_479_i0.mono (by decide +kernel)
  · exact (placed21_template row_works_435 5 (6, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_474 1 (1, 2)).mono (by decide +kernel)
theorem row_works_479 : Template HasSnaky 10 required_479 envelope_479 := by
  refine compose HasSnaky 9 childrenC_479 childrenD_479 children_work_479 (3, 5)
    required_479 envelope_479 pivot_mem_479 child_required_sub_479 child_envelope_sub_479 ?_
  intro b hb
  exact common_sub_479 (mem_commonEnvelope childrenD_479 b hb)
def required_480 : Finset Cell := ⟨(([(3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_480 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 2), (5, 3), (5, 4), (6, 2), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_480 : Fin 7 → Finset Cell := ![(placed21 4 (2, 7) required_13), (placed21 4 (2, 7) required_14), (placed21 2 (4, 1) required_192), (placed21 1 (0, 1) required_298), (placed21 7 (6, 6) required_435), (placed21 7 (5, 6) required_474), (placed21 5 (5, 2) required_477)]
def childrenD_480 : Fin 7 → Finset Cell := ![(placed21 4 (2, 7) envelope_13), (placed21 4 (2, 7) envelope_14), (placed21 2 (4, 1) envelope_192), (placed21 1 (0, 1) envelope_298), (placed21 7 (6, 6) envelope_435), (placed21 7 (5, 6) envelope_474), (placed21 5 (5, 2) envelope_477)]
theorem common_sub_480 : commonEnvelope childrenD_480 ⊆ insert (3, 3) required_480 := by decide +kernel
theorem child_required_sub_480 : ∀ j, childrenC_480 j ⊆ insert (3, 3) required_480 := by decide +kernel
theorem child_envelope_sub_480 : ∀ j, childrenD_480 j ⊆ envelope_480 := by decide +kernel
theorem pivot_mem_480 : (3, 3) ∈ envelope_480 := by decide +kernel
theorem children_work_480 : ∀ j, Template HasSnaky 9 (childrenC_480 j) (childrenD_480 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 4 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_14 4 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_192 2 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_298 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 7 (6, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_474 7 (5, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_477 5 (5, 2)).mono (by decide +kernel)
theorem row_works_480 : Template HasSnaky 10 required_480 envelope_480 := by
  refine compose HasSnaky 9 childrenC_480 childrenD_480 children_work_480 (3, 3)
    required_480 envelope_480 pivot_mem_480 child_required_sub_480 child_envelope_sub_480 ?_
  intro b hb
  exact common_sub_480 (mem_commonEnvelope childrenD_480 b hb)
def required_481 : Finset Cell := ⟨(([(2, 3), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_481 : Finset Cell := ⟨(([(0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 6), (1, 7), (1, 8), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_481 : Fin 5 → Finset Cell := ![(placed21 0 (1, 1) required_13), (placed21 2 (3, 1) required_14), (placed21 0 (1, 1) required_33), (placed21 4 (1, 6) required_457), (placed21 1 (0, 2) required_477)]
def childrenD_481 : Fin 5 → Finset Cell := ![(placed21 0 (1, 1) envelope_13), (placed21 2 (3, 1) envelope_14), (placed21 0 (1, 1) envelope_33), (placed21 4 (1, 6) envelope_457), (placed21 1 (0, 2) envelope_477)]
theorem common_sub_481 : commonEnvelope childrenD_481 ⊆ insert (2, 4) required_481 := by decide +kernel
theorem child_required_sub_481 : ∀ j, childrenC_481 j ⊆ insert (2, 4) required_481 := by decide +kernel
theorem child_envelope_sub_481 : ∀ j, childrenD_481 j ⊆ envelope_481 := by decide +kernel
theorem pivot_mem_481 : (2, 4) ∈ envelope_481 := by decide +kernel
theorem children_work_481 : ∀ j, Template HasSnaky 9 (childrenC_481 j) (childrenD_481 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_14 2 (3, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_33 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_457 4 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_477 1 (0, 2)).mono (by decide +kernel)
theorem row_works_481 : Template HasSnaky 10 required_481 envelope_481 := by
  refine compose HasSnaky 9 childrenC_481 childrenD_481 children_work_481 (2, 4)
    required_481 envelope_481 pivot_mem_481 child_required_sub_481 child_envelope_sub_481 ?_
  intro b hb
  exact common_sub_481 (mem_commonEnvelope childrenD_481 b hb)
def required_483 : Finset Cell := ⟨(([(2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_483 : Finset Cell := ⟨(([(0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 6), (1, 7), (1, 8), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (5, 4), (6, 2), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_483 : Fin 5 → Finset Cell := ![(placed21 0 (1, 1) required_13), (placed21 2 (3, 1) required_14), (placed21 0 (1, 1) required_33), (placed21 0 (1, 2) required_458), (placed21 3 (0, 6) required_474)]
def childrenD_483 : Fin 5 → Finset Cell := ![(placed21 0 (1, 1) envelope_13), (placed21 2 (3, 1) envelope_14), (placed21 0 (1, 1) envelope_33), (placed21 0 (1, 2) envelope_458), (placed21 3 (0, 6) envelope_474)]
theorem common_sub_483 : commonEnvelope childrenD_483 ⊆ insert (2, 5) required_483 := by decide +kernel
theorem child_required_sub_483 : ∀ j, childrenC_483 j ⊆ insert (2, 5) required_483 := by decide +kernel
theorem child_envelope_sub_483 : ∀ j, childrenD_483 j ⊆ envelope_483 := by decide +kernel
theorem pivot_mem_483 : (2, 5) ∈ envelope_483 := by decide +kernel
theorem children_work_483 : ∀ j, Template HasSnaky 9 (childrenC_483 j) (childrenD_483 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_14 2 (3, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_33 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_458 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_474 3 (0, 6)).mono (by decide +kernel)
theorem row_works_483 : Template HasSnaky 10 required_483 envelope_483 := by
  refine compose HasSnaky 9 childrenC_483 childrenD_483 children_work_483 (2, 5)
    required_483 envelope_483 pivot_mem_483 child_required_sub_483 child_envelope_sub_483 ?_
  intro b hb
  exact common_sub_483 (mem_commonEnvelope childrenD_483 b hb)
def required_491_i0 : Finset Cell := ⟨(([(1, 2), (3, 3), (4, 1), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_491_i0 : Finset Cell := ⟨(([(0, 4), (1, 2), (1, 4), (2, 2), (2, 3), (2, 4), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (5, 3), (5, 4), (6, 3), (6, 4), (7, 4), (8, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_491_i0 : Fin 4 → Finset Cell := ![(placed21 3 (2, 4) required_60), (placed21 7 (6, 4) required_60), (placed21 4 (3, 4) required_83), (placed21 1 (1, 2) required_106)]
def childrenD_491_i0 : Fin 4 → Finset Cell := ![(placed21 3 (2, 4) envelope_60), (placed21 7 (6, 4) envelope_60), (placed21 4 (3, 4) envelope_83), (placed21 1 (1, 2) envelope_106)]
theorem common_sub_491_i0 : commonEnvelope childrenD_491_i0 ⊆ insert (5, 3) required_491_i0 := by decide +kernel
theorem child_required_sub_491_i0 : ∀ j, childrenC_491_i0 j ⊆ insert (5, 3) required_491_i0 := by decide +kernel
theorem child_envelope_sub_491_i0 : ∀ j, childrenD_491_i0 j ⊆ envelope_491_i0 := by decide +kernel
theorem pivot_mem_491_i0 : (5, 3) ∈ envelope_491_i0 := by decide +kernel
theorem children_work_491_i0 : ∀ j, Template HasSnaky 4 (childrenC_491_i0 j) (childrenD_491_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_60 3 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_60 7 (6, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_83 4 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_106 1 (1, 2)).mono (by decide +kernel)
theorem row_works_491_i0 : Template HasSnaky 5 required_491_i0 envelope_491_i0 := by
  refine compose HasSnaky 4 childrenC_491_i0 childrenD_491_i0 children_work_491_i0 (5, 3)
    required_491_i0 envelope_491_i0 pivot_mem_491_i0 child_required_sub_491_i0 child_envelope_sub_491_i0 ?_
  intro b hb
  exact common_sub_491_i0 (mem_commonEnvelope childrenD_491_i0 b hb)
def required_491_i1 : Finset Cell := ⟨(([(1, 2), (3, 3), (4, 1), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_491_i1 : Finset Cell := ⟨(([(1, 2), (2, 2), (2, 3), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 1), (5, 3), (5, 4), (5, 5), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, 2), (8, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_491_i1 : Fin 3 → Finset Cell := ![(placed21 3 (2, 4) required_60), (placed21 7 (5, 3) required_70), (placed21 4 (2, 5) required_345)]
def childrenD_491_i1 : Fin 3 → Finset Cell := ![(placed21 3 (2, 4) envelope_60), (placed21 7 (5, 3) envelope_70), (placed21 4 (2, 5) envelope_345)]
theorem common_sub_491_i1 : commonEnvelope childrenD_491_i1 ⊆ insert (5, 3) required_491_i1 := by decide +kernel
theorem child_required_sub_491_i1 : ∀ j, childrenC_491_i1 j ⊆ insert (5, 3) required_491_i1 := by decide +kernel
theorem child_envelope_sub_491_i1 : ∀ j, childrenD_491_i1 j ⊆ envelope_491_i1 := by decide +kernel
theorem pivot_mem_491_i1 : (5, 3) ∈ envelope_491_i1 := by decide +kernel
theorem children_work_491_i1 : ∀ j, Template HasSnaky 8 (childrenC_491_i1 j) (childrenD_491_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_60 3 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_70 7 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_345 4 (2, 5)).mono (by decide +kernel)
theorem row_works_491_i1 : Template HasSnaky 9 required_491_i1 envelope_491_i1 := by
  refine compose HasSnaky 8 childrenC_491_i1 childrenD_491_i1 children_work_491_i1 (5, 3)
    required_491_i1 envelope_491_i1 pivot_mem_491_i1 child_required_sub_491_i1 child_envelope_sub_491_i1 ?_
  intro b hb
  exact common_sub_491_i1 (mem_commonEnvelope childrenD_491_i1 b hb)
def required_491 : Finset Cell := ⟨(([(1, 2), (4, 1), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_491 : Finset Cell := ⟨(([(0, 4), (1, 2), (1, 4), (2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 1), (5, 3), (5, 4), (5, 5), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, 2), (8, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_491 : Fin 4 → Finset Cell := ![(placed21 2 (4, 0) required_44), (placed21 0 (1, 1) required_270), required_491_i0, required_491_i1]
def childrenD_491 : Fin 4 → Finset Cell := ![(placed21 2 (4, 0) envelope_44), (placed21 0 (1, 1) envelope_270), envelope_491_i0, envelope_491_i1]
theorem common_sub_491 : commonEnvelope childrenD_491 ⊆ insert (3, 3) required_491 := by decide +kernel
theorem child_required_sub_491 : ∀ j, childrenC_491 j ⊆ insert (3, 3) required_491 := by decide +kernel
theorem child_envelope_sub_491 : ∀ j, childrenD_491 j ⊆ envelope_491 := by decide +kernel
theorem pivot_mem_491 : (3, 3) ∈ envelope_491 := by decide +kernel
theorem children_work_491 : ∀ j, Template HasSnaky 9 (childrenC_491 j) (childrenD_491 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 2 (4, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_270 0 (1, 1)).mono (by decide +kernel)
  · exact row_works_491_i0.mono (by decide +kernel)
  · exact row_works_491_i1.mono (by decide +kernel)
theorem row_works_491 : Template HasSnaky 10 required_491 envelope_491 := by
  refine compose HasSnaky 9 childrenC_491 childrenD_491 children_work_491 (3, 3)
    required_491 envelope_491 pivot_mem_491 child_required_sub_491 child_envelope_sub_491 ?_
  intro b hb
  exact common_sub_491 (mem_commonEnvelope childrenD_491 b hb)
def required_508 : Finset Cell := ⟨(([(2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_508 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, 2), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_508 : Fin 7 → Finset Cell := ![(placed21 1 (0, 2) required_12), (placed21 1 (0, 2) required_13), (placed21 1 (0, 2) required_14), required_297, required_298, (placed21 4 (1, 5) required_474), (placed21 0 (1, 0) required_507)]
def childrenD_508 : Fin 7 → Finset Cell := ![(placed21 1 (0, 2) envelope_12), (placed21 1 (0, 2) envelope_13), (placed21 1 (0, 2) envelope_14), envelope_297, envelope_298, (placed21 4 (1, 5) envelope_474), (placed21 0 (1, 0) envelope_507)]
theorem common_sub_508 : commonEnvelope childrenD_508 ⊆ insert (4, 3) required_508 := by decide +kernel
theorem child_required_sub_508 : ∀ j, childrenC_508 j ⊆ insert (4, 3) required_508 := by decide +kernel
theorem child_envelope_sub_508 : ∀ j, childrenD_508 j ⊆ envelope_508 := by decide +kernel
theorem pivot_mem_508 : (4, 3) ∈ envelope_508 := by decide +kernel
theorem children_work_508 : ∀ j, Template HasSnaky 9 (childrenC_508 j) (childrenD_508 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_13 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_14 1 (0, 2)).mono (by decide +kernel)
  · exact row_works_297.mono (by decide +kernel)
  · exact row_works_298.mono (by decide +kernel)
  · exact (placed21_template row_works_474 4 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_507 0 (1, 0)).mono (by decide +kernel)
theorem row_works_508 : Template HasSnaky 10 required_508 envelope_508 := by
  refine compose HasSnaky 9 childrenC_508 childrenD_508 children_work_508 (4, 3)
    required_508 envelope_508 pivot_mem_508 child_required_sub_508 child_envelope_sub_508 ?_
  intro b hb
  exact common_sub_508 (mem_commonEnvelope childrenD_508 b hb)
def required_509 : Finset Cell := ⟨(([(2, 2), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_509 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 2), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_509 : Fin 5 → Finset Cell := ![(placed21 3 (0, 4) required_12), (placed21 1 (0, 2) required_127), (placed21 1 (0, 2) required_128), (placed21 0 (1, 1) required_474), (placed21 0 (1, 0) required_507)]
def childrenD_509 : Fin 5 → Finset Cell := ![(placed21 3 (0, 4) envelope_12), (placed21 1 (0, 2) envelope_127), (placed21 1 (0, 2) envelope_128), (placed21 0 (1, 1) envelope_474), (placed21 0 (1, 0) envelope_507)]
theorem common_sub_509 : commonEnvelope childrenD_509 ⊆ insert (4, 3) required_509 := by decide +kernel
theorem child_required_sub_509 : ∀ j, childrenC_509 j ⊆ insert (4, 3) required_509 := by decide +kernel
theorem child_envelope_sub_509 : ∀ j, childrenD_509 j ⊆ envelope_509 := by decide +kernel
theorem pivot_mem_509 : (4, 3) ∈ envelope_509 := by decide +kernel
theorem children_work_509 : ∀ j, Template HasSnaky 9 (childrenC_509 j) (childrenD_509 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 3 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_127 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_128 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_474 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_507 0 (1, 0)).mono (by decide +kernel)
theorem row_works_509 : Template HasSnaky 10 required_509 envelope_509 := by
  refine compose HasSnaky 9 childrenC_509 childrenD_509 children_work_509 (4, 3)
    required_509 envelope_509 pivot_mem_509 child_required_sub_509 child_envelope_sub_509 ?_
  intro b hb
  exact common_sub_509 (mem_commonEnvelope childrenD_509 b hb)
def required_520 : Finset Cell := ⟨(([(3, 5), (3, 6), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_520 : Finset Cell := ⟨(([(0, 4), (0, 7), (1, 4), (1, 7), (2, 1), (2, 2), (2, 3), (2, 4), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 7), (4, 8), (4, 9), (4, 10), (5, 5), (5, 8), (6, 4), (6, 5), (6, 6), (6, 8), (7, 4), (7, 5), (7, 6), (8, 4), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_520 : Fin 3 → Finset Cell := ![(placed21 3 (2, 6) required_10), (placed21 6 (6, 9) required_317), (placed21 2 (6, 2) required_519)]
def childrenD_520 : Fin 3 → Finset Cell := ![(placed21 3 (2, 6) envelope_10), (placed21 6 (6, 9) envelope_317), (placed21 2 (6, 2) envelope_519)]
theorem common_sub_520 : commonEnvelope childrenD_520 ⊆ insert (4, 5) required_520 := by decide +kernel
theorem child_required_sub_520 : ∀ j, childrenC_520 j ⊆ insert (4, 5) required_520 := by decide +kernel
theorem child_envelope_sub_520 : ∀ j, childrenD_520 j ⊆ envelope_520 := by decide +kernel
theorem pivot_mem_520 : (4, 5) ∈ envelope_520 := by decide +kernel
theorem children_work_520 : ∀ j, Template HasSnaky 9 (childrenC_520 j) (childrenD_520 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 3 (2, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_317 6 (6, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_519 2 (6, 2)).mono (by decide +kernel)
theorem row_works_520 : Template HasSnaky 10 required_520 envelope_520 := by
  refine compose HasSnaky 9 childrenC_520 childrenD_520 children_work_520 (4, 5)
    required_520 envelope_520 pivot_mem_520 child_required_sub_520 child_envelope_sub_520 ?_
  intro b hb
  exact common_sub_520 (mem_commonEnvelope childrenD_520 b hb)
def height_399 : ℕ := 10
def childrenH_399 : Fin 5 → ℕ := ![height_12, height_135, height_181, height_396, height_396]
theorem height_exact_399 : height_399 = 1 + Finset.univ.sup childrenH_399 := by decide +kernel
theorem required_origin_399 : ∀ x ∈ required_399,
    (∃ j, x ∈ childrenC_399 j) ∨ ∀ j, x ∈ childrenD_399 j := by decide +kernel
theorem required_exact_399 : required_399 =
    ((Finset.univ.biUnion childrenC_399) ∪ commonEnvelope childrenD_399).erase (2, 5) := by
  exact required_eq_combination childrenC_399 childrenD_399 (2, 5) required_399
    (by decide +kernel) child_required_sub_399 common_sub_399 required_origin_399
theorem envelope_origin_399 : ∀ x ∈ envelope_399,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_399 j := by decide +kernel
theorem envelope_exact_399 : envelope_399 =
    insert (2, 5) (Finset.univ.biUnion childrenD_399) := by
  exact envelope_eq_combination childrenD_399 (2, 5) envelope_399
    pivot_mem_399 child_envelope_sub_399 envelope_origin_399
def checked_399 : CheckedCard where
  required := required_399
  envelope := envelope_399
  height := height_399
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_399
def height_401 : ℕ := 10
def childrenH_401 : Fin 2 → ℕ := ![height_3, height_397]
theorem height_exact_401 : height_401 = 1 + Finset.univ.sup childrenH_401 := by decide +kernel
theorem required_origin_401 : ∀ x ∈ required_401,
    (∃ j, x ∈ childrenC_401 j) ∨ ∀ j, x ∈ childrenD_401 j := by decide +kernel
theorem required_exact_401 : required_401 =
    ((Finset.univ.biUnion childrenC_401) ∪ commonEnvelope childrenD_401).erase (2, 4) := by
  exact required_eq_combination childrenC_401 childrenD_401 (2, 4) required_401
    (by decide +kernel) child_required_sub_401 common_sub_401 required_origin_401
theorem envelope_origin_401 : ∀ x ∈ envelope_401,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_401 j := by decide +kernel
theorem envelope_exact_401 : envelope_401 =
    insert (2, 4) (Finset.univ.biUnion childrenD_401) := by
  exact envelope_eq_combination childrenD_401 (2, 4) envelope_401
    pivot_mem_401 child_envelope_sub_401 envelope_origin_401
def checked_401 : CheckedCard where
  required := required_401
  envelope := envelope_401
  height := height_401
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_401
def height_408 : ℕ := 10
def childrenH_408 : Fin 3 → ℕ := ![height_44, height_127, height_407]
theorem height_exact_408 : height_408 = 1 + Finset.univ.sup childrenH_408 := by decide +kernel
theorem required_origin_408 : ∀ x ∈ required_408,
    (∃ j, x ∈ childrenC_408 j) ∨ ∀ j, x ∈ childrenD_408 j := by decide +kernel
theorem required_exact_408 : required_408 =
    ((Finset.univ.biUnion childrenC_408) ∪ commonEnvelope childrenD_408).erase (1, 5) := by
  exact required_eq_combination childrenC_408 childrenD_408 (1, 5) required_408
    (by decide +kernel) child_required_sub_408 common_sub_408 required_origin_408
theorem envelope_origin_408 : ∀ x ∈ envelope_408,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_408 j := by decide +kernel
theorem envelope_exact_408 : envelope_408 =
    insert (1, 5) (Finset.univ.biUnion childrenD_408) := by
  exact envelope_eq_combination childrenD_408 (1, 5) envelope_408
    pivot_mem_408 child_envelope_sub_408 envelope_origin_408
def checked_408 : CheckedCard where
  required := required_408
  envelope := envelope_408
  height := height_408
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_408
def height_409 : ℕ := 10
def childrenH_409 : Fin 3 → ℕ := ![height_44, height_127, height_407]
theorem height_exact_409 : height_409 = 1 + Finset.univ.sup childrenH_409 := by decide +kernel
theorem required_origin_409 : ∀ x ∈ required_409,
    (∃ j, x ∈ childrenC_409 j) ∨ ∀ j, x ∈ childrenD_409 j := by decide +kernel
theorem required_exact_409 : required_409 =
    ((Finset.univ.biUnion childrenC_409) ∪ commonEnvelope childrenD_409).erase (1, 4) := by
  exact required_eq_combination childrenC_409 childrenD_409 (1, 4) required_409
    (by decide +kernel) child_required_sub_409 common_sub_409 required_origin_409
theorem envelope_origin_409 : ∀ x ∈ envelope_409,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_409 j := by decide +kernel
theorem envelope_exact_409 : envelope_409 =
    insert (1, 4) (Finset.univ.biUnion childrenD_409) := by
  exact envelope_eq_combination childrenD_409 (1, 4) envelope_409
    pivot_mem_409 child_envelope_sub_409 envelope_origin_409
def checked_409 : CheckedCard where
  required := required_409
  envelope := envelope_409
  height := height_409
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_409
def height_410 : ℕ := 10
def childrenH_410 : Fin 4 → ℕ := ![height_10, height_12, height_12, height_407]
theorem height_exact_410 : height_410 = 1 + Finset.univ.sup childrenH_410 := by decide +kernel
theorem required_origin_410 : ∀ x ∈ required_410,
    (∃ j, x ∈ childrenC_410 j) ∨ ∀ j, x ∈ childrenD_410 j := by decide +kernel
theorem required_exact_410 : required_410 =
    ((Finset.univ.biUnion childrenC_410) ∪ commonEnvelope childrenD_410).erase (1, 5) := by
  exact required_eq_combination childrenC_410 childrenD_410 (1, 5) required_410
    (by decide +kernel) child_required_sub_410 common_sub_410 required_origin_410
theorem envelope_origin_410 : ∀ x ∈ envelope_410,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_410 j := by decide +kernel
theorem envelope_exact_410 : envelope_410 =
    insert (1, 5) (Finset.univ.biUnion childrenD_410) := by
  exact envelope_eq_combination childrenD_410 (1, 5) envelope_410
    pivot_mem_410 child_envelope_sub_410 envelope_origin_410
def checked_410 : CheckedCard where
  required := required_410
  envelope := envelope_410
  height := height_410
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_410
def height_411 : ℕ := 10
def childrenH_411 : Fin 3 → ℕ := ![height_15, height_65, height_407]
theorem height_exact_411 : height_411 = 1 + Finset.univ.sup childrenH_411 := by decide +kernel
theorem required_origin_411 : ∀ x ∈ required_411,
    (∃ j, x ∈ childrenC_411 j) ∨ ∀ j, x ∈ childrenD_411 j := by decide +kernel
theorem required_exact_411 : required_411 =
    ((Finset.univ.biUnion childrenC_411) ∪ commonEnvelope childrenD_411).erase (1, 5) := by
  exact required_eq_combination childrenC_411 childrenD_411 (1, 5) required_411
    (by decide +kernel) child_required_sub_411 common_sub_411 required_origin_411
theorem envelope_origin_411 : ∀ x ∈ envelope_411,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_411 j := by decide +kernel
theorem envelope_exact_411 : envelope_411 =
    insert (1, 5) (Finset.univ.biUnion childrenD_411) := by
  exact envelope_eq_combination childrenD_411 (1, 5) envelope_411
    pivot_mem_411 child_envelope_sub_411 envelope_origin_411
def checked_411 : CheckedCard where
  required := required_411
  envelope := envelope_411
  height := height_411
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_411
def height_444 : ℕ := 10
def childrenH_444 : Fin 4 → ℕ := ![height_7, height_8, height_9, height_443]
theorem height_exact_444 : height_444 = 1 + Finset.univ.sup childrenH_444 := by decide +kernel
theorem required_origin_444 : ∀ x ∈ required_444,
    (∃ j, x ∈ childrenC_444 j) ∨ ∀ j, x ∈ childrenD_444 j := by decide +kernel
theorem required_exact_444 : required_444 =
    ((Finset.univ.biUnion childrenC_444) ∪ commonEnvelope childrenD_444).erase (1, 4) := by
  exact required_eq_combination childrenC_444 childrenD_444 (1, 4) required_444
    (by decide +kernel) child_required_sub_444 common_sub_444 required_origin_444
theorem envelope_origin_444 : ∀ x ∈ envelope_444,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_444 j := by decide +kernel
theorem envelope_exact_444 : envelope_444 =
    insert (1, 4) (Finset.univ.biUnion childrenD_444) := by
  exact envelope_eq_combination childrenD_444 (1, 4) envelope_444
    pivot_mem_444 child_envelope_sub_444 envelope_origin_444
def checked_444 : CheckedCard where
  required := required_444
  envelope := envelope_444
  height := height_444
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_444
def height_459 : ℕ := 10
def childrenH_459 : Fin 8 → ℕ := ![height_12, height_13, height_33, height_189, height_192, height_369, height_457, height_458]
theorem height_exact_459 : height_459 = 1 + Finset.univ.sup childrenH_459 := by decide +kernel
theorem required_origin_459 : ∀ x ∈ required_459,
    (∃ j, x ∈ childrenC_459 j) ∨ ∀ j, x ∈ childrenD_459 j := by decide +kernel
theorem required_exact_459 : required_459 =
    ((Finset.univ.biUnion childrenC_459) ∪ commonEnvelope childrenD_459).erase (1, 6) := by
  exact required_eq_combination childrenC_459 childrenD_459 (1, 6) required_459
    (by decide +kernel) child_required_sub_459 common_sub_459 required_origin_459
theorem envelope_origin_459 : ∀ x ∈ envelope_459,
    x = (1, 6) ∨ ∃ j, x ∈ childrenD_459 j := by decide +kernel
theorem envelope_exact_459 : envelope_459 =
    insert (1, 6) (Finset.univ.biUnion childrenD_459) := by
  exact envelope_eq_combination childrenD_459 (1, 6) envelope_459
    pivot_mem_459 child_envelope_sub_459 envelope_origin_459
def checked_459 : CheckedCard where
  required := required_459
  envelope := envelope_459
  height := height_459
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_459
def height_460 : ℕ := 10
def childrenH_460 : Fin 5 → ℕ := ![height_13, height_14, height_33, height_457, height_458]
theorem height_exact_460 : height_460 = 1 + Finset.univ.sup childrenH_460 := by decide +kernel
theorem required_origin_460 : ∀ x ∈ required_460,
    (∃ j, x ∈ childrenC_460 j) ∨ ∀ j, x ∈ childrenD_460 j := by decide +kernel
theorem required_exact_460 : required_460 =
    ((Finset.univ.biUnion childrenC_460) ∪ commonEnvelope childrenD_460).erase (1, 4) := by
  exact required_eq_combination childrenC_460 childrenD_460 (1, 4) required_460
    (by decide +kernel) child_required_sub_460 common_sub_460 required_origin_460
theorem envelope_origin_460 : ∀ x ∈ envelope_460,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_460 j := by decide +kernel
theorem envelope_exact_460 : envelope_460 =
    insert (1, 4) (Finset.univ.biUnion childrenD_460) := by
  exact envelope_eq_combination childrenD_460 (1, 4) envelope_460
    pivot_mem_460 child_envelope_sub_460 envelope_origin_460
def checked_460 : CheckedCard where
  required := required_460
  envelope := envelope_460
  height := height_460
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_460
def height_461 : ℕ := 10
def childrenH_461 : Fin 4 → ℕ := ![height_28, height_100, height_429, height_457]
theorem height_exact_461 : height_461 = 1 + Finset.univ.sup childrenH_461 := by decide +kernel
theorem required_origin_461 : ∀ x ∈ required_461,
    (∃ j, x ∈ childrenC_461 j) ∨ ∀ j, x ∈ childrenD_461 j := by decide +kernel
theorem required_exact_461 : required_461 =
    ((Finset.univ.biUnion childrenC_461) ∪ commonEnvelope childrenD_461).erase (3, 3) := by
  exact required_eq_combination childrenC_461 childrenD_461 (3, 3) required_461
    (by decide +kernel) child_required_sub_461 common_sub_461 required_origin_461
theorem envelope_origin_461 : ∀ x ∈ envelope_461,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_461 j := by decide +kernel
theorem envelope_exact_461 : envelope_461 =
    insert (3, 3) (Finset.univ.biUnion childrenD_461) := by
  exact envelope_eq_combination childrenD_461 (3, 3) envelope_461
    pivot_mem_461 child_envelope_sub_461 envelope_origin_461
def checked_461 : CheckedCard where
  required := required_461
  envelope := envelope_461
  height := height_461
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_461
def height_475 : ℕ := 10
def childrenH_475 : Fin 5 → ℕ := ![height_13, height_14, height_31, height_396, height_474]
theorem height_exact_475 : height_475 = 1 + Finset.univ.sup childrenH_475 := by decide +kernel
theorem required_origin_475 : ∀ x ∈ required_475,
    (∃ j, x ∈ childrenC_475 j) ∨ ∀ j, x ∈ childrenD_475 j := by decide +kernel
theorem required_exact_475 : required_475 =
    ((Finset.univ.biUnion childrenC_475) ∪ commonEnvelope childrenD_475).erase (2, 5) := by
  exact required_eq_combination childrenC_475 childrenD_475 (2, 5) required_475
    (by decide +kernel) child_required_sub_475 common_sub_475 required_origin_475
theorem envelope_origin_475 : ∀ x ∈ envelope_475,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_475 j := by decide +kernel
theorem envelope_exact_475 : envelope_475 =
    insert (2, 5) (Finset.univ.biUnion childrenD_475) := by
  exact envelope_eq_combination childrenD_475 (2, 5) envelope_475
    pivot_mem_475 child_envelope_sub_475 envelope_origin_475
def checked_475 : CheckedCard where
  required := required_475
  envelope := envelope_475
  height := height_475
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_475
def height_476 : ℕ := 10
def childrenH_476 : Fin 5 → ℕ := ![height_12, height_12, height_12, height_264, height_474]
theorem height_exact_476 : height_476 = 1 + Finset.univ.sup childrenH_476 := by decide +kernel
theorem required_origin_476 : ∀ x ∈ required_476,
    (∃ j, x ∈ childrenC_476 j) ∨ ∀ j, x ∈ childrenD_476 j := by decide +kernel
theorem required_exact_476 : required_476 =
    ((Finset.univ.biUnion childrenC_476) ∪ commonEnvelope childrenD_476).erase (3, 5) := by
  exact required_eq_combination childrenC_476 childrenD_476 (3, 5) required_476
    (by decide +kernel) child_required_sub_476 common_sub_476 required_origin_476
theorem envelope_origin_476 : ∀ x ∈ envelope_476,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_476 j := by decide +kernel
theorem envelope_exact_476 : envelope_476 =
    insert (3, 5) (Finset.univ.biUnion childrenD_476) := by
  exact envelope_eq_combination childrenD_476 (3, 5) envelope_476
    pivot_mem_476 child_envelope_sub_476 envelope_origin_476
def checked_476 : CheckedCard where
  required := required_476
  envelope := envelope_476
  height := height_476
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_476
def height_479_i0 : ℕ := 6
def childrenH_479_i0 : Fin 2 → ℕ := ![height_8, height_386]
theorem height_exact_479_i0 : height_479_i0 = 1 + Finset.univ.sup childrenH_479_i0 := by decide +kernel
theorem required_origin_479_i0 : ∀ x ∈ required_479_i0,
    (∃ j, x ∈ childrenC_479_i0 j) ∨ ∀ j, x ∈ childrenD_479_i0 j := by decide +kernel
theorem required_exact_479_i0 : required_479_i0 =
    ((Finset.univ.biUnion childrenC_479_i0) ∪ commonEnvelope childrenD_479_i0).erase (3, 2) := by
  exact required_eq_combination childrenC_479_i0 childrenD_479_i0 (3, 2) required_479_i0
    (by decide +kernel) child_required_sub_479_i0 common_sub_479_i0 required_origin_479_i0
theorem envelope_origin_479_i0 : ∀ x ∈ envelope_479_i0,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_479_i0 j := by decide +kernel
theorem envelope_exact_479_i0 : envelope_479_i0 =
    insert (3, 2) (Finset.univ.biUnion childrenD_479_i0) := by
  exact envelope_eq_combination childrenD_479_i0 (3, 2) envelope_479_i0
    pivot_mem_479_i0 child_envelope_sub_479_i0 envelope_origin_479_i0
def checked_479_i0 : CheckedCard where
  required := required_479_i0
  envelope := envelope_479_i0
  height := height_479_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_479_i0
def height_479 : ℕ := 10
def childrenH_479 : Fin 7 → ℕ := ![height_14, height_31, height_181, height_367, height_479_i0, height_435, height_474]
theorem height_exact_479 : height_479 = 1 + Finset.univ.sup childrenH_479 := by decide +kernel
theorem required_origin_479 : ∀ x ∈ required_479,
    (∃ j, x ∈ childrenC_479 j) ∨ ∀ j, x ∈ childrenD_479 j := by decide +kernel
theorem required_exact_479 : required_479 =
    ((Finset.univ.biUnion childrenC_479) ∪ commonEnvelope childrenD_479).erase (3, 5) := by
  exact required_eq_combination childrenC_479 childrenD_479 (3, 5) required_479
    (by decide +kernel) child_required_sub_479 common_sub_479 required_origin_479
theorem envelope_origin_479 : ∀ x ∈ envelope_479,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_479 j := by decide +kernel
theorem envelope_exact_479 : envelope_479 =
    insert (3, 5) (Finset.univ.biUnion childrenD_479) := by
  exact envelope_eq_combination childrenD_479 (3, 5) envelope_479
    pivot_mem_479 child_envelope_sub_479 envelope_origin_479
def checked_479 : CheckedCard where
  required := required_479
  envelope := envelope_479
  height := height_479
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_479
def height_480 : ℕ := 10
def childrenH_480 : Fin 7 → ℕ := ![height_13, height_14, height_192, height_298, height_435, height_474, height_477]
theorem height_exact_480 : height_480 = 1 + Finset.univ.sup childrenH_480 := by decide +kernel
theorem required_origin_480 : ∀ x ∈ required_480,
    (∃ j, x ∈ childrenC_480 j) ∨ ∀ j, x ∈ childrenD_480 j := by decide +kernel
theorem required_exact_480 : required_480 =
    ((Finset.univ.biUnion childrenC_480) ∪ commonEnvelope childrenD_480).erase (3, 3) := by
  exact required_eq_combination childrenC_480 childrenD_480 (3, 3) required_480
    (by decide +kernel) child_required_sub_480 common_sub_480 required_origin_480
theorem envelope_origin_480 : ∀ x ∈ envelope_480,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_480 j := by decide +kernel
theorem envelope_exact_480 : envelope_480 =
    insert (3, 3) (Finset.univ.biUnion childrenD_480) := by
  exact envelope_eq_combination childrenD_480 (3, 3) envelope_480
    pivot_mem_480 child_envelope_sub_480 envelope_origin_480
def checked_480 : CheckedCard where
  required := required_480
  envelope := envelope_480
  height := height_480
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_480
def height_481 : ℕ := 10
def childrenH_481 : Fin 5 → ℕ := ![height_13, height_14, height_33, height_457, height_477]
theorem height_exact_481 : height_481 = 1 + Finset.univ.sup childrenH_481 := by decide +kernel
theorem required_origin_481 : ∀ x ∈ required_481,
    (∃ j, x ∈ childrenC_481 j) ∨ ∀ j, x ∈ childrenD_481 j := by decide +kernel
theorem required_exact_481 : required_481 =
    ((Finset.univ.biUnion childrenC_481) ∪ commonEnvelope childrenD_481).erase (2, 4) := by
  exact required_eq_combination childrenC_481 childrenD_481 (2, 4) required_481
    (by decide +kernel) child_required_sub_481 common_sub_481 required_origin_481
theorem envelope_origin_481 : ∀ x ∈ envelope_481,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_481 j := by decide +kernel
theorem envelope_exact_481 : envelope_481 =
    insert (2, 4) (Finset.univ.biUnion childrenD_481) := by
  exact envelope_eq_combination childrenD_481 (2, 4) envelope_481
    pivot_mem_481 child_envelope_sub_481 envelope_origin_481
def checked_481 : CheckedCard where
  required := required_481
  envelope := envelope_481
  height := height_481
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_481
def height_483 : ℕ := 10
def childrenH_483 : Fin 5 → ℕ := ![height_13, height_14, height_33, height_458, height_474]
theorem height_exact_483 : height_483 = 1 + Finset.univ.sup childrenH_483 := by decide +kernel
theorem required_origin_483 : ∀ x ∈ required_483,
    (∃ j, x ∈ childrenC_483 j) ∨ ∀ j, x ∈ childrenD_483 j := by decide +kernel
theorem required_exact_483 : required_483 =
    ((Finset.univ.biUnion childrenC_483) ∪ commonEnvelope childrenD_483).erase (2, 5) := by
  exact required_eq_combination childrenC_483 childrenD_483 (2, 5) required_483
    (by decide +kernel) child_required_sub_483 common_sub_483 required_origin_483
theorem envelope_origin_483 : ∀ x ∈ envelope_483,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_483 j := by decide +kernel
theorem envelope_exact_483 : envelope_483 =
    insert (2, 5) (Finset.univ.biUnion childrenD_483) := by
  exact envelope_eq_combination childrenD_483 (2, 5) envelope_483
    pivot_mem_483 child_envelope_sub_483 envelope_origin_483
def checked_483 : CheckedCard where
  required := required_483
  envelope := envelope_483
  height := height_483
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_483
def height_491_i0 : ℕ := 5
def childrenH_491_i0 : Fin 4 → ℕ := ![height_60, height_60, height_83, height_106]
theorem height_exact_491_i0 : height_491_i0 = 1 + Finset.univ.sup childrenH_491_i0 := by decide +kernel
theorem required_origin_491_i0 : ∀ x ∈ required_491_i0,
    (∃ j, x ∈ childrenC_491_i0 j) ∨ ∀ j, x ∈ childrenD_491_i0 j := by decide +kernel
theorem required_exact_491_i0 : required_491_i0 =
    ((Finset.univ.biUnion childrenC_491_i0) ∪ commonEnvelope childrenD_491_i0).erase (5, 3) := by
  exact required_eq_combination childrenC_491_i0 childrenD_491_i0 (5, 3) required_491_i0
    (by decide +kernel) child_required_sub_491_i0 common_sub_491_i0 required_origin_491_i0
theorem envelope_origin_491_i0 : ∀ x ∈ envelope_491_i0,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_491_i0 j := by decide +kernel
theorem envelope_exact_491_i0 : envelope_491_i0 =
    insert (5, 3) (Finset.univ.biUnion childrenD_491_i0) := by
  exact envelope_eq_combination childrenD_491_i0 (5, 3) envelope_491_i0
    pivot_mem_491_i0 child_envelope_sub_491_i0 envelope_origin_491_i0
def checked_491_i0 : CheckedCard where
  required := required_491_i0
  envelope := envelope_491_i0
  height := height_491_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_491_i0
def height_491_i1 : ℕ := 9
def childrenH_491_i1 : Fin 3 → ℕ := ![height_60, height_70, height_345]
theorem height_exact_491_i1 : height_491_i1 = 1 + Finset.univ.sup childrenH_491_i1 := by decide +kernel
theorem required_origin_491_i1 : ∀ x ∈ required_491_i1,
    (∃ j, x ∈ childrenC_491_i1 j) ∨ ∀ j, x ∈ childrenD_491_i1 j := by decide +kernel
theorem required_exact_491_i1 : required_491_i1 =
    ((Finset.univ.biUnion childrenC_491_i1) ∪ commonEnvelope childrenD_491_i1).erase (5, 3) := by
  exact required_eq_combination childrenC_491_i1 childrenD_491_i1 (5, 3) required_491_i1
    (by decide +kernel) child_required_sub_491_i1 common_sub_491_i1 required_origin_491_i1
theorem envelope_origin_491_i1 : ∀ x ∈ envelope_491_i1,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_491_i1 j := by decide +kernel
theorem envelope_exact_491_i1 : envelope_491_i1 =
    insert (5, 3) (Finset.univ.biUnion childrenD_491_i1) := by
  exact envelope_eq_combination childrenD_491_i1 (5, 3) envelope_491_i1
    pivot_mem_491_i1 child_envelope_sub_491_i1 envelope_origin_491_i1
def checked_491_i1 : CheckedCard where
  required := required_491_i1
  envelope := envelope_491_i1
  height := height_491_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_491_i1
def height_491 : ℕ := 10
def childrenH_491 : Fin 4 → ℕ := ![height_44, height_270, height_491_i0, height_491_i1]
theorem height_exact_491 : height_491 = 1 + Finset.univ.sup childrenH_491 := by decide +kernel
theorem required_origin_491 : ∀ x ∈ required_491,
    (∃ j, x ∈ childrenC_491 j) ∨ ∀ j, x ∈ childrenD_491 j := by decide +kernel
theorem required_exact_491 : required_491 =
    ((Finset.univ.biUnion childrenC_491) ∪ commonEnvelope childrenD_491).erase (3, 3) := by
  exact required_eq_combination childrenC_491 childrenD_491 (3, 3) required_491
    (by decide +kernel) child_required_sub_491 common_sub_491 required_origin_491
theorem envelope_origin_491 : ∀ x ∈ envelope_491,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_491 j := by decide +kernel
theorem envelope_exact_491 : envelope_491 =
    insert (3, 3) (Finset.univ.biUnion childrenD_491) := by
  exact envelope_eq_combination childrenD_491 (3, 3) envelope_491
    pivot_mem_491 child_envelope_sub_491 envelope_origin_491
def checked_491 : CheckedCard where
  required := required_491
  envelope := envelope_491
  height := height_491
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_491
def height_508 : ℕ := 10
def childrenH_508 : Fin 7 → ℕ := ![height_12, height_13, height_14, height_297, height_298, height_474, height_507]
theorem height_exact_508 : height_508 = 1 + Finset.univ.sup childrenH_508 := by decide +kernel
theorem required_origin_508 : ∀ x ∈ required_508,
    (∃ j, x ∈ childrenC_508 j) ∨ ∀ j, x ∈ childrenD_508 j := by decide +kernel
theorem required_exact_508 : required_508 =
    ((Finset.univ.biUnion childrenC_508) ∪ commonEnvelope childrenD_508).erase (4, 3) := by
  exact required_eq_combination childrenC_508 childrenD_508 (4, 3) required_508
    (by decide +kernel) child_required_sub_508 common_sub_508 required_origin_508
theorem envelope_origin_508 : ∀ x ∈ envelope_508,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_508 j := by decide +kernel
theorem envelope_exact_508 : envelope_508 =
    insert (4, 3) (Finset.univ.biUnion childrenD_508) := by
  exact envelope_eq_combination childrenD_508 (4, 3) envelope_508
    pivot_mem_508 child_envelope_sub_508 envelope_origin_508
def checked_508 : CheckedCard where
  required := required_508
  envelope := envelope_508
  height := height_508
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_508
def height_509 : ℕ := 10
def childrenH_509 : Fin 5 → ℕ := ![height_12, height_127, height_128, height_474, height_507]
theorem height_exact_509 : height_509 = 1 + Finset.univ.sup childrenH_509 := by decide +kernel
theorem required_origin_509 : ∀ x ∈ required_509,
    (∃ j, x ∈ childrenC_509 j) ∨ ∀ j, x ∈ childrenD_509 j := by decide +kernel
theorem required_exact_509 : required_509 =
    ((Finset.univ.biUnion childrenC_509) ∪ commonEnvelope childrenD_509).erase (4, 3) := by
  exact required_eq_combination childrenC_509 childrenD_509 (4, 3) required_509
    (by decide +kernel) child_required_sub_509 common_sub_509 required_origin_509
theorem envelope_origin_509 : ∀ x ∈ envelope_509,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_509 j := by decide +kernel
theorem envelope_exact_509 : envelope_509 =
    insert (4, 3) (Finset.univ.biUnion childrenD_509) := by
  exact envelope_eq_combination childrenD_509 (4, 3) envelope_509
    pivot_mem_509 child_envelope_sub_509 envelope_origin_509
def checked_509 : CheckedCard where
  required := required_509
  envelope := envelope_509
  height := height_509
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_509
def height_520 : ℕ := 10
def childrenH_520 : Fin 3 → ℕ := ![height_10, height_317, height_519]
theorem height_exact_520 : height_520 = 1 + Finset.univ.sup childrenH_520 := by decide +kernel
theorem required_origin_520 : ∀ x ∈ required_520,
    (∃ j, x ∈ childrenC_520 j) ∨ ∀ j, x ∈ childrenD_520 j := by decide +kernel
theorem required_exact_520 : required_520 =
    ((Finset.univ.biUnion childrenC_520) ∪ commonEnvelope childrenD_520).erase (4, 5) := by
  exact required_eq_combination childrenC_520 childrenD_520 (4, 5) required_520
    (by decide +kernel) child_required_sub_520 common_sub_520 required_origin_520
theorem envelope_origin_520 : ∀ x ∈ envelope_520,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_520 j := by decide +kernel
theorem envelope_exact_520 : envelope_520 =
    insert (4, 5) (Finset.univ.biUnion childrenD_520) := by
  exact envelope_eq_combination childrenD_520 (4, 5) envelope_520
    pivot_mem_520 child_envelope_sub_520 envelope_origin_520
def checked_520 : CheckedCard where
  required := required_520
  envelope := envelope_520
  height := height_520
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_520
end SnakyPrototype.Certificate21

end OAI
