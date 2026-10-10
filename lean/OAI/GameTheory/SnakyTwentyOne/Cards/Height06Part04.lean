import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part05
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_378_i0 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 0), (2, 2), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_378_i0 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_378_i0 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) required_5), (placed21 0 (2, 0) required_18)]
def childrenD_378_i0 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) envelope_5), (placed21 0 (2, 0) envelope_18)]
theorem common_sub_378_i0 : commonEnvelope childrenD_378_i0 ⊆ insert (3, 3) required_378_i0 := by decide +kernel
theorem child_required_sub_378_i0 : ∀ j, childrenC_378_i0 j ⊆ insert (3, 3) required_378_i0 := by decide +kernel
theorem child_envelope_sub_378_i0 : ∀ j, childrenD_378_i0 j ⊆ envelope_378_i0 := by decide +kernel
theorem pivot_mem_378_i0 : (3, 3) ∈ envelope_378_i0 := by decide +kernel
theorem children_work_378_i0 : ∀ j, Template HasSnaky 4 (childrenC_378_i0 j) (childrenD_378_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_18 0 (2, 0)).mono (by decide +kernel)
theorem row_works_378_i0 : Template HasSnaky 5 required_378_i0 envelope_378_i0 := by
  refine compose HasSnaky 4 childrenC_378_i0 childrenD_378_i0 children_work_378_i0 (3, 3)
    required_378_i0 envelope_378_i0 pivot_mem_378_i0 child_required_sub_378_i0 child_envelope_sub_378_i0 ?_
  intro b hb
  exact common_sub_378_i0 (mem_commonEnvelope childrenD_378_i0 b hb)
def required_378 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 0), (2, 2), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_378 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_378 : Fin 2 → Finset Cell := ![(placed21 4 (0, 2) required_5), required_378_i0]
def childrenD_378 : Fin 2 → Finset Cell := ![(placed21 4 (0, 2) envelope_5), envelope_378_i0]
theorem common_sub_378 : commonEnvelope childrenD_378 ⊆ insert (3, 1) required_378 := by decide +kernel
theorem child_required_sub_378 : ∀ j, childrenC_378 j ⊆ insert (3, 1) required_378 := by decide +kernel
theorem child_envelope_sub_378 : ∀ j, childrenD_378 j ⊆ envelope_378 := by decide +kernel
theorem pivot_mem_378 : (3, 1) ∈ envelope_378 := by decide +kernel
theorem children_work_378 : ∀ j, Template HasSnaky 5 (childrenC_378 j) (childrenD_378 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 2)).mono (by decide +kernel)
  · exact row_works_378_i0.mono (by decide +kernel)
theorem row_works_378 : Template HasSnaky 6 required_378 envelope_378 := by
  refine compose HasSnaky 5 childrenC_378 childrenD_378 children_work_378 (3, 1)
    required_378 envelope_378 pivot_mem_378 child_required_sub_378 child_envelope_sub_378 ?_
  intro b hb
  exact common_sub_378 (mem_commonEnvelope childrenD_378 b hb)
def required_384 : Finset Cell := ⟨(([(0, 2), (3, 1), (3, 2), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_384 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (2, 0), (2, 1), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_384 : Fin 2 → Finset Cell := ![(placed21 1 (2, 1) required_8), (placed21 7 (5, 4) required_383)]
def childrenD_384 : Fin 2 → Finset Cell := ![(placed21 1 (2, 1) envelope_8), (placed21 7 (5, 4) envelope_383)]
theorem common_sub_384 : commonEnvelope childrenD_384 ⊆ insert (3, 3) required_384 := by decide +kernel
theorem child_required_sub_384 : ∀ j, childrenC_384 j ⊆ insert (3, 3) required_384 := by decide +kernel
theorem child_envelope_sub_384 : ∀ j, childrenD_384 j ⊆ envelope_384 := by decide +kernel
theorem pivot_mem_384 : (3, 3) ∈ envelope_384 := by decide +kernel
theorem children_work_384 : ∀ j, Template HasSnaky 5 (childrenC_384 j) (childrenD_384 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 1 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_383 7 (5, 4)).mono (by decide +kernel)
theorem row_works_384 : Template HasSnaky 6 required_384 envelope_384 := by
  refine compose HasSnaky 5 childrenC_384 childrenD_384 children_work_384 (3, 3)
    required_384 envelope_384 pivot_mem_384 child_required_sub_384 child_envelope_sub_384 ?_
  intro b hb
  exact common_sub_384 (mem_commonEnvelope childrenD_384 b hb)
def required_387 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (2, 2), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_387 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (5, 2), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_387 : Fin 3 → Finset Cell := ![(placed21 1 (0, 1) required_200), (placed21 1 (1, 0) required_376), (placed21 1 (0, 0) required_386)]
def childrenD_387 : Fin 3 → Finset Cell := ![(placed21 1 (0, 1) envelope_200), (placed21 1 (1, 0) envelope_376), (placed21 1 (0, 0) envelope_386)]
theorem common_sub_387 : commonEnvelope childrenD_387 ⊆ insert (4, 2) required_387 := by decide +kernel
theorem child_required_sub_387 : ∀ j, childrenC_387 j ⊆ insert (4, 2) required_387 := by decide +kernel
theorem child_envelope_sub_387 : ∀ j, childrenD_387 j ⊆ envelope_387 := by decide +kernel
theorem pivot_mem_387 : (4, 2) ∈ envelope_387 := by decide +kernel
theorem children_work_387 : ∀ j, Template HasSnaky 5 (childrenC_387 j) (childrenD_387 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_200 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_376 1 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_386 1 (0, 0)).mono (by decide +kernel)
theorem row_works_387 : Template HasSnaky 6 required_387 envelope_387 := by
  refine compose HasSnaky 5 childrenC_387 childrenD_387 children_work_387 (4, 2)
    required_387 envelope_387 pivot_mem_387 child_required_sub_387 child_envelope_sub_387 ?_
  intro b hb
  exact common_sub_387 (mem_commonEnvelope childrenD_387 b hb)
def required_390 : Finset Cell := ⟨(([(0, 5), (1, 4), (1, 5), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_390 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 8), (0, 9), (0, 10), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 7), (2, 8), (2, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_390 : Fin 3 → Finset Cell := ![(placed21 2 (1, 3) required_11), (placed21 0 (0, 4) required_17), (placed21 6 (1, 7) required_389)]
def childrenD_390 : Fin 3 → Finset Cell := ![(placed21 2 (1, 3) envelope_11), (placed21 0 (0, 4) envelope_17), (placed21 6 (1, 7) envelope_389)]
theorem common_sub_390 : commonEnvelope childrenD_390 ⊆ insert (1, 7) required_390 := by decide +kernel
theorem child_required_sub_390 : ∀ j, childrenC_390 j ⊆ insert (1, 7) required_390 := by decide +kernel
theorem child_envelope_sub_390 : ∀ j, childrenD_390 j ⊆ envelope_390 := by decide +kernel
theorem pivot_mem_390 : (1, 7) ∈ envelope_390 := by decide +kernel
theorem children_work_390 : ∀ j, Template HasSnaky 5 (childrenC_390 j) (childrenD_390 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 2 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_17 0 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_389 6 (1, 7)).mono (by decide +kernel)
theorem row_works_390 : Template HasSnaky 6 required_390 envelope_390 := by
  refine compose HasSnaky 5 childrenC_390 childrenD_390 children_work_390 (1, 7)
    required_390 envelope_390 pivot_mem_390 child_required_sub_390 child_envelope_sub_390 ?_
  intro b hb
  exact common_sub_390 (mem_commonEnvelope childrenD_390 b hb)
def required_392 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_392 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (4, 1), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_392 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) required_0), required_391]
def childrenD_392 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) envelope_0), envelope_391]
theorem common_sub_392 : commonEnvelope childrenD_392 ⊆ insert (3, 3) required_392 := by decide +kernel
theorem child_required_sub_392 : ∀ j, childrenC_392 j ⊆ insert (3, 3) required_392 := by decide +kernel
theorem child_envelope_sub_392 : ∀ j, childrenD_392 j ⊆ envelope_392 := by decide +kernel
theorem pivot_mem_392 : (3, 3) ∈ envelope_392 := by decide +kernel
theorem children_work_392 : ∀ j, Template HasSnaky 5 (childrenC_392 j) (childrenD_392 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (4, 3)).mono (by decide +kernel)
  · exact row_works_391.mono (by decide +kernel)
theorem row_works_392 : Template HasSnaky 6 required_392 envelope_392 := by
  refine compose HasSnaky 5 childrenC_392 childrenD_392 children_work_392 (3, 3)
    required_392 envelope_392 pivot_mem_392 child_required_sub_392 child_envelope_sub_392 ?_
  intro b hb
  exact common_sub_392 (mem_commonEnvelope childrenD_392 b hb)
def required_393 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (2, 2), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_393 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 2), (3, 3), (3, 4), (3, 5), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_393 : Fin 3 → Finset Cell := ![(placed21 0 (1, 0) required_11), (placed21 0 (0, 1) required_20), (placed21 4 (0, 5) required_391)]
def childrenD_393 : Fin 3 → Finset Cell := ![(placed21 0 (1, 0) envelope_11), (placed21 0 (0, 1) envelope_20), (placed21 4 (0, 5) envelope_391)]
theorem common_sub_393 : commonEnvelope childrenD_393 ⊆ insert (1, 4) required_393 := by decide +kernel
theorem child_required_sub_393 : ∀ j, childrenC_393 j ⊆ insert (1, 4) required_393 := by decide +kernel
theorem child_envelope_sub_393 : ∀ j, childrenD_393 j ⊆ envelope_393 := by decide +kernel
theorem pivot_mem_393 : (1, 4) ∈ envelope_393 := by decide +kernel
theorem children_work_393 : ∀ j, Template HasSnaky 5 (childrenC_393 j) (childrenD_393 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_20 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_391 4 (0, 5)).mono (by decide +kernel)
theorem row_works_393 : Template HasSnaky 6 required_393 envelope_393 := by
  refine compose HasSnaky 5 childrenC_393 childrenD_393 children_work_393 (1, 4)
    required_393 envelope_393 pivot_mem_393 child_required_sub_393 child_envelope_sub_393 ?_
  intro b hb
  exact common_sub_393 (mem_commonEnvelope childrenD_393 b hb)
def required_403_i0 : Finset Cell := ⟨(([(1, 5), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_403_i0 : Finset Cell := ⟨(([(0, 5), (1, 5), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 5), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_403_i0 : Fin 2 → Finset Cell := ![(placed21 5 (3, 1) required_4), (placed21 5 (4, 2) required_381)]
def childrenD_403_i0 : Fin 2 → Finset Cell := ![(placed21 5 (3, 1) envelope_4), (placed21 5 (4, 2) envelope_381)]
theorem common_sub_403_i0 : commonEnvelope childrenD_403_i0 ⊆ insert (2, 5) required_403_i0 := by decide +kernel
theorem child_required_sub_403_i0 : ∀ j, childrenC_403_i0 j ⊆ insert (2, 5) required_403_i0 := by decide +kernel
theorem child_envelope_sub_403_i0 : ∀ j, childrenD_403_i0 j ⊆ envelope_403_i0 := by decide +kernel
theorem pivot_mem_403_i0 : (2, 5) ∈ envelope_403_i0 := by decide +kernel
theorem children_work_403_i0 : ∀ j, Template HasSnaky 4 (childrenC_403_i0 j) (childrenD_403_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 5 (3, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_381 5 (4, 2)).mono (by decide +kernel)
theorem row_works_403_i0 : Template HasSnaky 5 required_403_i0 envelope_403_i0 := by
  refine compose HasSnaky 4 childrenC_403_i0 childrenD_403_i0 children_work_403_i0 (2, 5)
    required_403_i0 envelope_403_i0 pivot_mem_403_i0 child_required_sub_403_i0 child_envelope_sub_403_i0 ?_
  intro b hb
  exact common_sub_403_i0 (mem_commonEnvelope childrenD_403_i0 b hb)
def required_403 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 4), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_403 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 5), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_403 : Fin 2 → Finset Cell := ![required_86, required_403_i0]
def childrenD_403 : Fin 2 → Finset Cell := ![envelope_86, envelope_403_i0]
theorem common_sub_403 : commonEnvelope childrenD_403 ⊆ insert (1, 5) required_403 := by decide +kernel
theorem child_required_sub_403 : ∀ j, childrenC_403 j ⊆ insert (1, 5) required_403 := by decide +kernel
theorem child_envelope_sub_403 : ∀ j, childrenD_403 j ⊆ envelope_403 := by decide +kernel
theorem pivot_mem_403 : (1, 5) ∈ envelope_403 := by decide +kernel
theorem children_work_403 : ∀ j, Template HasSnaky 5 (childrenC_403 j) (childrenD_403 j) := by
  intro j
  fin_cases j
  · exact row_works_86.mono (by decide +kernel)
  · exact row_works_403_i0.mono (by decide +kernel)
theorem row_works_403 : Template HasSnaky 6 required_403 envelope_403 := by
  refine compose HasSnaky 5 childrenC_403 childrenD_403 children_work_403 (1, 5)
    required_403 envelope_403 pivot_mem_403 child_required_sub_403 child_envelope_sub_403 ?_
  intro b hb
  exact common_sub_403 (mem_commonEnvelope childrenD_403 b hb)
def required_414 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (2, 1), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_414 : Finset Cell := ⟨(([(0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 4), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_414 : Fin 2 → Finset Cell := ![(placed21 3 (1, 5) required_0), required_413]
def childrenD_414 : Fin 2 → Finset Cell := ![(placed21 3 (1, 5) envelope_0), envelope_413]
theorem common_sub_414 : commonEnvelope childrenD_414 ⊆ insert (1, 4) required_414 := by decide +kernel
theorem child_required_sub_414 : ∀ j, childrenC_414 j ⊆ insert (1, 4) required_414 := by decide +kernel
theorem child_envelope_sub_414 : ∀ j, childrenD_414 j ⊆ envelope_414 := by decide +kernel
theorem pivot_mem_414 : (1, 4) ∈ envelope_414 := by decide +kernel
theorem children_work_414 : ∀ j, Template HasSnaky 5 (childrenC_414 j) (childrenD_414 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 3 (1, 5)).mono (by decide +kernel)
  · exact row_works_413.mono (by decide +kernel)
theorem row_works_414 : Template HasSnaky 6 required_414 envelope_414 := by
  refine compose HasSnaky 5 childrenC_414 childrenD_414 children_work_414 (1, 4)
    required_414 envelope_414 pivot_mem_414 child_required_sub_414 child_envelope_sub_414 ?_
  intro b hb
  exact common_sub_414 (mem_commonEnvelope childrenD_414 b hb)
def required_417 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_417 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_417 : Fin 2 → Finset Cell := ![(placed21 2 (4, 2) required_0), required_416]
def childrenD_417 : Fin 2 → Finset Cell := ![(placed21 2 (4, 2) envelope_0), envelope_416]
theorem common_sub_417 : commonEnvelope childrenD_417 ⊆ insert (3, 2) required_417 := by decide +kernel
theorem child_required_sub_417 : ∀ j, childrenC_417 j ⊆ insert (3, 2) required_417 := by decide +kernel
theorem child_envelope_sub_417 : ∀ j, childrenD_417 j ⊆ envelope_417 := by decide +kernel
theorem pivot_mem_417 : (3, 2) ∈ envelope_417 := by decide +kernel
theorem children_work_417 : ∀ j, Template HasSnaky 5 (childrenC_417 j) (childrenD_417 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 2 (4, 2)).mono (by decide +kernel)
  · exact row_works_416.mono (by decide +kernel)
theorem row_works_417 : Template HasSnaky 6 required_417 envelope_417 := by
  refine compose HasSnaky 5 childrenC_417 childrenD_417 children_work_417 (3, 2)
    required_417 envelope_417 pivot_mem_417 child_required_sub_417 child_envelope_sub_417 ?_
  intro b hb
  exact common_sub_417 (mem_commonEnvelope childrenD_417 b hb)
def required_423_i0 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 3), (2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_423_i0 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_423_i0 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) required_5), required_244]
def childrenD_423_i0 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) envelope_5), envelope_244]
theorem common_sub_423_i0 : commonEnvelope childrenD_423_i0 ⊆ insert (1, 2) required_423_i0 := by decide +kernel
theorem child_required_sub_423_i0 : ∀ j, childrenC_423_i0 j ⊆ insert (1, 2) required_423_i0 := by decide +kernel
theorem child_envelope_sub_423_i0 : ∀ j, childrenD_423_i0 j ⊆ envelope_423_i0 := by decide +kernel
theorem pivot_mem_423_i0 : (1, 2) ∈ envelope_423_i0 := by decide +kernel
theorem children_work_423_i0 : ∀ j, Template HasSnaky 2 (childrenC_423_i0 j) (childrenD_423_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 6 (4, 3)).mono (by decide +kernel)
  · exact row_works_244.mono (by decide +kernel)
theorem row_works_423_i0 : Template HasSnaky 3 required_423_i0 envelope_423_i0 := by
  refine compose HasSnaky 2 childrenC_423_i0 childrenD_423_i0 children_work_423_i0 (1, 2)
    required_423_i0 envelope_423_i0 pivot_mem_423_i0 child_required_sub_423_i0 child_envelope_sub_423_i0 ?_
  intro b hb
  exact common_sub_423_i0 (mem_commonEnvelope childrenD_423_i0 b hb)
def required_423 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 3), (3, 0), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_423 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 3), (3, 0), (3, 1), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 2), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_423 : Fin 2 → Finset Cell := ![(placed21 4 (1, 5) required_383), required_423_i0]
def childrenD_423 : Fin 2 → Finset Cell := ![(placed21 4 (1, 5) envelope_383), envelope_423_i0]
theorem common_sub_423 : commonEnvelope childrenD_423 ⊆ insert (2, 3) required_423 := by decide +kernel
theorem child_required_sub_423 : ∀ j, childrenC_423 j ⊆ insert (2, 3) required_423 := by decide +kernel
theorem child_envelope_sub_423 : ∀ j, childrenD_423 j ⊆ envelope_423 := by decide +kernel
theorem pivot_mem_423 : (2, 3) ∈ envelope_423 := by decide +kernel
theorem children_work_423 : ∀ j, Template HasSnaky 5 (childrenC_423 j) (childrenD_423 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_383 4 (1, 5)).mono (by decide +kernel)
  · exact row_works_423_i0.mono (by decide +kernel)
theorem row_works_423 : Template HasSnaky 6 required_423 envelope_423 := by
  refine compose HasSnaky 5 childrenC_423 childrenD_423 children_work_423 (2, 3)
    required_423 envelope_423 pivot_mem_423 child_required_sub_423 child_envelope_sub_423 ?_
  intro b hb
  exact common_sub_423 (mem_commonEnvelope childrenD_423 b hb)
def required_429_i0 : Finset Cell := ⟨(([(0, 2), (1, 2), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_429_i0 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 2), (1, 4), (2, 2), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (4, 3), (4, 4), (4, 5), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_429_i0 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) required_2), (placed21 5 (5, 1) required_46)]
def childrenD_429_i0 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) envelope_2), (placed21 5 (5, 1) envelope_46)]
theorem common_sub_429_i0 : commonEnvelope childrenD_429_i0 ⊆ insert (4, 3) required_429_i0 := by decide +kernel
theorem child_required_sub_429_i0 : ∀ j, childrenC_429_i0 j ⊆ insert (4, 3) required_429_i0 := by decide +kernel
theorem child_envelope_sub_429_i0 : ∀ j, childrenD_429_i0 j ⊆ envelope_429_i0 := by decide +kernel
theorem pivot_mem_429_i0 : (4, 3) ∈ envelope_429_i0 := by decide +kernel
theorem children_work_429_i0 : ∀ j, Template HasSnaky 4 (childrenC_429_i0 j) (childrenD_429_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_46 5 (5, 1)).mono (by decide +kernel)
theorem row_works_429_i0 : Template HasSnaky 5 required_429_i0 envelope_429_i0 := by
  refine compose HasSnaky 4 childrenC_429_i0 childrenD_429_i0 children_work_429_i0 (4, 3)
    required_429_i0 envelope_429_i0 pivot_mem_429_i0 child_required_sub_429_i0 child_envelope_sub_429_i0 ?_
  intro b hb
  exact common_sub_429_i0 (mem_commonEnvelope childrenD_429_i0 b hb)
def required_429 : Finset Cell := ⟨(([(0, 2), (1, 2), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_429 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 2), (1, 4), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 3), (4, 4), (4, 5), (4, 6), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_429 : Fin 4 → Finset Cell := ![(placed21 2 (3, 0) required_7), (placed21 1 (2, 1) required_8), (placed21 0 (2, 0) required_9), required_429_i0]
def childrenD_429 : Fin 4 → Finset Cell := ![(placed21 2 (3, 0) envelope_7), (placed21 1 (2, 1) envelope_8), (placed21 0 (2, 0) envelope_9), envelope_429_i0]
theorem common_sub_429 : commonEnvelope childrenD_429 ⊆ insert (3, 4) required_429 := by decide +kernel
theorem child_required_sub_429 : ∀ j, childrenC_429 j ⊆ insert (3, 4) required_429 := by decide +kernel
theorem child_envelope_sub_429 : ∀ j, childrenD_429 j ⊆ envelope_429 := by decide +kernel
theorem pivot_mem_429 : (3, 4) ∈ envelope_429 := by decide +kernel
theorem children_work_429 : ∀ j, Template HasSnaky 5 (childrenC_429 j) (childrenD_429 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 2 (3, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 1 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 0 (2, 0)).mono (by decide +kernel)
  · exact row_works_429_i0.mono (by decide +kernel)
theorem row_works_429 : Template HasSnaky 6 required_429 envelope_429 := by
  refine compose HasSnaky 5 childrenC_429 childrenD_429 children_work_429 (3, 4)
    required_429 envelope_429 pivot_mem_429 child_required_sub_429 child_envelope_sub_429 ?_
  intro b hb
  exact common_sub_429 (mem_commonEnvelope childrenD_429 b hb)
def required_435_i1 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 3), (3, 4), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_435_i1 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 2), (2, 3), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_435_i1 : Fin 2 → Finset Cell := ![(placed21 4 (0, 3) required_0), (placed21 2 (4, 1) required_212)]
def childrenD_435_i1 : Fin 2 → Finset Cell := ![(placed21 4 (0, 3) envelope_0), (placed21 2 (4, 1) envelope_212)]
theorem common_sub_435_i1 : commonEnvelope childrenD_435_i1 ⊆ insert (3, 2) required_435_i1 := by decide +kernel
theorem child_required_sub_435_i1 : ∀ j, childrenC_435_i1 j ⊆ insert (3, 2) required_435_i1 := by decide +kernel
theorem child_envelope_sub_435_i1 : ∀ j, childrenD_435_i1 j ⊆ envelope_435_i1 := by decide +kernel
theorem pivot_mem_435_i1 : (3, 2) ∈ envelope_435_i1 := by decide +kernel
theorem children_work_435_i1 : ∀ j, Template HasSnaky 3 (childrenC_435_i1 j) (childrenD_435_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 4 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_212 2 (4, 1)).mono (by decide +kernel)
theorem row_works_435_i1 : Template HasSnaky 4 required_435_i1 envelope_435_i1 := by
  refine compose HasSnaky 3 childrenC_435_i1 childrenD_435_i1 children_work_435_i1 (3, 2)
    required_435_i1 envelope_435_i1 pivot_mem_435_i1 child_required_sub_435_i1 child_envelope_sub_435_i1 ?_
  intro b hb
  exact common_sub_435_i1 (mem_commonEnvelope childrenD_435_i1 b hb)
def required_435_i3 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 4), (3, 5), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_435_i3 : Finset Cell := ⟨(([(2, 1), (2, 2), (2, 3), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_435_i3 : Fin 2 → Finset Cell := ![(placed21 3 (3, 5) required_5), (placed21 2 (3, 1) required_11)]
def childrenD_435_i3 : Fin 2 → Finset Cell := ![(placed21 3 (3, 5) envelope_5), (placed21 2 (3, 1) envelope_11)]
theorem common_sub_435_i3 : commonEnvelope childrenD_435_i3 ⊆ insert (3, 2) required_435_i3 := by decide +kernel
theorem child_required_sub_435_i3 : ∀ j, childrenC_435_i3 j ⊆ insert (3, 2) required_435_i3 := by decide +kernel
theorem child_envelope_sub_435_i3 : ∀ j, childrenD_435_i3 j ⊆ envelope_435_i3 := by decide +kernel
theorem pivot_mem_435_i3 : (3, 2) ∈ envelope_435_i3 := by decide +kernel
theorem children_work_435_i3 : ∀ j, Template HasSnaky 2 (childrenC_435_i3 j) (childrenD_435_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (3, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_11 2 (3, 1)).mono (by decide +kernel)
theorem row_works_435_i3 : Template HasSnaky 3 required_435_i3 envelope_435_i3 := by
  refine compose HasSnaky 2 childrenC_435_i3 childrenD_435_i3 children_work_435_i3 (3, 2)
    required_435_i3 envelope_435_i3 pivot_mem_435_i3 child_required_sub_435_i3 child_envelope_sub_435_i3 ?_
  intro b hb
  exact common_sub_435_i3 (mem_commonEnvelope childrenD_435_i3 b hb)
def required_435_i2 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 4), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_435_i2 : Finset Cell := ⟨(([(2, 1), (2, 2), (2, 3), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_435_i2 : Fin 3 → Finset Cell := ![(placed21 2 (4, 2) required_76), (placed21 4 (3, 5) required_130), required_435_i3]
def childrenD_435_i2 : Fin 3 → Finset Cell := ![(placed21 2 (4, 2) envelope_76), (placed21 4 (3, 5) envelope_130), envelope_435_i3]
theorem common_sub_435_i2 : commonEnvelope childrenD_435_i2 ⊆ insert (3, 5) required_435_i2 := by decide +kernel
theorem child_required_sub_435_i2 : ∀ j, childrenC_435_i2 j ⊆ insert (3, 5) required_435_i2 := by decide +kernel
theorem child_envelope_sub_435_i2 : ∀ j, childrenD_435_i2 j ⊆ envelope_435_i2 := by decide +kernel
theorem pivot_mem_435_i2 : (3, 5) ∈ envelope_435_i2 := by decide +kernel
theorem children_work_435_i2 : ∀ j, Template HasSnaky 3 (childrenC_435_i2 j) (childrenD_435_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_76 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_130 4 (3, 5)).mono (by decide +kernel)
  · exact row_works_435_i3.mono (by decide +kernel)
theorem row_works_435_i2 : Template HasSnaky 4 required_435_i2 envelope_435_i2 := by
  refine compose HasSnaky 3 childrenC_435_i2 childrenD_435_i2 children_work_435_i2 (3, 5)
    required_435_i2 envelope_435_i2 pivot_mem_435_i2 child_required_sub_435_i2 child_envelope_sub_435_i2 ?_
  intro b hb
  exact common_sub_435_i2 (mem_commonEnvelope childrenD_435_i2 b hb)
def required_435_i0 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 3), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_435_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 1), (2, 2), (2, 3), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_435_i0 : Fin 4 → Finset Cell := ![(placed21 1 (0, 3) required_52), (placed21 5 (4, 2) required_76), required_435_i1, required_435_i2]
def childrenD_435_i0 : Fin 4 → Finset Cell := ![(placed21 1 (0, 3) envelope_52), (placed21 5 (4, 2) envelope_76), envelope_435_i1, envelope_435_i2]
theorem common_sub_435_i0 : commonEnvelope childrenD_435_i0 ⊆ insert (3, 4) required_435_i0 := by decide +kernel
theorem child_required_sub_435_i0 : ∀ j, childrenC_435_i0 j ⊆ insert (3, 4) required_435_i0 := by decide +kernel
theorem child_envelope_sub_435_i0 : ∀ j, childrenD_435_i0 j ⊆ envelope_435_i0 := by decide +kernel
theorem pivot_mem_435_i0 : (3, 4) ∈ envelope_435_i0 := by decide +kernel
theorem children_work_435_i0 : ∀ j, Template HasSnaky 4 (childrenC_435_i0 j) (childrenD_435_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_76 5 (4, 2)).mono (by decide +kernel)
  · exact row_works_435_i1.mono (by decide +kernel)
  · exact row_works_435_i2.mono (by decide +kernel)
theorem row_works_435_i0 : Template HasSnaky 5 required_435_i0 envelope_435_i0 := by
  refine compose HasSnaky 4 childrenC_435_i0 childrenD_435_i0 children_work_435_i0 (3, 4)
    required_435_i0 envelope_435_i0 pivot_mem_435_i0 child_required_sub_435_i0 child_envelope_sub_435_i0 ?_
  intro b hb
  exact common_sub_435_i0 (mem_commonEnvelope childrenD_435_i0 b hb)
def required_435 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_435 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 1), (2, 2), (2, 3), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 2), (5, 4), (6, 2), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_435 : Fin 4 → Finset Cell := ![(placed21 3 (1, 3) required_130), (placed21 3 (0, 3) required_140), (placed21 4 (0, 5) required_183), required_435_i0]
def childrenD_435 : Fin 4 → Finset Cell := ![(placed21 3 (1, 3) envelope_130), (placed21 3 (0, 3) envelope_140), (placed21 4 (0, 5) envelope_183), envelope_435_i0]
theorem common_sub_435 : commonEnvelope childrenD_435 ⊆ insert (4, 2) required_435 := by decide +kernel
theorem child_required_sub_435 : ∀ j, childrenC_435 j ⊆ insert (4, 2) required_435 := by decide +kernel
theorem child_envelope_sub_435 : ∀ j, childrenD_435 j ⊆ envelope_435 := by decide +kernel
theorem pivot_mem_435 : (4, 2) ∈ envelope_435 := by decide +kernel
theorem children_work_435 : ∀ j, Template HasSnaky 5 (childrenC_435 j) (childrenD_435 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_130 3 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_140 3 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_183 4 (0, 5)).mono (by decide +kernel)
  · exact row_works_435_i0.mono (by decide +kernel)
theorem row_works_435 : Template HasSnaky 6 required_435 envelope_435 := by
  refine compose HasSnaky 5 childrenC_435 childrenD_435 children_work_435 (4, 2)
    required_435 envelope_435 pivot_mem_435 child_required_sub_435 child_envelope_sub_435 ?_
  intro b hb
  exact common_sub_435 (mem_commonEnvelope childrenD_435 b hb)
def height_378_i0 : ℕ := 5
def childrenH_378_i0 : Fin 2 → ℕ := ![height_5, height_18]
theorem height_exact_378_i0 : height_378_i0 = 1 + Finset.univ.sup childrenH_378_i0 := by decide +kernel
theorem required_origin_378_i0 : ∀ x ∈ required_378_i0,
    (∃ j, x ∈ childrenC_378_i0 j) ∨ ∀ j, x ∈ childrenD_378_i0 j := by decide +kernel
theorem required_exact_378_i0 : required_378_i0 =
    ((Finset.univ.biUnion childrenC_378_i0) ∪ commonEnvelope childrenD_378_i0).erase (3, 3) := by
  exact required_eq_combination childrenC_378_i0 childrenD_378_i0 (3, 3) required_378_i0
    (by decide +kernel) child_required_sub_378_i0 common_sub_378_i0 required_origin_378_i0
theorem envelope_origin_378_i0 : ∀ x ∈ envelope_378_i0,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_378_i0 j := by decide +kernel
theorem envelope_exact_378_i0 : envelope_378_i0 =
    insert (3, 3) (Finset.univ.biUnion childrenD_378_i0) := by
  exact envelope_eq_combination childrenD_378_i0 (3, 3) envelope_378_i0
    pivot_mem_378_i0 child_envelope_sub_378_i0 envelope_origin_378_i0
def checked_378_i0 : CheckedCard where
  required := required_378_i0
  envelope := envelope_378_i0
  height := height_378_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_378_i0
def height_378 : ℕ := 6
def childrenH_378 : Fin 2 → ℕ := ![height_5, height_378_i0]
theorem height_exact_378 : height_378 = 1 + Finset.univ.sup childrenH_378 := by decide +kernel
theorem required_origin_378 : ∀ x ∈ required_378,
    (∃ j, x ∈ childrenC_378 j) ∨ ∀ j, x ∈ childrenD_378 j := by decide +kernel
theorem required_exact_378 : required_378 =
    ((Finset.univ.biUnion childrenC_378) ∪ commonEnvelope childrenD_378).erase (3, 1) := by
  exact required_eq_combination childrenC_378 childrenD_378 (3, 1) required_378
    (by decide +kernel) child_required_sub_378 common_sub_378 required_origin_378
theorem envelope_origin_378 : ∀ x ∈ envelope_378,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_378 j := by decide +kernel
theorem envelope_exact_378 : envelope_378 =
    insert (3, 1) (Finset.univ.biUnion childrenD_378) := by
  exact envelope_eq_combination childrenD_378 (3, 1) envelope_378
    pivot_mem_378 child_envelope_sub_378 envelope_origin_378
def checked_378 : CheckedCard where
  required := required_378
  envelope := envelope_378
  height := height_378
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_378
def height_384 : ℕ := 6
def childrenH_384 : Fin 2 → ℕ := ![height_8, height_383]
theorem height_exact_384 : height_384 = 1 + Finset.univ.sup childrenH_384 := by decide +kernel
theorem required_origin_384 : ∀ x ∈ required_384,
    (∃ j, x ∈ childrenC_384 j) ∨ ∀ j, x ∈ childrenD_384 j := by decide +kernel
theorem required_exact_384 : required_384 =
    ((Finset.univ.biUnion childrenC_384) ∪ commonEnvelope childrenD_384).erase (3, 3) := by
  exact required_eq_combination childrenC_384 childrenD_384 (3, 3) required_384
    (by decide +kernel) child_required_sub_384 common_sub_384 required_origin_384
theorem envelope_origin_384 : ∀ x ∈ envelope_384,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_384 j := by decide +kernel
theorem envelope_exact_384 : envelope_384 =
    insert (3, 3) (Finset.univ.biUnion childrenD_384) := by
  exact envelope_eq_combination childrenD_384 (3, 3) envelope_384
    pivot_mem_384 child_envelope_sub_384 envelope_origin_384
def checked_384 : CheckedCard where
  required := required_384
  envelope := envelope_384
  height := height_384
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_384
def height_387 : ℕ := 6
def childrenH_387 : Fin 3 → ℕ := ![height_200, height_376, height_386]
theorem height_exact_387 : height_387 = 1 + Finset.univ.sup childrenH_387 := by decide +kernel
theorem required_origin_387 : ∀ x ∈ required_387,
    (∃ j, x ∈ childrenC_387 j) ∨ ∀ j, x ∈ childrenD_387 j := by decide +kernel
theorem required_exact_387 : required_387 =
    ((Finset.univ.biUnion childrenC_387) ∪ commonEnvelope childrenD_387).erase (4, 2) := by
  exact required_eq_combination childrenC_387 childrenD_387 (4, 2) required_387
    (by decide +kernel) child_required_sub_387 common_sub_387 required_origin_387
theorem envelope_origin_387 : ∀ x ∈ envelope_387,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_387 j := by decide +kernel
theorem envelope_exact_387 : envelope_387 =
    insert (4, 2) (Finset.univ.biUnion childrenD_387) := by
  exact envelope_eq_combination childrenD_387 (4, 2) envelope_387
    pivot_mem_387 child_envelope_sub_387 envelope_origin_387
def checked_387 : CheckedCard where
  required := required_387
  envelope := envelope_387
  height := height_387
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_387
def height_390 : ℕ := 6
def childrenH_390 : Fin 3 → ℕ := ![height_11, height_17, height_389]
theorem height_exact_390 : height_390 = 1 + Finset.univ.sup childrenH_390 := by decide +kernel
theorem required_origin_390 : ∀ x ∈ required_390,
    (∃ j, x ∈ childrenC_390 j) ∨ ∀ j, x ∈ childrenD_390 j := by decide +kernel
theorem required_exact_390 : required_390 =
    ((Finset.univ.biUnion childrenC_390) ∪ commonEnvelope childrenD_390).erase (1, 7) := by
  exact required_eq_combination childrenC_390 childrenD_390 (1, 7) required_390
    (by decide +kernel) child_required_sub_390 common_sub_390 required_origin_390
theorem envelope_origin_390 : ∀ x ∈ envelope_390,
    x = (1, 7) ∨ ∃ j, x ∈ childrenD_390 j := by decide +kernel
theorem envelope_exact_390 : envelope_390 =
    insert (1, 7) (Finset.univ.biUnion childrenD_390) := by
  exact envelope_eq_combination childrenD_390 (1, 7) envelope_390
    pivot_mem_390 child_envelope_sub_390 envelope_origin_390
def checked_390 : CheckedCard where
  required := required_390
  envelope := envelope_390
  height := height_390
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_390
def height_392 : ℕ := 6
def childrenH_392 : Fin 2 → ℕ := ![height_0, height_391]
theorem height_exact_392 : height_392 = 1 + Finset.univ.sup childrenH_392 := by decide +kernel
theorem required_origin_392 : ∀ x ∈ required_392,
    (∃ j, x ∈ childrenC_392 j) ∨ ∀ j, x ∈ childrenD_392 j := by decide +kernel
theorem required_exact_392 : required_392 =
    ((Finset.univ.biUnion childrenC_392) ∪ commonEnvelope childrenD_392).erase (3, 3) := by
  exact required_eq_combination childrenC_392 childrenD_392 (3, 3) required_392
    (by decide +kernel) child_required_sub_392 common_sub_392 required_origin_392
theorem envelope_origin_392 : ∀ x ∈ envelope_392,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_392 j := by decide +kernel
theorem envelope_exact_392 : envelope_392 =
    insert (3, 3) (Finset.univ.biUnion childrenD_392) := by
  exact envelope_eq_combination childrenD_392 (3, 3) envelope_392
    pivot_mem_392 child_envelope_sub_392 envelope_origin_392
def checked_392 : CheckedCard where
  required := required_392
  envelope := envelope_392
  height := height_392
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_392
def height_393 : ℕ := 6
def childrenH_393 : Fin 3 → ℕ := ![height_11, height_20, height_391]
theorem height_exact_393 : height_393 = 1 + Finset.univ.sup childrenH_393 := by decide +kernel
theorem required_origin_393 : ∀ x ∈ required_393,
    (∃ j, x ∈ childrenC_393 j) ∨ ∀ j, x ∈ childrenD_393 j := by decide +kernel
theorem required_exact_393 : required_393 =
    ((Finset.univ.biUnion childrenC_393) ∪ commonEnvelope childrenD_393).erase (1, 4) := by
  exact required_eq_combination childrenC_393 childrenD_393 (1, 4) required_393
    (by decide +kernel) child_required_sub_393 common_sub_393 required_origin_393
theorem envelope_origin_393 : ∀ x ∈ envelope_393,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_393 j := by decide +kernel
theorem envelope_exact_393 : envelope_393 =
    insert (1, 4) (Finset.univ.biUnion childrenD_393) := by
  exact envelope_eq_combination childrenD_393 (1, 4) envelope_393
    pivot_mem_393 child_envelope_sub_393 envelope_origin_393
def checked_393 : CheckedCard where
  required := required_393
  envelope := envelope_393
  height := height_393
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_393
def height_403_i0 : ℕ := 5
def childrenH_403_i0 : Fin 2 → ℕ := ![height_4, height_381]
theorem height_exact_403_i0 : height_403_i0 = 1 + Finset.univ.sup childrenH_403_i0 := by decide +kernel
theorem required_origin_403_i0 : ∀ x ∈ required_403_i0,
    (∃ j, x ∈ childrenC_403_i0 j) ∨ ∀ j, x ∈ childrenD_403_i0 j := by decide +kernel
theorem required_exact_403_i0 : required_403_i0 =
    ((Finset.univ.biUnion childrenC_403_i0) ∪ commonEnvelope childrenD_403_i0).erase (2, 5) := by
  exact required_eq_combination childrenC_403_i0 childrenD_403_i0 (2, 5) required_403_i0
    (by decide +kernel) child_required_sub_403_i0 common_sub_403_i0 required_origin_403_i0
theorem envelope_origin_403_i0 : ∀ x ∈ envelope_403_i0,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_403_i0 j := by decide +kernel
theorem envelope_exact_403_i0 : envelope_403_i0 =
    insert (2, 5) (Finset.univ.biUnion childrenD_403_i0) := by
  exact envelope_eq_combination childrenD_403_i0 (2, 5) envelope_403_i0
    pivot_mem_403_i0 child_envelope_sub_403_i0 envelope_origin_403_i0
def checked_403_i0 : CheckedCard where
  required := required_403_i0
  envelope := envelope_403_i0
  height := height_403_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_403_i0
def height_403 : ℕ := 6
def childrenH_403 : Fin 2 → ℕ := ![height_86, height_403_i0]
theorem height_exact_403 : height_403 = 1 + Finset.univ.sup childrenH_403 := by decide +kernel
theorem required_origin_403 : ∀ x ∈ required_403,
    (∃ j, x ∈ childrenC_403 j) ∨ ∀ j, x ∈ childrenD_403 j := by decide +kernel
theorem required_exact_403 : required_403 =
    ((Finset.univ.biUnion childrenC_403) ∪ commonEnvelope childrenD_403).erase (1, 5) := by
  exact required_eq_combination childrenC_403 childrenD_403 (1, 5) required_403
    (by decide +kernel) child_required_sub_403 common_sub_403 required_origin_403
theorem envelope_origin_403 : ∀ x ∈ envelope_403,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_403 j := by decide +kernel
theorem envelope_exact_403 : envelope_403 =
    insert (1, 5) (Finset.univ.biUnion childrenD_403) := by
  exact envelope_eq_combination childrenD_403 (1, 5) envelope_403
    pivot_mem_403 child_envelope_sub_403 envelope_origin_403
def checked_403 : CheckedCard where
  required := required_403
  envelope := envelope_403
  height := height_403
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_403
def height_414 : ℕ := 6
def childrenH_414 : Fin 2 → ℕ := ![height_0, height_413]
theorem height_exact_414 : height_414 = 1 + Finset.univ.sup childrenH_414 := by decide +kernel
theorem required_origin_414 : ∀ x ∈ required_414,
    (∃ j, x ∈ childrenC_414 j) ∨ ∀ j, x ∈ childrenD_414 j := by decide +kernel
theorem required_exact_414 : required_414 =
    ((Finset.univ.biUnion childrenC_414) ∪ commonEnvelope childrenD_414).erase (1, 4) := by
  exact required_eq_combination childrenC_414 childrenD_414 (1, 4) required_414
    (by decide +kernel) child_required_sub_414 common_sub_414 required_origin_414
theorem envelope_origin_414 : ∀ x ∈ envelope_414,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_414 j := by decide +kernel
theorem envelope_exact_414 : envelope_414 =
    insert (1, 4) (Finset.univ.biUnion childrenD_414) := by
  exact envelope_eq_combination childrenD_414 (1, 4) envelope_414
    pivot_mem_414 child_envelope_sub_414 envelope_origin_414
def checked_414 : CheckedCard where
  required := required_414
  envelope := envelope_414
  height := height_414
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_414
def height_417 : ℕ := 6
def childrenH_417 : Fin 2 → ℕ := ![height_0, height_416]
theorem height_exact_417 : height_417 = 1 + Finset.univ.sup childrenH_417 := by decide +kernel
theorem required_origin_417 : ∀ x ∈ required_417,
    (∃ j, x ∈ childrenC_417 j) ∨ ∀ j, x ∈ childrenD_417 j := by decide +kernel
theorem required_exact_417 : required_417 =
    ((Finset.univ.biUnion childrenC_417) ∪ commonEnvelope childrenD_417).erase (3, 2) := by
  exact required_eq_combination childrenC_417 childrenD_417 (3, 2) required_417
    (by decide +kernel) child_required_sub_417 common_sub_417 required_origin_417
theorem envelope_origin_417 : ∀ x ∈ envelope_417,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_417 j := by decide +kernel
theorem envelope_exact_417 : envelope_417 =
    insert (3, 2) (Finset.univ.biUnion childrenD_417) := by
  exact envelope_eq_combination childrenD_417 (3, 2) envelope_417
    pivot_mem_417 child_envelope_sub_417 envelope_origin_417
def checked_417 : CheckedCard where
  required := required_417
  envelope := envelope_417
  height := height_417
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_417
def height_423_i0 : ℕ := 3
def childrenH_423_i0 : Fin 2 → ℕ := ![height_5, height_244]
theorem height_exact_423_i0 : height_423_i0 = 1 + Finset.univ.sup childrenH_423_i0 := by decide +kernel
theorem required_origin_423_i0 : ∀ x ∈ required_423_i0,
    (∃ j, x ∈ childrenC_423_i0 j) ∨ ∀ j, x ∈ childrenD_423_i0 j := by decide +kernel
theorem required_exact_423_i0 : required_423_i0 =
    ((Finset.univ.biUnion childrenC_423_i0) ∪ commonEnvelope childrenD_423_i0).erase (1, 2) := by
  exact required_eq_combination childrenC_423_i0 childrenD_423_i0 (1, 2) required_423_i0
    (by decide +kernel) child_required_sub_423_i0 common_sub_423_i0 required_origin_423_i0
theorem envelope_origin_423_i0 : ∀ x ∈ envelope_423_i0,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_423_i0 j := by decide +kernel
theorem envelope_exact_423_i0 : envelope_423_i0 =
    insert (1, 2) (Finset.univ.biUnion childrenD_423_i0) := by
  exact envelope_eq_combination childrenD_423_i0 (1, 2) envelope_423_i0
    pivot_mem_423_i0 child_envelope_sub_423_i0 envelope_origin_423_i0
def checked_423_i0 : CheckedCard where
  required := required_423_i0
  envelope := envelope_423_i0
  height := height_423_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_423_i0
def height_423 : ℕ := 6
def childrenH_423 : Fin 2 → ℕ := ![height_383, height_423_i0]
theorem height_exact_423 : height_423 = 1 + Finset.univ.sup childrenH_423 := by decide +kernel
theorem required_origin_423 : ∀ x ∈ required_423,
    (∃ j, x ∈ childrenC_423 j) ∨ ∀ j, x ∈ childrenD_423 j := by decide +kernel
theorem required_exact_423 : required_423 =
    ((Finset.univ.biUnion childrenC_423) ∪ commonEnvelope childrenD_423).erase (2, 3) := by
  exact required_eq_combination childrenC_423 childrenD_423 (2, 3) required_423
    (by decide +kernel) child_required_sub_423 common_sub_423 required_origin_423
theorem envelope_origin_423 : ∀ x ∈ envelope_423,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_423 j := by decide +kernel
theorem envelope_exact_423 : envelope_423 =
    insert (2, 3) (Finset.univ.biUnion childrenD_423) := by
  exact envelope_eq_combination childrenD_423 (2, 3) envelope_423
    pivot_mem_423 child_envelope_sub_423 envelope_origin_423
def checked_423 : CheckedCard where
  required := required_423
  envelope := envelope_423
  height := height_423
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_423
def height_429_i0 : ℕ := 5
def childrenH_429_i0 : Fin 2 → ℕ := ![height_2, height_46]
theorem height_exact_429_i0 : height_429_i0 = 1 + Finset.univ.sup childrenH_429_i0 := by decide +kernel
theorem required_origin_429_i0 : ∀ x ∈ required_429_i0,
    (∃ j, x ∈ childrenC_429_i0 j) ∨ ∀ j, x ∈ childrenD_429_i0 j := by decide +kernel
theorem required_exact_429_i0 : required_429_i0 =
    ((Finset.univ.biUnion childrenC_429_i0) ∪ commonEnvelope childrenD_429_i0).erase (4, 3) := by
  exact required_eq_combination childrenC_429_i0 childrenD_429_i0 (4, 3) required_429_i0
    (by decide +kernel) child_required_sub_429_i0 common_sub_429_i0 required_origin_429_i0
theorem envelope_origin_429_i0 : ∀ x ∈ envelope_429_i0,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_429_i0 j := by decide +kernel
theorem envelope_exact_429_i0 : envelope_429_i0 =
    insert (4, 3) (Finset.univ.biUnion childrenD_429_i0) := by
  exact envelope_eq_combination childrenD_429_i0 (4, 3) envelope_429_i0
    pivot_mem_429_i0 child_envelope_sub_429_i0 envelope_origin_429_i0
def checked_429_i0 : CheckedCard where
  required := required_429_i0
  envelope := envelope_429_i0
  height := height_429_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_429_i0
def height_429 : ℕ := 6
def childrenH_429 : Fin 4 → ℕ := ![height_7, height_8, height_9, height_429_i0]
theorem height_exact_429 : height_429 = 1 + Finset.univ.sup childrenH_429 := by decide +kernel
theorem required_origin_429 : ∀ x ∈ required_429,
    (∃ j, x ∈ childrenC_429 j) ∨ ∀ j, x ∈ childrenD_429 j := by decide +kernel
theorem required_exact_429 : required_429 =
    ((Finset.univ.biUnion childrenC_429) ∪ commonEnvelope childrenD_429).erase (3, 4) := by
  exact required_eq_combination childrenC_429 childrenD_429 (3, 4) required_429
    (by decide +kernel) child_required_sub_429 common_sub_429 required_origin_429
theorem envelope_origin_429 : ∀ x ∈ envelope_429,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_429 j := by decide +kernel
theorem envelope_exact_429 : envelope_429 =
    insert (3, 4) (Finset.univ.biUnion childrenD_429) := by
  exact envelope_eq_combination childrenD_429 (3, 4) envelope_429
    pivot_mem_429 child_envelope_sub_429 envelope_origin_429
def checked_429 : CheckedCard where
  required := required_429
  envelope := envelope_429
  height := height_429
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_429
def height_435_i1 : ℕ := 4
def childrenH_435_i1 : Fin 2 → ℕ := ![height_0, height_212]
theorem height_exact_435_i1 : height_435_i1 = 1 + Finset.univ.sup childrenH_435_i1 := by decide +kernel
theorem required_origin_435_i1 : ∀ x ∈ required_435_i1,
    (∃ j, x ∈ childrenC_435_i1 j) ∨ ∀ j, x ∈ childrenD_435_i1 j := by decide +kernel
theorem required_exact_435_i1 : required_435_i1 =
    ((Finset.univ.biUnion childrenC_435_i1) ∪ commonEnvelope childrenD_435_i1).erase (3, 2) := by
  exact required_eq_combination childrenC_435_i1 childrenD_435_i1 (3, 2) required_435_i1
    (by decide +kernel) child_required_sub_435_i1 common_sub_435_i1 required_origin_435_i1
theorem envelope_origin_435_i1 : ∀ x ∈ envelope_435_i1,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_435_i1 j := by decide +kernel
theorem envelope_exact_435_i1 : envelope_435_i1 =
    insert (3, 2) (Finset.univ.biUnion childrenD_435_i1) := by
  exact envelope_eq_combination childrenD_435_i1 (3, 2) envelope_435_i1
    pivot_mem_435_i1 child_envelope_sub_435_i1 envelope_origin_435_i1
def checked_435_i1 : CheckedCard where
  required := required_435_i1
  envelope := envelope_435_i1
  height := height_435_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_435_i1
def height_435_i3 : ℕ := 3
def childrenH_435_i3 : Fin 2 → ℕ := ![height_5, height_11]
theorem height_exact_435_i3 : height_435_i3 = 1 + Finset.univ.sup childrenH_435_i3 := by decide +kernel
theorem required_origin_435_i3 : ∀ x ∈ required_435_i3,
    (∃ j, x ∈ childrenC_435_i3 j) ∨ ∀ j, x ∈ childrenD_435_i3 j := by decide +kernel
theorem required_exact_435_i3 : required_435_i3 =
    ((Finset.univ.biUnion childrenC_435_i3) ∪ commonEnvelope childrenD_435_i3).erase (3, 2) := by
  exact required_eq_combination childrenC_435_i3 childrenD_435_i3 (3, 2) required_435_i3
    (by decide +kernel) child_required_sub_435_i3 common_sub_435_i3 required_origin_435_i3
theorem envelope_origin_435_i3 : ∀ x ∈ envelope_435_i3,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_435_i3 j := by decide +kernel
theorem envelope_exact_435_i3 : envelope_435_i3 =
    insert (3, 2) (Finset.univ.biUnion childrenD_435_i3) := by
  exact envelope_eq_combination childrenD_435_i3 (3, 2) envelope_435_i3
    pivot_mem_435_i3 child_envelope_sub_435_i3 envelope_origin_435_i3
def checked_435_i3 : CheckedCard where
  required := required_435_i3
  envelope := envelope_435_i3
  height := height_435_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_435_i3
def height_435_i2 : ℕ := 4
def childrenH_435_i2 : Fin 3 → ℕ := ![height_76, height_130, height_435_i3]
theorem height_exact_435_i2 : height_435_i2 = 1 + Finset.univ.sup childrenH_435_i2 := by decide +kernel
theorem required_origin_435_i2 : ∀ x ∈ required_435_i2,
    (∃ j, x ∈ childrenC_435_i2 j) ∨ ∀ j, x ∈ childrenD_435_i2 j := by decide +kernel
theorem required_exact_435_i2 : required_435_i2 =
    ((Finset.univ.biUnion childrenC_435_i2) ∪ commonEnvelope childrenD_435_i2).erase (3, 5) := by
  exact required_eq_combination childrenC_435_i2 childrenD_435_i2 (3, 5) required_435_i2
    (by decide +kernel) child_required_sub_435_i2 common_sub_435_i2 required_origin_435_i2
theorem envelope_origin_435_i2 : ∀ x ∈ envelope_435_i2,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_435_i2 j := by decide +kernel
theorem envelope_exact_435_i2 : envelope_435_i2 =
    insert (3, 5) (Finset.univ.biUnion childrenD_435_i2) := by
  exact envelope_eq_combination childrenD_435_i2 (3, 5) envelope_435_i2
    pivot_mem_435_i2 child_envelope_sub_435_i2 envelope_origin_435_i2
def checked_435_i2 : CheckedCard where
  required := required_435_i2
  envelope := envelope_435_i2
  height := height_435_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_435_i2
def height_435_i0 : ℕ := 5
def childrenH_435_i0 : Fin 4 → ℕ := ![height_52, height_76, height_435_i1, height_435_i2]
theorem height_exact_435_i0 : height_435_i0 = 1 + Finset.univ.sup childrenH_435_i0 := by decide +kernel
theorem required_origin_435_i0 : ∀ x ∈ required_435_i0,
    (∃ j, x ∈ childrenC_435_i0 j) ∨ ∀ j, x ∈ childrenD_435_i0 j := by decide +kernel
theorem required_exact_435_i0 : required_435_i0 =
    ((Finset.univ.biUnion childrenC_435_i0) ∪ commonEnvelope childrenD_435_i0).erase (3, 4) := by
  exact required_eq_combination childrenC_435_i0 childrenD_435_i0 (3, 4) required_435_i0
    (by decide +kernel) child_required_sub_435_i0 common_sub_435_i0 required_origin_435_i0
theorem envelope_origin_435_i0 : ∀ x ∈ envelope_435_i0,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_435_i0 j := by decide +kernel
theorem envelope_exact_435_i0 : envelope_435_i0 =
    insert (3, 4) (Finset.univ.biUnion childrenD_435_i0) := by
  exact envelope_eq_combination childrenD_435_i0 (3, 4) envelope_435_i0
    pivot_mem_435_i0 child_envelope_sub_435_i0 envelope_origin_435_i0
def checked_435_i0 : CheckedCard where
  required := required_435_i0
  envelope := envelope_435_i0
  height := height_435_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_435_i0
def height_435 : ℕ := 6
def childrenH_435 : Fin 4 → ℕ := ![height_130, height_140, height_183, height_435_i0]
theorem height_exact_435 : height_435 = 1 + Finset.univ.sup childrenH_435 := by decide +kernel
theorem required_origin_435 : ∀ x ∈ required_435,
    (∃ j, x ∈ childrenC_435 j) ∨ ∀ j, x ∈ childrenD_435 j := by decide +kernel
theorem required_exact_435 : required_435 =
    ((Finset.univ.biUnion childrenC_435) ∪ commonEnvelope childrenD_435).erase (4, 2) := by
  exact required_eq_combination childrenC_435 childrenD_435 (4, 2) required_435
    (by decide +kernel) child_required_sub_435 common_sub_435 required_origin_435
theorem envelope_origin_435 : ∀ x ∈ envelope_435,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_435 j := by decide +kernel
theorem envelope_exact_435 : envelope_435 =
    insert (4, 2) (Finset.univ.biUnion childrenD_435) := by
  exact envelope_eq_combination childrenD_435 (4, 2) envelope_435
    pivot_mem_435 child_envelope_sub_435 envelope_origin_435
def checked_435 : CheckedCard where
  required := required_435
  envelope := envelope_435
  height := height_435
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_435
end SnakyPrototype.Certificate21

end OAI
