import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_658_i0 : Finset Cell := ⟨(([(0, 4), (1, 5), (2, 3), (2, 4), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_658_i0 : Finset Cell := ⟨(([(0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 2), (3, 3), (3, 7), (3, 8), (3, 9), (4, 2), (4, 3), (4, 4), (5, 2), (5, 3), (5, 4), (6, 2), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_658_i0 : Fin 2 → Finset Cell := ![(placed21 1 (1, 3) required_314), (placed21 3 (0, 6) required_378)]
def childrenD_658_i0 : Fin 2 → Finset Cell := ![(placed21 1 (1, 3) envelope_314), (placed21 3 (0, 6) envelope_378)]
theorem common_sub_658_i0 : commonEnvelope childrenD_658_i0 ⊆ insert (2, 6) required_658_i0 := by decide +kernel
theorem child_required_sub_658_i0 : ∀ j, childrenC_658_i0 j ⊆ insert (2, 6) required_658_i0 := by decide +kernel
theorem child_envelope_sub_658_i0 : ∀ j, childrenD_658_i0 j ⊆ envelope_658_i0 := by decide +kernel
theorem pivot_mem_658_i0 : (2, 6) ∈ envelope_658_i0 := by decide +kernel
theorem children_work_658_i0 : ∀ j, Template HasSnaky 6 (childrenC_658_i0 j) (childrenD_658_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_314 1 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_378 3 (0, 6)).mono (by decide +kernel)
theorem row_works_658_i0 : Template HasSnaky 7 required_658_i0 envelope_658_i0 := by
  refine compose HasSnaky 6 childrenC_658_i0 childrenD_658_i0 children_work_658_i0 (2, 6)
    required_658_i0 envelope_658_i0 pivot_mem_658_i0 child_required_sub_658_i0 child_envelope_sub_658_i0 ?_
  intro b hb
  exact common_sub_658_i0 (mem_commonEnvelope childrenD_658_i0 b hb)
def required_658 : Finset Cell := ⟨(([(0, 4), (1, 5), (2, 4), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_658 : Finset Cell := ⟨(([(0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 1), (3, 2), (3, 3), (3, 7), (3, 8), (3, 9), (4, 2), (4, 3), (4, 4), (5, 2), (5, 3), (5, 4), (6, 2), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_658 : Fin 4 → Finset Cell := ![(placed21 6 (2, 6) required_27), (placed21 2 (2, 2) required_52), (placed21 4 (1, 9) required_284), required_658_i0]
def childrenD_658 : Fin 4 → Finset Cell := ![(placed21 6 (2, 6) envelope_27), (placed21 2 (2, 2) envelope_52), (placed21 4 (1, 9) envelope_284), envelope_658_i0]
theorem common_sub_658 : commonEnvelope childrenD_658 ⊆ insert (2, 3) required_658 := by decide +kernel
theorem child_required_sub_658 : ∀ j, childrenC_658 j ⊆ insert (2, 3) required_658 := by decide +kernel
theorem child_envelope_sub_658 : ∀ j, childrenD_658 j ⊆ envelope_658 := by decide +kernel
theorem pivot_mem_658 : (2, 3) ∈ envelope_658 := by decide +kernel
theorem children_work_658 : ∀ j, Template HasSnaky 7 (childrenC_658 j) (childrenD_658 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_27 6 (2, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 2 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_284 4 (1, 9)).mono (by decide +kernel)
  · exact row_works_658_i0.mono (by decide +kernel)
theorem row_works_658 : Template HasSnaky 8 required_658 envelope_658 := by
  refine compose HasSnaky 7 childrenC_658 childrenD_658 children_work_658 (2, 3)
    required_658 envelope_658 pivot_mem_658 child_required_sub_658 child_envelope_sub_658 ?_
  intro b hb
  exact common_sub_658 (mem_commonEnvelope childrenD_658 b hb)
def required_661_i0 : Finset Cell := ⟨(([(4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_661_i0 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 3), (6, 4), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_661_i0 : Fin 4 → Finset Cell := ![(placed21 6 (5, 7) required_9), (placed21 7 (7, 6) required_115), (placed21 7 (7, 7) required_302), (placed21 7 (7, 7) required_303)]
def childrenD_661_i0 : Fin 4 → Finset Cell := ![(placed21 6 (5, 7) envelope_9), (placed21 7 (7, 6) envelope_115), (placed21 7 (7, 7) envelope_302), (placed21 7 (7, 7) envelope_303)]
theorem common_sub_661_i0 : commonEnvelope childrenD_661_i0 ⊆ insert (4, 3) required_661_i0 := by decide +kernel
theorem child_required_sub_661_i0 : ∀ j, childrenC_661_i0 j ⊆ insert (4, 3) required_661_i0 := by decide +kernel
theorem child_envelope_sub_661_i0 : ∀ j, childrenD_661_i0 j ⊆ envelope_661_i0 := by decide +kernel
theorem pivot_mem_661_i0 : (4, 3) ∈ envelope_661_i0 := by decide +kernel
theorem children_work_661_i0 : ∀ j, Template HasSnaky 6 (childrenC_661_i0 j) (childrenD_661_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_9 6 (5, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_115 7 (7, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_302 7 (7, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_303 7 (7, 7)).mono (by decide +kernel)
theorem row_works_661_i0 : Template HasSnaky 7 required_661_i0 envelope_661_i0 := by
  refine compose HasSnaky 6 childrenC_661_i0 childrenD_661_i0 children_work_661_i0 (4, 3)
    required_661_i0 envelope_661_i0 pivot_mem_661_i0 child_required_sub_661_i0 child_envelope_sub_661_i0 ?_
  intro b hb
  exact common_sub_661_i0 (mem_commonEnvelope childrenD_661_i0 b hb)
def required_661 : Finset Cell := ⟨(([(4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_661 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 7), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 3), (6, 4), (6, 5), (7, 3), (7, 4), (7, 5), (8, 3), (8, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_661 : Fin 5 → Finset Cell := ![(placed21 0 (3, 2) required_13), (placed21 2 (5, 2) required_14), (placed21 0 (3, 2) required_33), (placed21 1 (1, 3) required_116), required_661_i0]
def childrenD_661 : Fin 5 → Finset Cell := ![(placed21 0 (3, 2) envelope_13), (placed21 2 (5, 2) envelope_14), (placed21 0 (3, 2) envelope_33), (placed21 1 (1, 3) envelope_116), envelope_661_i0]
theorem common_sub_661 : commonEnvelope childrenD_661 ⊆ insert (4, 6) required_661 := by decide +kernel
theorem child_required_sub_661 : ∀ j, childrenC_661 j ⊆ insert (4, 6) required_661 := by decide +kernel
theorem child_envelope_sub_661 : ∀ j, childrenD_661 j ⊆ envelope_661 := by decide +kernel
theorem pivot_mem_661 : (4, 6) ∈ envelope_661 := by decide +kernel
theorem children_work_661 : ∀ j, Template HasSnaky 7 (childrenC_661 j) (childrenD_661 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 0 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_14 2 (5, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_33 0 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_116 1 (1, 3)).mono (by decide +kernel)
  · exact row_works_661_i0.mono (by decide +kernel)
theorem row_works_661 : Template HasSnaky 8 required_661 envelope_661 := by
  refine compose HasSnaky 7 childrenC_661 childrenD_661 children_work_661 (4, 6)
    required_661 envelope_661 pivot_mem_661 child_required_sub_661 child_envelope_sub_661 ?_
  intro b hb
  exact common_sub_661 (mem_commonEnvelope childrenD_661 b hb)
def required_666_i1 : Finset Cell := ⟨(([(0, 2), (2, 3), (3, 2), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_666_i1 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 3), (3, 2), (3, 3), (4, 2), (4, 3), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4), (7, 2), (7, 3), (7, 4), (8, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_666_i1 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) required_4), (placed21 0 (1, 2) required_314)]
def childrenD_666_i1 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) envelope_4), (placed21 0 (1, 2) envelope_314)]
theorem common_sub_666_i1 : commonEnvelope childrenD_666_i1 ⊆ insert (1, 3) required_666_i1 := by decide +kernel
theorem child_required_sub_666_i1 : ∀ j, childrenC_666_i1 j ⊆ insert (1, 3) required_666_i1 := by decide +kernel
theorem child_envelope_sub_666_i1 : ∀ j, childrenD_666_i1 j ⊆ envelope_666_i1 := by decide +kernel
theorem pivot_mem_666_i1 : (1, 3) ∈ envelope_666_i1 := by decide +kernel
theorem children_work_666_i1 : ∀ j, Template HasSnaky 5 (childrenC_666_i1 j) (childrenD_666_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 6 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_314 0 (1, 2)).mono (by decide +kernel)
theorem row_works_666_i1 : Template HasSnaky 6 required_666_i1 envelope_666_i1 := by
  refine compose HasSnaky 5 childrenC_666_i1 childrenD_666_i1 children_work_666_i1 (1, 3)
    required_666_i1 envelope_666_i1 pivot_mem_666_i1 child_required_sub_666_i1 child_envelope_sub_666_i1 ?_
  intro b hb
  exact common_sub_666_i1 (mem_commonEnvelope childrenD_666_i1 b hb)
def required_666_i0 : Finset Cell := ⟨(([(0, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_666_i0 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3), (4, 2), (4, 3), (4, 4), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4), (7, 2), (7, 3), (7, 4), (8, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_666_i0 : Fin 2 → Finset Cell := ![(placed21 1 (3, 0) required_5), required_666_i1]
def childrenD_666_i0 : Fin 2 → Finset Cell := ![(placed21 1 (3, 0) envelope_5), envelope_666_i1]
theorem common_sub_666_i0 : commonEnvelope childrenD_666_i0 ⊆ insert (4, 3) required_666_i0 := by decide +kernel
theorem child_required_sub_666_i0 : ∀ j, childrenC_666_i0 j ⊆ insert (4, 3) required_666_i0 := by decide +kernel
theorem child_envelope_sub_666_i0 : ∀ j, childrenD_666_i0 j ⊆ envelope_666_i0 := by decide +kernel
theorem pivot_mem_666_i0 : (4, 3) ∈ envelope_666_i0 := by decide +kernel
theorem children_work_666_i0 : ∀ j, Template HasSnaky 6 (childrenC_666_i0 j) (childrenD_666_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (3, 0)).mono (by decide +kernel)
  · exact row_works_666_i1.mono (by decide +kernel)
theorem row_works_666_i0 : Template HasSnaky 7 required_666_i0 envelope_666_i0 := by
  refine compose HasSnaky 6 childrenC_666_i0 childrenD_666_i0 children_work_666_i0 (4, 3)
    required_666_i0 envelope_666_i0 pivot_mem_666_i0 child_required_sub_666_i0 child_envelope_sub_666_i0 ?_
  intro b hb
  exact common_sub_666_i0 (mem_commonEnvelope childrenD_666_i0 b hb)
def required_666 : Finset Cell := ⟨(([(0, 2), (3, 0), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_666 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (4, 2), (4, 3), (4, 4), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4), (7, 2), (7, 3), (7, 4), (8, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_666 : Fin 2 → Finset Cell := ![(placed21 5 (3, 0) required_5), required_666_i0]
def childrenD_666 : Fin 2 → Finset Cell := ![(placed21 5 (3, 0) envelope_5), envelope_666_i0]
theorem common_sub_666 : commonEnvelope childrenD_666 ⊆ insert (2, 3) required_666 := by decide +kernel
theorem child_required_sub_666 : ∀ j, childrenC_666 j ⊆ insert (2, 3) required_666 := by decide +kernel
theorem child_envelope_sub_666 : ∀ j, childrenD_666 j ⊆ envelope_666 := by decide +kernel
theorem pivot_mem_666 : (2, 3) ∈ envelope_666 := by decide +kernel
theorem children_work_666 : ∀ j, Template HasSnaky 7 (childrenC_666 j) (childrenD_666 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (3, 0)).mono (by decide +kernel)
  · exact row_works_666_i0.mono (by decide +kernel)
theorem row_works_666 : Template HasSnaky 8 required_666 envelope_666 := by
  refine compose HasSnaky 7 childrenC_666 childrenD_666 children_work_666 (2, 3)
    required_666 envelope_666 pivot_mem_666 child_required_sub_666 child_envelope_sub_666 ?_
  intro b hb
  exact common_sub_666 (mem_commonEnvelope childrenD_666 b hb)
def required_678_i1 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (2, 6), (3, 3), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_678_i1 : Finset Cell := ⟨(([(0, 4), (0, 6), (0, 7), (0, 8), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 4), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 6), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_678_i1 : Fin 2 → Finset Cell := ![(placed21 7 (5, 4) required_22), (placed21 2 (4, 2) required_382)]
def childrenD_678_i1 : Fin 2 → Finset Cell := ![(placed21 7 (5, 4) envelope_22), (placed21 2 (4, 2) envelope_382)]
theorem common_sub_678_i1 : commonEnvelope childrenD_678_i1 ⊆ insert (4, 3) required_678_i1 := by decide +kernel
theorem child_required_sub_678_i1 : ∀ j, childrenC_678_i1 j ⊆ insert (4, 3) required_678_i1 := by decide +kernel
theorem child_envelope_sub_678_i1 : ∀ j, childrenD_678_i1 j ⊆ envelope_678_i1 := by decide +kernel
theorem pivot_mem_678_i1 : (4, 3) ∈ envelope_678_i1 := by decide +kernel
theorem children_work_678_i1 : ∀ j, Template HasSnaky 5 (childrenC_678_i1 j) (childrenD_678_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_22 7 (5, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_382 2 (4, 2)).mono (by decide +kernel)
theorem row_works_678_i1 : Template HasSnaky 6 required_678_i1 envelope_678_i1 := by
  refine compose HasSnaky 5 childrenC_678_i1 childrenD_678_i1 children_work_678_i1 (4, 3)
    required_678_i1 envelope_678_i1 pivot_mem_678_i1 child_required_sub_678_i1 child_envelope_sub_678_i1 ?_
  intro b hb
  exact common_sub_678_i1 (mem_commonEnvelope childrenD_678_i1 b hb)
def required_678_i0 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (3, 3), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_678_i0 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 4), (0, 6), (0, 7), (0, 8), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 6), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_678_i0 : Fin 2 → Finset Cell := ![(placed21 6 (2, 6) required_18), required_678_i1]
def childrenD_678_i0 : Fin 2 → Finset Cell := ![(placed21 6 (2, 6) envelope_18), envelope_678_i1]
theorem common_sub_678_i0 : commonEnvelope childrenD_678_i0 ⊆ insert (2, 6) required_678_i0 := by decide +kernel
theorem child_required_sub_678_i0 : ∀ j, childrenC_678_i0 j ⊆ insert (2, 6) required_678_i0 := by decide +kernel
theorem child_envelope_sub_678_i0 : ∀ j, childrenD_678_i0 j ⊆ envelope_678_i0 := by decide +kernel
theorem pivot_mem_678_i0 : (2, 6) ∈ envelope_678_i0 := by decide +kernel
theorem children_work_678_i0 : ∀ j, Template HasSnaky 6 (childrenC_678_i0 j) (childrenD_678_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_18 6 (2, 6)).mono (by decide +kernel)
  · exact row_works_678_i1.mono (by decide +kernel)
theorem row_works_678_i0 : Template HasSnaky 7 required_678_i0 envelope_678_i0 := by
  refine compose HasSnaky 6 childrenC_678_i0 childrenD_678_i0 children_work_678_i0 (2, 6)
    required_678_i0 envelope_678_i0 pivot_mem_678_i0 child_required_sub_678_i0 child_envelope_sub_678_i0 ?_
  intro b hb
  exact common_sub_678_i0 (mem_commonEnvelope childrenD_678_i0 b hb)
def required_678 : Finset Cell := ⟨(([(1, 3), (1, 4), (3, 3), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_678 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 6), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_678 : Fin 3 → Finset Cell := ![(placed21 4 (0, 7) required_31), (placed21 3 (0, 5) required_160), required_678_i0]
def childrenD_678 : Fin 3 → Finset Cell := ![(placed21 4 (0, 7) envelope_31), (placed21 3 (0, 5) envelope_160), envelope_678_i0]
theorem common_sub_678 : commonEnvelope childrenD_678 ⊆ insert (1, 5) required_678 := by decide +kernel
theorem child_required_sub_678 : ∀ j, childrenC_678 j ⊆ insert (1, 5) required_678 := by decide +kernel
theorem child_envelope_sub_678 : ∀ j, childrenD_678 j ⊆ envelope_678 := by decide +kernel
theorem pivot_mem_678 : (1, 5) ∈ envelope_678 := by decide +kernel
theorem children_work_678 : ∀ j, Template HasSnaky 7 (childrenC_678 j) (childrenD_678 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_31 4 (0, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_160 3 (0, 5)).mono (by decide +kernel)
  · exact row_works_678_i0.mono (by decide +kernel)
theorem row_works_678 : Template HasSnaky 8 required_678 envelope_678 := by
  refine compose HasSnaky 7 childrenC_678 childrenD_678 children_work_678 (1, 5)
    required_678 envelope_678 pivot_mem_678 child_required_sub_678 child_envelope_sub_678 ?_
  intro b hb
  exact common_sub_678 (mem_commonEnvelope childrenD_678 b hb)
def required_703_i1 : Finset Cell := ⟨(([(1, 4), (2, 4), (3, 3), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_703_i1 : Finset Cell := ⟨(([(1, 4), (2, 3), (2, 4), (3, 3), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_703_i1 : Fin 2 → Finset Cell := ![(placed21 2 (5, 3) required_3), (placed21 0 (4, 2) required_27)]
def childrenD_703_i1 : Fin 2 → Finset Cell := ![(placed21 2 (5, 3) envelope_3), (placed21 0 (4, 2) envelope_27)]
theorem common_sub_703_i1 : commonEnvelope childrenD_703_i1 ⊆ insert (5, 3) required_703_i1 := by decide +kernel
theorem child_required_sub_703_i1 : ∀ j, childrenC_703_i1 j ⊆ insert (5, 3) required_703_i1 := by decide +kernel
theorem child_envelope_sub_703_i1 : ∀ j, childrenD_703_i1 j ⊆ envelope_703_i1 := by decide +kernel
theorem pivot_mem_703_i1 : (5, 3) ∈ envelope_703_i1 := by decide +kernel
theorem children_work_703_i1 : ∀ j, Template HasSnaky 4 (childrenC_703_i1 j) (childrenD_703_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 2 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_27 0 (4, 2)).mono (by decide +kernel)
theorem row_works_703_i1 : Template HasSnaky 5 required_703_i1 envelope_703_i1 := by
  refine compose HasSnaky 4 childrenC_703_i1 childrenD_703_i1 children_work_703_i1 (5, 3)
    required_703_i1 envelope_703_i1 pivot_mem_703_i1 child_required_sub_703_i1 child_envelope_sub_703_i1 ?_
  intro b hb
  exact common_sub_703_i1 (mem_commonEnvelope childrenD_703_i1 b hb)
def required_703_i2 : Finset Cell := ⟨(([(1, 4), (2, 4), (2, 5), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_703_i2 : Finset Cell := ⟨(([(1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (4, 3), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_703_i2 : Fin 2 → Finset Cell := ![(placed21 2 (5, 3) required_0), (placed21 4 (2, 6) required_52)]
def childrenD_703_i2 : Fin 2 → Finset Cell := ![(placed21 2 (5, 3) envelope_0), (placed21 4 (2, 6) envelope_52)]
theorem common_sub_703_i2 : commonEnvelope childrenD_703_i2 ⊆ insert (2, 3) required_703_i2 := by decide +kernel
theorem child_required_sub_703_i2 : ∀ j, childrenC_703_i2 j ⊆ insert (2, 3) required_703_i2 := by decide +kernel
theorem child_envelope_sub_703_i2 : ∀ j, childrenD_703_i2 j ⊆ envelope_703_i2 := by decide +kernel
theorem pivot_mem_703_i2 : (2, 3) ∈ envelope_703_i2 := by decide +kernel
theorem children_work_703_i2 : ∀ j, Template HasSnaky 3 (childrenC_703_i2 j) (childrenD_703_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 2 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 4 (2, 6)).mono (by decide +kernel)
theorem row_works_703_i2 : Template HasSnaky 4 required_703_i2 envelope_703_i2 := by
  refine compose HasSnaky 3 childrenC_703_i2 childrenD_703_i2 children_work_703_i2 (2, 3)
    required_703_i2 envelope_703_i2 pivot_mem_703_i2 child_required_sub_703_i2 child_envelope_sub_703_i2 ?_
  intro b hb
  exact common_sub_703_i2 (mem_commonEnvelope childrenD_703_i2 b hb)
def required_703_i3 : Finset Cell := ⟨(([(2, 4), (2, 5), (3, 3), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_703_i3 : Finset Cell := ⟨(([(2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_703_i3 : Fin 2 → Finset Cell := ![(placed21 7 (4, 6) required_0), (placed21 4 (2, 6) required_101)]
def childrenD_703_i3 : Fin 2 → Finset Cell := ![(placed21 7 (4, 6) envelope_0), (placed21 4 (2, 6) envelope_101)]
theorem common_sub_703_i3 : commonEnvelope childrenD_703_i3 ⊆ insert (3, 2) required_703_i3 := by decide +kernel
theorem child_required_sub_703_i3 : ∀ j, childrenC_703_i3 j ⊆ insert (3, 2) required_703_i3 := by decide +kernel
theorem child_envelope_sub_703_i3 : ∀ j, childrenD_703_i3 j ⊆ envelope_703_i3 := by decide +kernel
theorem pivot_mem_703_i3 : (3, 2) ∈ envelope_703_i3 := by decide +kernel
theorem children_work_703_i3 : ∀ j, Template HasSnaky 3 (childrenC_703_i3 j) (childrenD_703_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (4, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_101 4 (2, 6)).mono (by decide +kernel)
theorem row_works_703_i3 : Template HasSnaky 4 required_703_i3 envelope_703_i3 := by
  refine compose HasSnaky 3 childrenC_703_i3 childrenD_703_i3 children_work_703_i3 (3, 2)
    required_703_i3 envelope_703_i3 pivot_mem_703_i3 child_required_sub_703_i3 child_envelope_sub_703_i3 ?_
  intro b hb
  exact common_sub_703_i3 (mem_commonEnvelope childrenD_703_i3 b hb)
def required_703_i0 : Finset Cell := ⟨(([(1, 4), (2, 4), (2, 5), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_703_i0 : Finset Cell := ⟨(([(1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_703_i0 : Fin 4 → Finset Cell := ![(placed21 0 (3, 2) required_195), required_703_i1, required_703_i2, required_703_i3]
def childrenD_703_i0 : Fin 4 → Finset Cell := ![(placed21 0 (3, 2) envelope_195), envelope_703_i1, envelope_703_i2, envelope_703_i3]
theorem common_sub_703_i0 : commonEnvelope childrenD_703_i0 ⊆ insert (3, 3) required_703_i0 := by decide +kernel
theorem child_required_sub_703_i0 : ∀ j, childrenC_703_i0 j ⊆ insert (3, 3) required_703_i0 := by decide +kernel
theorem child_envelope_sub_703_i0 : ∀ j, childrenD_703_i0 j ⊆ envelope_703_i0 := by decide +kernel
theorem pivot_mem_703_i0 : (3, 3) ∈ envelope_703_i0 := by decide +kernel
theorem children_work_703_i0 : ∀ j, Template HasSnaky 5 (childrenC_703_i0 j) (childrenD_703_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_195 0 (3, 2)).mono (by decide +kernel)
  · exact row_works_703_i1.mono (by decide +kernel)
  · exact row_works_703_i2.mono (by decide +kernel)
  · exact row_works_703_i3.mono (by decide +kernel)
theorem row_works_703_i0 : Template HasSnaky 6 required_703_i0 envelope_703_i0 := by
  refine compose HasSnaky 5 childrenC_703_i0 childrenD_703_i0 children_work_703_i0 (3, 3)
    required_703_i0 envelope_703_i0 pivot_mem_703_i0 child_required_sub_703_i0 child_envelope_sub_703_i0 ?_
  intro b hb
  exact common_sub_703_i0 (mem_commonEnvelope childrenD_703_i0 b hb)
def required_703_i7 : Finset Cell := ⟨(([(2, 4), (2, 5), (3, 2), (4, 2), (4, 3), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_703_i7 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 2), (3, 3), (4, 2), (4, 3), (5, 2), (5, 3), (6, 2), (6, 3), (7, 2), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_703_i7 : Fin 3 → Finset Cell := ![(placed21 5 (6, 2) required_11), (placed21 1 (2, 2) required_103), (placed21 2 (5, 1) required_157)]
def childrenD_703_i7 : Fin 3 → Finset Cell := ![(placed21 5 (6, 2) envelope_11), (placed21 1 (2, 2) envelope_103), (placed21 2 (5, 1) envelope_157)]
theorem common_sub_703_i7 : commonEnvelope childrenD_703_i7 ⊆ insert (2, 2) required_703_i7 := by decide +kernel
theorem child_required_sub_703_i7 : ∀ j, childrenC_703_i7 j ⊆ insert (2, 2) required_703_i7 := by decide +kernel
theorem child_envelope_sub_703_i7 : ∀ j, childrenD_703_i7 j ⊆ envelope_703_i7 := by decide +kernel
theorem pivot_mem_703_i7 : (2, 2) ∈ envelope_703_i7 := by decide +kernel
theorem children_work_703_i7 : ∀ j, Template HasSnaky 3 (childrenC_703_i7 j) (childrenD_703_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 5 (6, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_103 1 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_157 2 (5, 1)).mono (by decide +kernel)
theorem row_works_703_i7 : Template HasSnaky 4 required_703_i7 envelope_703_i7 := by
  refine compose HasSnaky 3 childrenC_703_i7 childrenD_703_i7 children_work_703_i7 (2, 2)
    required_703_i7 envelope_703_i7 pivot_mem_703_i7 child_required_sub_703_i7 child_envelope_sub_703_i7 ?_
  intro b hb
  exact common_sub_703_i7 (mem_commonEnvelope childrenD_703_i7 b hb)
def required_703_i6 : Finset Cell := ⟨(([(2, 4), (2, 5), (3, 2), (4, 2), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_703_i6 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 2), (3, 3), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (6, 2), (6, 3), (7, 2), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_703_i6 : Fin 2 → Finset Cell := ![(placed21 3 (4, 5) required_5), required_703_i7]
def childrenD_703_i6 : Fin 2 → Finset Cell := ![(placed21 3 (4, 5) envelope_5), envelope_703_i7]
theorem common_sub_703_i6 : commonEnvelope childrenD_703_i6 ⊆ insert (5, 2) required_703_i6 := by decide +kernel
theorem child_required_sub_703_i6 : ∀ j, childrenC_703_i6 j ⊆ insert (5, 2) required_703_i6 := by decide +kernel
theorem child_envelope_sub_703_i6 : ∀ j, childrenD_703_i6 j ⊆ envelope_703_i6 := by decide +kernel
theorem pivot_mem_703_i6 : (5, 2) ∈ envelope_703_i6 := by decide +kernel
theorem children_work_703_i6 : ∀ j, Template HasSnaky 4 (childrenC_703_i6 j) (childrenD_703_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (4, 5)).mono (by decide +kernel)
  · exact row_works_703_i7.mono (by decide +kernel)
theorem row_works_703_i6 : Template HasSnaky 5 required_703_i6 envelope_703_i6 := by
  refine compose HasSnaky 4 childrenC_703_i6 childrenD_703_i6 children_work_703_i6 (5, 2)
    required_703_i6 envelope_703_i6 pivot_mem_703_i6 child_required_sub_703_i6 child_envelope_sub_703_i6 ?_
  intro b hb
  exact common_sub_703_i6 (mem_commonEnvelope childrenD_703_i6 b hb)
def required_703_i5 : Finset Cell := ⟨(([(2, 4), (2, 5), (4, 2), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_703_i5 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (6, 2), (6, 3), (7, 2), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_703_i5 : Fin 2 → Finset Cell := ![(placed21 7 (4, 5) required_5), required_703_i6]
def childrenD_703_i5 : Fin 2 → Finset Cell := ![(placed21 7 (4, 5) envelope_5), envelope_703_i6]
theorem common_sub_703_i5 : commonEnvelope childrenD_703_i5 ⊆ insert (3, 2) required_703_i5 := by decide +kernel
theorem child_required_sub_703_i5 : ∀ j, childrenC_703_i5 j ⊆ insert (3, 2) required_703_i5 := by decide +kernel
theorem child_envelope_sub_703_i5 : ∀ j, childrenD_703_i5 j ⊆ envelope_703_i5 := by decide +kernel
theorem pivot_mem_703_i5 : (3, 2) ∈ envelope_703_i5 := by decide +kernel
theorem children_work_703_i5 : ∀ j, Template HasSnaky 5 (childrenC_703_i5 j) (childrenD_703_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (4, 5)).mono (by decide +kernel)
  · exact row_works_703_i6.mono (by decide +kernel)
theorem row_works_703_i5 : Template HasSnaky 6 required_703_i5 envelope_703_i5 := by
  refine compose HasSnaky 5 childrenC_703_i5 childrenD_703_i5 children_work_703_i5 (3, 2)
    required_703_i5 envelope_703_i5 pivot_mem_703_i5 child_required_sub_703_i5 child_envelope_sub_703_i5 ?_
  intro b hb
  exact common_sub_703_i5 (mem_commonEnvelope childrenD_703_i5 b hb)
def required_703_i4 : Finset Cell := ⟨(([(2, 4), (2, 5), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_703_i4 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 2), (6, 3), (7, 2), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_703_i4 : Fin 3 → Finset Cell := ![(placed21 4 (4, 6) required_7), (placed21 6 (5, 6) required_9), required_703_i5]
def childrenD_703_i4 : Fin 3 → Finset Cell := ![(placed21 4 (4, 6) envelope_7), (placed21 6 (5, 6) envelope_9), envelope_703_i5]
theorem common_sub_703_i4 : commonEnvelope childrenD_703_i4 ⊆ insert (4, 2) required_703_i4 := by decide +kernel
theorem child_required_sub_703_i4 : ∀ j, childrenC_703_i4 j ⊆ insert (4, 2) required_703_i4 := by decide +kernel
theorem child_envelope_sub_703_i4 : ∀ j, childrenD_703_i4 j ⊆ envelope_703_i4 := by decide +kernel
theorem pivot_mem_703_i4 : (4, 2) ∈ envelope_703_i4 := by decide +kernel
theorem children_work_703_i4 : ∀ j, Template HasSnaky 6 (childrenC_703_i4 j) (childrenD_703_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 4 (4, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 6 (5, 6)).mono (by decide +kernel)
  · exact row_works_703_i5.mono (by decide +kernel)
theorem row_works_703_i4 : Template HasSnaky 7 required_703_i4 envelope_703_i4 := by
  refine compose HasSnaky 6 childrenC_703_i4 childrenD_703_i4 children_work_703_i4 (4, 2)
    required_703_i4 envelope_703_i4 pivot_mem_703_i4 child_required_sub_703_i4 child_envelope_sub_703_i4 ?_
  intro b hb
  exact common_sub_703_i4 (mem_commonEnvelope childrenD_703_i4 b hb)
def required_703_i9 : Finset Cell := ⟨(([(1, 4), (2, 4), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_703_i9 : Finset Cell := ⟨(([(1, 4), (2, 3), (2, 4), (3, 2), (3, 3), (3, 7), (3, 8), (3, 9), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 3), (5, 4), (5, 7), (5, 8), (5, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_703_i9 : Fin 2 → Finset Cell := ![(placed21 2 (5, 3) required_18), (placed21 2 (5, 2) required_77)]
def childrenD_703_i9 : Fin 2 → Finset Cell := ![(placed21 2 (5, 3) envelope_18), (placed21 2 (5, 2) envelope_77)]
theorem common_sub_703_i9 : commonEnvelope childrenD_703_i9 ⊆ insert (5, 3) required_703_i9 := by decide +kernel
theorem child_required_sub_703_i9 : ∀ j, childrenC_703_i9 j ⊆ insert (5, 3) required_703_i9 := by decide +kernel
theorem child_envelope_sub_703_i9 : ∀ j, childrenD_703_i9 j ⊆ envelope_703_i9 := by decide +kernel
theorem pivot_mem_703_i9 : (5, 3) ∈ envelope_703_i9 := by decide +kernel
theorem children_work_703_i9 : ∀ j, Template HasSnaky 4 (childrenC_703_i9 j) (childrenD_703_i9 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_18 2 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_77 2 (5, 2)).mono (by decide +kernel)
theorem row_works_703_i9 : Template HasSnaky 5 required_703_i9 envelope_703_i9 := by
  refine compose HasSnaky 4 childrenC_703_i9 childrenD_703_i9 children_work_703_i9 (5, 3)
    required_703_i9 envelope_703_i9 pivot_mem_703_i9 child_required_sub_703_i9 child_envelope_sub_703_i9 ?_
  intro b hb
  exact common_sub_703_i9 (mem_commonEnvelope childrenD_703_i9 b hb)
def required_703_i8 : Finset Cell := ⟨(([(1, 4), (2, 4), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_703_i8 : Finset Cell := ⟨(([(1, 4), (2, 3), (2, 4), (3, 1), (3, 2), (3, 3), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_703_i8 : Fin 4 → Finset Cell := ![(placed21 6 (5, 7) required_9), (placed21 5 (5, 3) required_49), (placed21 0 (3, 1) required_186), required_703_i9]
def childrenD_703_i8 : Fin 4 → Finset Cell := ![(placed21 6 (5, 7) envelope_9), (placed21 5 (5, 3) envelope_49), (placed21 0 (3, 1) envelope_186), envelope_703_i9]
theorem common_sub_703_i8 : commonEnvelope childrenD_703_i8 ⊆ insert (4, 6) required_703_i8 := by decide +kernel
theorem child_required_sub_703_i8 : ∀ j, childrenC_703_i8 j ⊆ insert (4, 6) required_703_i8 := by decide +kernel
theorem child_envelope_sub_703_i8 : ∀ j, childrenD_703_i8 j ⊆ envelope_703_i8 := by decide +kernel
theorem pivot_mem_703_i8 : (4, 6) ∈ envelope_703_i8 := by decide +kernel
theorem children_work_703_i8 : ∀ j, Template HasSnaky 5 (childrenC_703_i8 j) (childrenD_703_i8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_9 6 (5, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_49 5 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_186 0 (3, 1)).mono (by decide +kernel)
  · exact row_works_703_i9.mono (by decide +kernel)
theorem row_works_703_i8 : Template HasSnaky 6 required_703_i8 envelope_703_i8 := by
  refine compose HasSnaky 5 childrenC_703_i8 childrenD_703_i8 children_work_703_i8 (4, 6)
    required_703_i8 envelope_703_i8 pivot_mem_703_i8 child_required_sub_703_i8 child_envelope_sub_703_i8 ?_
  intro b hb
  exact common_sub_703_i8 (mem_commonEnvelope childrenD_703_i8 b hb)
def required_703 : Finset Cell := ⟨(([(1, 4), (1, 5), (2, 4), (2, 5), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_703 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 2), (6, 3), (7, 2), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_703 : Fin 6 → Finset Cell := ![(placed21 6 (5, 7) required_13), (placed21 2 (5, 0) required_369), required_703_i0, (placed21 4 (1, 6) required_516), required_703_i4, required_703_i8]
def childrenD_703 : Fin 6 → Finset Cell := ![(placed21 6 (5, 7) envelope_13), (placed21 2 (5, 0) envelope_369), envelope_703_i0, (placed21 4 (1, 6) envelope_516), envelope_703_i4, envelope_703_i8]
theorem common_sub_703 : commonEnvelope childrenD_703 ⊆ insert (4, 3) required_703 := by decide +kernel
theorem child_required_sub_703 : ∀ j, childrenC_703 j ⊆ insert (4, 3) required_703 := by decide +kernel
theorem child_envelope_sub_703 : ∀ j, childrenD_703 j ⊆ envelope_703 := by decide +kernel
theorem pivot_mem_703 : (4, 3) ∈ envelope_703 := by decide +kernel
theorem children_work_703 : ∀ j, Template HasSnaky 7 (childrenC_703 j) (childrenD_703 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 6 (5, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_369 2 (5, 0)).mono (by decide +kernel)
  · exact row_works_703_i0.mono (by decide +kernel)
  · exact (placed21_template row_works_516 4 (1, 6)).mono (by decide +kernel)
  · exact row_works_703_i4.mono (by decide +kernel)
  · exact row_works_703_i8.mono (by decide +kernel)
theorem row_works_703 : Template HasSnaky 8 required_703 envelope_703 := by
  refine compose HasSnaky 7 childrenC_703 childrenD_703 children_work_703 (4, 3)
    required_703 envelope_703 pivot_mem_703 child_required_sub_703 child_envelope_sub_703 ?_
  intro b hb
  exact common_sub_703 (mem_commonEnvelope childrenD_703 b hb)
def height_658_i0 : ℕ := 7
def childrenH_658_i0 : Fin 2 → ℕ := ![height_314, height_378]
theorem height_exact_658_i0 : height_658_i0 = 1 + Finset.univ.sup childrenH_658_i0 := by decide +kernel
theorem required_origin_658_i0 : ∀ x ∈ required_658_i0,
    (∃ j, x ∈ childrenC_658_i0 j) ∨ ∀ j, x ∈ childrenD_658_i0 j := by decide +kernel
theorem required_exact_658_i0 : required_658_i0 =
    ((Finset.univ.biUnion childrenC_658_i0) ∪ commonEnvelope childrenD_658_i0).erase (2, 6) := by
  exact required_eq_combination childrenC_658_i0 childrenD_658_i0 (2, 6) required_658_i0
    (by decide +kernel) child_required_sub_658_i0 common_sub_658_i0 required_origin_658_i0
theorem envelope_origin_658_i0 : ∀ x ∈ envelope_658_i0,
    x = (2, 6) ∨ ∃ j, x ∈ childrenD_658_i0 j := by decide +kernel
theorem envelope_exact_658_i0 : envelope_658_i0 =
    insert (2, 6) (Finset.univ.biUnion childrenD_658_i0) := by
  exact envelope_eq_combination childrenD_658_i0 (2, 6) envelope_658_i0
    pivot_mem_658_i0 child_envelope_sub_658_i0 envelope_origin_658_i0
def checked_658_i0 : CheckedCard where
  required := required_658_i0
  envelope := envelope_658_i0
  height := height_658_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_658_i0
def height_658 : ℕ := 8
def childrenH_658 : Fin 4 → ℕ := ![height_27, height_52, height_284, height_658_i0]
theorem height_exact_658 : height_658 = 1 + Finset.univ.sup childrenH_658 := by decide +kernel
theorem required_origin_658 : ∀ x ∈ required_658,
    (∃ j, x ∈ childrenC_658 j) ∨ ∀ j, x ∈ childrenD_658 j := by decide +kernel
theorem required_exact_658 : required_658 =
    ((Finset.univ.biUnion childrenC_658) ∪ commonEnvelope childrenD_658).erase (2, 3) := by
  exact required_eq_combination childrenC_658 childrenD_658 (2, 3) required_658
    (by decide +kernel) child_required_sub_658 common_sub_658 required_origin_658
theorem envelope_origin_658 : ∀ x ∈ envelope_658,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_658 j := by decide +kernel
theorem envelope_exact_658 : envelope_658 =
    insert (2, 3) (Finset.univ.biUnion childrenD_658) := by
  exact envelope_eq_combination childrenD_658 (2, 3) envelope_658
    pivot_mem_658 child_envelope_sub_658 envelope_origin_658
def checked_658 : CheckedCard where
  required := required_658
  envelope := envelope_658
  height := height_658
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_658
def height_661_i0 : ℕ := 7
def childrenH_661_i0 : Fin 4 → ℕ := ![height_9, height_115, height_302, height_303]
theorem height_exact_661_i0 : height_661_i0 = 1 + Finset.univ.sup childrenH_661_i0 := by decide +kernel
theorem required_origin_661_i0 : ∀ x ∈ required_661_i0,
    (∃ j, x ∈ childrenC_661_i0 j) ∨ ∀ j, x ∈ childrenD_661_i0 j := by decide +kernel
theorem required_exact_661_i0 : required_661_i0 =
    ((Finset.univ.biUnion childrenC_661_i0) ∪ commonEnvelope childrenD_661_i0).erase (4, 3) := by
  exact required_eq_combination childrenC_661_i0 childrenD_661_i0 (4, 3) required_661_i0
    (by decide +kernel) child_required_sub_661_i0 common_sub_661_i0 required_origin_661_i0
theorem envelope_origin_661_i0 : ∀ x ∈ envelope_661_i0,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_661_i0 j := by decide +kernel
theorem envelope_exact_661_i0 : envelope_661_i0 =
    insert (4, 3) (Finset.univ.biUnion childrenD_661_i0) := by
  exact envelope_eq_combination childrenD_661_i0 (4, 3) envelope_661_i0
    pivot_mem_661_i0 child_envelope_sub_661_i0 envelope_origin_661_i0
def checked_661_i0 : CheckedCard where
  required := required_661_i0
  envelope := envelope_661_i0
  height := height_661_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_661_i0
def height_661 : ℕ := 8
def childrenH_661 : Fin 5 → ℕ := ![height_13, height_14, height_33, height_116, height_661_i0]
theorem height_exact_661 : height_661 = 1 + Finset.univ.sup childrenH_661 := by decide +kernel
theorem required_origin_661 : ∀ x ∈ required_661,
    (∃ j, x ∈ childrenC_661 j) ∨ ∀ j, x ∈ childrenD_661 j := by decide +kernel
theorem required_exact_661 : required_661 =
    ((Finset.univ.biUnion childrenC_661) ∪ commonEnvelope childrenD_661).erase (4, 6) := by
  exact required_eq_combination childrenC_661 childrenD_661 (4, 6) required_661
    (by decide +kernel) child_required_sub_661 common_sub_661 required_origin_661
theorem envelope_origin_661 : ∀ x ∈ envelope_661,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_661 j := by decide +kernel
theorem envelope_exact_661 : envelope_661 =
    insert (4, 6) (Finset.univ.biUnion childrenD_661) := by
  exact envelope_eq_combination childrenD_661 (4, 6) envelope_661
    pivot_mem_661 child_envelope_sub_661 envelope_origin_661
def checked_661 : CheckedCard where
  required := required_661
  envelope := envelope_661
  height := height_661
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_661
def height_666_i1 : ℕ := 6
def childrenH_666_i1 : Fin 2 → ℕ := ![height_4, height_314]
theorem height_exact_666_i1 : height_666_i1 = 1 + Finset.univ.sup childrenH_666_i1 := by decide +kernel
theorem required_origin_666_i1 : ∀ x ∈ required_666_i1,
    (∃ j, x ∈ childrenC_666_i1 j) ∨ ∀ j, x ∈ childrenD_666_i1 j := by decide +kernel
theorem required_exact_666_i1 : required_666_i1 =
    ((Finset.univ.biUnion childrenC_666_i1) ∪ commonEnvelope childrenD_666_i1).erase (1, 3) := by
  exact required_eq_combination childrenC_666_i1 childrenD_666_i1 (1, 3) required_666_i1
    (by decide +kernel) child_required_sub_666_i1 common_sub_666_i1 required_origin_666_i1
theorem envelope_origin_666_i1 : ∀ x ∈ envelope_666_i1,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_666_i1 j := by decide +kernel
theorem envelope_exact_666_i1 : envelope_666_i1 =
    insert (1, 3) (Finset.univ.biUnion childrenD_666_i1) := by
  exact envelope_eq_combination childrenD_666_i1 (1, 3) envelope_666_i1
    pivot_mem_666_i1 child_envelope_sub_666_i1 envelope_origin_666_i1
def checked_666_i1 : CheckedCard where
  required := required_666_i1
  envelope := envelope_666_i1
  height := height_666_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_666_i1
def height_666_i0 : ℕ := 7
def childrenH_666_i0 : Fin 2 → ℕ := ![height_5, height_666_i1]
theorem height_exact_666_i0 : height_666_i0 = 1 + Finset.univ.sup childrenH_666_i0 := by decide +kernel
theorem required_origin_666_i0 : ∀ x ∈ required_666_i0,
    (∃ j, x ∈ childrenC_666_i0 j) ∨ ∀ j, x ∈ childrenD_666_i0 j := by decide +kernel
theorem required_exact_666_i0 : required_666_i0 =
    ((Finset.univ.biUnion childrenC_666_i0) ∪ commonEnvelope childrenD_666_i0).erase (4, 3) := by
  exact required_eq_combination childrenC_666_i0 childrenD_666_i0 (4, 3) required_666_i0
    (by decide +kernel) child_required_sub_666_i0 common_sub_666_i0 required_origin_666_i0
theorem envelope_origin_666_i0 : ∀ x ∈ envelope_666_i0,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_666_i0 j := by decide +kernel
theorem envelope_exact_666_i0 : envelope_666_i0 =
    insert (4, 3) (Finset.univ.biUnion childrenD_666_i0) := by
  exact envelope_eq_combination childrenD_666_i0 (4, 3) envelope_666_i0
    pivot_mem_666_i0 child_envelope_sub_666_i0 envelope_origin_666_i0
def checked_666_i0 : CheckedCard where
  required := required_666_i0
  envelope := envelope_666_i0
  height := height_666_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_666_i0
def height_666 : ℕ := 8
def childrenH_666 : Fin 2 → ℕ := ![height_5, height_666_i0]
theorem height_exact_666 : height_666 = 1 + Finset.univ.sup childrenH_666 := by decide +kernel
theorem required_origin_666 : ∀ x ∈ required_666,
    (∃ j, x ∈ childrenC_666 j) ∨ ∀ j, x ∈ childrenD_666 j := by decide +kernel
theorem required_exact_666 : required_666 =
    ((Finset.univ.biUnion childrenC_666) ∪ commonEnvelope childrenD_666).erase (2, 3) := by
  exact required_eq_combination childrenC_666 childrenD_666 (2, 3) required_666
    (by decide +kernel) child_required_sub_666 common_sub_666 required_origin_666
theorem envelope_origin_666 : ∀ x ∈ envelope_666,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_666 j := by decide +kernel
theorem envelope_exact_666 : envelope_666 =
    insert (2, 3) (Finset.univ.biUnion childrenD_666) := by
  exact envelope_eq_combination childrenD_666 (2, 3) envelope_666
    pivot_mem_666 child_envelope_sub_666 envelope_origin_666
def checked_666 : CheckedCard where
  required := required_666
  envelope := envelope_666
  height := height_666
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_666
def height_678_i1 : ℕ := 6
def childrenH_678_i1 : Fin 2 → ℕ := ![height_22, height_382]
theorem height_exact_678_i1 : height_678_i1 = 1 + Finset.univ.sup childrenH_678_i1 := by decide +kernel
theorem required_origin_678_i1 : ∀ x ∈ required_678_i1,
    (∃ j, x ∈ childrenC_678_i1 j) ∨ ∀ j, x ∈ childrenD_678_i1 j := by decide +kernel
theorem required_exact_678_i1 : required_678_i1 =
    ((Finset.univ.biUnion childrenC_678_i1) ∪ commonEnvelope childrenD_678_i1).erase (4, 3) := by
  exact required_eq_combination childrenC_678_i1 childrenD_678_i1 (4, 3) required_678_i1
    (by decide +kernel) child_required_sub_678_i1 common_sub_678_i1 required_origin_678_i1
theorem envelope_origin_678_i1 : ∀ x ∈ envelope_678_i1,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_678_i1 j := by decide +kernel
theorem envelope_exact_678_i1 : envelope_678_i1 =
    insert (4, 3) (Finset.univ.biUnion childrenD_678_i1) := by
  exact envelope_eq_combination childrenD_678_i1 (4, 3) envelope_678_i1
    pivot_mem_678_i1 child_envelope_sub_678_i1 envelope_origin_678_i1
def checked_678_i1 : CheckedCard where
  required := required_678_i1
  envelope := envelope_678_i1
  height := height_678_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_678_i1
def height_678_i0 : ℕ := 7
def childrenH_678_i0 : Fin 2 → ℕ := ![height_18, height_678_i1]
theorem height_exact_678_i0 : height_678_i0 = 1 + Finset.univ.sup childrenH_678_i0 := by decide +kernel
theorem required_origin_678_i0 : ∀ x ∈ required_678_i0,
    (∃ j, x ∈ childrenC_678_i0 j) ∨ ∀ j, x ∈ childrenD_678_i0 j := by decide +kernel
theorem required_exact_678_i0 : required_678_i0 =
    ((Finset.univ.biUnion childrenC_678_i0) ∪ commonEnvelope childrenD_678_i0).erase (2, 6) := by
  exact required_eq_combination childrenC_678_i0 childrenD_678_i0 (2, 6) required_678_i0
    (by decide +kernel) child_required_sub_678_i0 common_sub_678_i0 required_origin_678_i0
theorem envelope_origin_678_i0 : ∀ x ∈ envelope_678_i0,
    x = (2, 6) ∨ ∃ j, x ∈ childrenD_678_i0 j := by decide +kernel
theorem envelope_exact_678_i0 : envelope_678_i0 =
    insert (2, 6) (Finset.univ.biUnion childrenD_678_i0) := by
  exact envelope_eq_combination childrenD_678_i0 (2, 6) envelope_678_i0
    pivot_mem_678_i0 child_envelope_sub_678_i0 envelope_origin_678_i0
def checked_678_i0 : CheckedCard where
  required := required_678_i0
  envelope := envelope_678_i0
  height := height_678_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_678_i0
def height_678 : ℕ := 8
def childrenH_678 : Fin 3 → ℕ := ![height_31, height_160, height_678_i0]
theorem height_exact_678 : height_678 = 1 + Finset.univ.sup childrenH_678 := by decide +kernel
theorem required_origin_678 : ∀ x ∈ required_678,
    (∃ j, x ∈ childrenC_678 j) ∨ ∀ j, x ∈ childrenD_678 j := by decide +kernel
theorem required_exact_678 : required_678 =
    ((Finset.univ.biUnion childrenC_678) ∪ commonEnvelope childrenD_678).erase (1, 5) := by
  exact required_eq_combination childrenC_678 childrenD_678 (1, 5) required_678
    (by decide +kernel) child_required_sub_678 common_sub_678 required_origin_678
theorem envelope_origin_678 : ∀ x ∈ envelope_678,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_678 j := by decide +kernel
theorem envelope_exact_678 : envelope_678 =
    insert (1, 5) (Finset.univ.biUnion childrenD_678) := by
  exact envelope_eq_combination childrenD_678 (1, 5) envelope_678
    pivot_mem_678 child_envelope_sub_678 envelope_origin_678
def checked_678 : CheckedCard where
  required := required_678
  envelope := envelope_678
  height := height_678
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_678
def height_703_i1 : ℕ := 5
def childrenH_703_i1 : Fin 2 → ℕ := ![height_3, height_27]
theorem height_exact_703_i1 : height_703_i1 = 1 + Finset.univ.sup childrenH_703_i1 := by decide +kernel
theorem required_origin_703_i1 : ∀ x ∈ required_703_i1,
    (∃ j, x ∈ childrenC_703_i1 j) ∨ ∀ j, x ∈ childrenD_703_i1 j := by decide +kernel
theorem required_exact_703_i1 : required_703_i1 =
    ((Finset.univ.biUnion childrenC_703_i1) ∪ commonEnvelope childrenD_703_i1).erase (5, 3) := by
  exact required_eq_combination childrenC_703_i1 childrenD_703_i1 (5, 3) required_703_i1
    (by decide +kernel) child_required_sub_703_i1 common_sub_703_i1 required_origin_703_i1
theorem envelope_origin_703_i1 : ∀ x ∈ envelope_703_i1,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_703_i1 j := by decide +kernel
theorem envelope_exact_703_i1 : envelope_703_i1 =
    insert (5, 3) (Finset.univ.biUnion childrenD_703_i1) := by
  exact envelope_eq_combination childrenD_703_i1 (5, 3) envelope_703_i1
    pivot_mem_703_i1 child_envelope_sub_703_i1 envelope_origin_703_i1
def checked_703_i1 : CheckedCard where
  required := required_703_i1
  envelope := envelope_703_i1
  height := height_703_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_703_i1
def height_703_i2 : ℕ := 4
def childrenH_703_i2 : Fin 2 → ℕ := ![height_0, height_52]
theorem height_exact_703_i2 : height_703_i2 = 1 + Finset.univ.sup childrenH_703_i2 := by decide +kernel
theorem required_origin_703_i2 : ∀ x ∈ required_703_i2,
    (∃ j, x ∈ childrenC_703_i2 j) ∨ ∀ j, x ∈ childrenD_703_i2 j := by decide +kernel
theorem required_exact_703_i2 : required_703_i2 =
    ((Finset.univ.biUnion childrenC_703_i2) ∪ commonEnvelope childrenD_703_i2).erase (2, 3) := by
  exact required_eq_combination childrenC_703_i2 childrenD_703_i2 (2, 3) required_703_i2
    (by decide +kernel) child_required_sub_703_i2 common_sub_703_i2 required_origin_703_i2
theorem envelope_origin_703_i2 : ∀ x ∈ envelope_703_i2,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_703_i2 j := by decide +kernel
theorem envelope_exact_703_i2 : envelope_703_i2 =
    insert (2, 3) (Finset.univ.biUnion childrenD_703_i2) := by
  exact envelope_eq_combination childrenD_703_i2 (2, 3) envelope_703_i2
    pivot_mem_703_i2 child_envelope_sub_703_i2 envelope_origin_703_i2
def checked_703_i2 : CheckedCard where
  required := required_703_i2
  envelope := envelope_703_i2
  height := height_703_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_703_i2
def height_703_i3 : ℕ := 4
def childrenH_703_i3 : Fin 2 → ℕ := ![height_0, height_101]
theorem height_exact_703_i3 : height_703_i3 = 1 + Finset.univ.sup childrenH_703_i3 := by decide +kernel
theorem required_origin_703_i3 : ∀ x ∈ required_703_i3,
    (∃ j, x ∈ childrenC_703_i3 j) ∨ ∀ j, x ∈ childrenD_703_i3 j := by decide +kernel
theorem required_exact_703_i3 : required_703_i3 =
    ((Finset.univ.biUnion childrenC_703_i3) ∪ commonEnvelope childrenD_703_i3).erase (3, 2) := by
  exact required_eq_combination childrenC_703_i3 childrenD_703_i3 (3, 2) required_703_i3
    (by decide +kernel) child_required_sub_703_i3 common_sub_703_i3 required_origin_703_i3
theorem envelope_origin_703_i3 : ∀ x ∈ envelope_703_i3,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_703_i3 j := by decide +kernel
theorem envelope_exact_703_i3 : envelope_703_i3 =
    insert (3, 2) (Finset.univ.biUnion childrenD_703_i3) := by
  exact envelope_eq_combination childrenD_703_i3 (3, 2) envelope_703_i3
    pivot_mem_703_i3 child_envelope_sub_703_i3 envelope_origin_703_i3
def checked_703_i3 : CheckedCard where
  required := required_703_i3
  envelope := envelope_703_i3
  height := height_703_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_703_i3
def height_703_i0 : ℕ := 6
def childrenH_703_i0 : Fin 4 → ℕ := ![height_195, height_703_i1, height_703_i2, height_703_i3]
theorem height_exact_703_i0 : height_703_i0 = 1 + Finset.univ.sup childrenH_703_i0 := by decide +kernel
theorem required_origin_703_i0 : ∀ x ∈ required_703_i0,
    (∃ j, x ∈ childrenC_703_i0 j) ∨ ∀ j, x ∈ childrenD_703_i0 j := by decide +kernel
theorem required_exact_703_i0 : required_703_i0 =
    ((Finset.univ.biUnion childrenC_703_i0) ∪ commonEnvelope childrenD_703_i0).erase (3, 3) := by
  exact required_eq_combination childrenC_703_i0 childrenD_703_i0 (3, 3) required_703_i0
    (by decide +kernel) child_required_sub_703_i0 common_sub_703_i0 required_origin_703_i0
theorem envelope_origin_703_i0 : ∀ x ∈ envelope_703_i0,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_703_i0 j := by decide +kernel
theorem envelope_exact_703_i0 : envelope_703_i0 =
    insert (3, 3) (Finset.univ.biUnion childrenD_703_i0) := by
  exact envelope_eq_combination childrenD_703_i0 (3, 3) envelope_703_i0
    pivot_mem_703_i0 child_envelope_sub_703_i0 envelope_origin_703_i0
def checked_703_i0 : CheckedCard where
  required := required_703_i0
  envelope := envelope_703_i0
  height := height_703_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_703_i0
def height_703_i7 : ℕ := 4
def childrenH_703_i7 : Fin 3 → ℕ := ![height_11, height_103, height_157]
theorem height_exact_703_i7 : height_703_i7 = 1 + Finset.univ.sup childrenH_703_i7 := by decide +kernel
theorem required_origin_703_i7 : ∀ x ∈ required_703_i7,
    (∃ j, x ∈ childrenC_703_i7 j) ∨ ∀ j, x ∈ childrenD_703_i7 j := by decide +kernel
theorem required_exact_703_i7 : required_703_i7 =
    ((Finset.univ.biUnion childrenC_703_i7) ∪ commonEnvelope childrenD_703_i7).erase (2, 2) := by
  exact required_eq_combination childrenC_703_i7 childrenD_703_i7 (2, 2) required_703_i7
    (by decide +kernel) child_required_sub_703_i7 common_sub_703_i7 required_origin_703_i7
theorem envelope_origin_703_i7 : ∀ x ∈ envelope_703_i7,
    x = (2, 2) ∨ ∃ j, x ∈ childrenD_703_i7 j := by decide +kernel
theorem envelope_exact_703_i7 : envelope_703_i7 =
    insert (2, 2) (Finset.univ.biUnion childrenD_703_i7) := by
  exact envelope_eq_combination childrenD_703_i7 (2, 2) envelope_703_i7
    pivot_mem_703_i7 child_envelope_sub_703_i7 envelope_origin_703_i7
def checked_703_i7 : CheckedCard where
  required := required_703_i7
  envelope := envelope_703_i7
  height := height_703_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_703_i7
def height_703_i6 : ℕ := 5
def childrenH_703_i6 : Fin 2 → ℕ := ![height_5, height_703_i7]
theorem height_exact_703_i6 : height_703_i6 = 1 + Finset.univ.sup childrenH_703_i6 := by decide +kernel
theorem required_origin_703_i6 : ∀ x ∈ required_703_i6,
    (∃ j, x ∈ childrenC_703_i6 j) ∨ ∀ j, x ∈ childrenD_703_i6 j := by decide +kernel
theorem required_exact_703_i6 : required_703_i6 =
    ((Finset.univ.biUnion childrenC_703_i6) ∪ commonEnvelope childrenD_703_i6).erase (5, 2) := by
  exact required_eq_combination childrenC_703_i6 childrenD_703_i6 (5, 2) required_703_i6
    (by decide +kernel) child_required_sub_703_i6 common_sub_703_i6 required_origin_703_i6
theorem envelope_origin_703_i6 : ∀ x ∈ envelope_703_i6,
    x = (5, 2) ∨ ∃ j, x ∈ childrenD_703_i6 j := by decide +kernel
theorem envelope_exact_703_i6 : envelope_703_i6 =
    insert (5, 2) (Finset.univ.biUnion childrenD_703_i6) := by
  exact envelope_eq_combination childrenD_703_i6 (5, 2) envelope_703_i6
    pivot_mem_703_i6 child_envelope_sub_703_i6 envelope_origin_703_i6
def checked_703_i6 : CheckedCard where
  required := required_703_i6
  envelope := envelope_703_i6
  height := height_703_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_703_i6
def height_703_i5 : ℕ := 6
def childrenH_703_i5 : Fin 2 → ℕ := ![height_5, height_703_i6]
theorem height_exact_703_i5 : height_703_i5 = 1 + Finset.univ.sup childrenH_703_i5 := by decide +kernel
theorem required_origin_703_i5 : ∀ x ∈ required_703_i5,
    (∃ j, x ∈ childrenC_703_i5 j) ∨ ∀ j, x ∈ childrenD_703_i5 j := by decide +kernel
theorem required_exact_703_i5 : required_703_i5 =
    ((Finset.univ.biUnion childrenC_703_i5) ∪ commonEnvelope childrenD_703_i5).erase (3, 2) := by
  exact required_eq_combination childrenC_703_i5 childrenD_703_i5 (3, 2) required_703_i5
    (by decide +kernel) child_required_sub_703_i5 common_sub_703_i5 required_origin_703_i5
theorem envelope_origin_703_i5 : ∀ x ∈ envelope_703_i5,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_703_i5 j := by decide +kernel
theorem envelope_exact_703_i5 : envelope_703_i5 =
    insert (3, 2) (Finset.univ.biUnion childrenD_703_i5) := by
  exact envelope_eq_combination childrenD_703_i5 (3, 2) envelope_703_i5
    pivot_mem_703_i5 child_envelope_sub_703_i5 envelope_origin_703_i5
def checked_703_i5 : CheckedCard where
  required := required_703_i5
  envelope := envelope_703_i5
  height := height_703_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_703_i5
def height_703_i4 : ℕ := 7
def childrenH_703_i4 : Fin 3 → ℕ := ![height_7, height_9, height_703_i5]
theorem height_exact_703_i4 : height_703_i4 = 1 + Finset.univ.sup childrenH_703_i4 := by decide +kernel
theorem required_origin_703_i4 : ∀ x ∈ required_703_i4,
    (∃ j, x ∈ childrenC_703_i4 j) ∨ ∀ j, x ∈ childrenD_703_i4 j := by decide +kernel
theorem required_exact_703_i4 : required_703_i4 =
    ((Finset.univ.biUnion childrenC_703_i4) ∪ commonEnvelope childrenD_703_i4).erase (4, 2) := by
  exact required_eq_combination childrenC_703_i4 childrenD_703_i4 (4, 2) required_703_i4
    (by decide +kernel) child_required_sub_703_i4 common_sub_703_i4 required_origin_703_i4
theorem envelope_origin_703_i4 : ∀ x ∈ envelope_703_i4,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_703_i4 j := by decide +kernel
theorem envelope_exact_703_i4 : envelope_703_i4 =
    insert (4, 2) (Finset.univ.biUnion childrenD_703_i4) := by
  exact envelope_eq_combination childrenD_703_i4 (4, 2) envelope_703_i4
    pivot_mem_703_i4 child_envelope_sub_703_i4 envelope_origin_703_i4
def checked_703_i4 : CheckedCard where
  required := required_703_i4
  envelope := envelope_703_i4
  height := height_703_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_703_i4
def height_703_i9 : ℕ := 5
def childrenH_703_i9 : Fin 2 → ℕ := ![height_18, height_77]
theorem height_exact_703_i9 : height_703_i9 = 1 + Finset.univ.sup childrenH_703_i9 := by decide +kernel
theorem required_origin_703_i9 : ∀ x ∈ required_703_i9,
    (∃ j, x ∈ childrenC_703_i9 j) ∨ ∀ j, x ∈ childrenD_703_i9 j := by decide +kernel
theorem required_exact_703_i9 : required_703_i9 =
    ((Finset.univ.biUnion childrenC_703_i9) ∪ commonEnvelope childrenD_703_i9).erase (5, 3) := by
  exact required_eq_combination childrenC_703_i9 childrenD_703_i9 (5, 3) required_703_i9
    (by decide +kernel) child_required_sub_703_i9 common_sub_703_i9 required_origin_703_i9
theorem envelope_origin_703_i9 : ∀ x ∈ envelope_703_i9,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_703_i9 j := by decide +kernel
theorem envelope_exact_703_i9 : envelope_703_i9 =
    insert (5, 3) (Finset.univ.biUnion childrenD_703_i9) := by
  exact envelope_eq_combination childrenD_703_i9 (5, 3) envelope_703_i9
    pivot_mem_703_i9 child_envelope_sub_703_i9 envelope_origin_703_i9
def checked_703_i9 : CheckedCard where
  required := required_703_i9
  envelope := envelope_703_i9
  height := height_703_i9
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_703_i9
def height_703_i8 : ℕ := 6
def childrenH_703_i8 : Fin 4 → ℕ := ![height_9, height_49, height_186, height_703_i9]
theorem height_exact_703_i8 : height_703_i8 = 1 + Finset.univ.sup childrenH_703_i8 := by decide +kernel
theorem required_origin_703_i8 : ∀ x ∈ required_703_i8,
    (∃ j, x ∈ childrenC_703_i8 j) ∨ ∀ j, x ∈ childrenD_703_i8 j := by decide +kernel
theorem required_exact_703_i8 : required_703_i8 =
    ((Finset.univ.biUnion childrenC_703_i8) ∪ commonEnvelope childrenD_703_i8).erase (4, 6) := by
  exact required_eq_combination childrenC_703_i8 childrenD_703_i8 (4, 6) required_703_i8
    (by decide +kernel) child_required_sub_703_i8 common_sub_703_i8 required_origin_703_i8
theorem envelope_origin_703_i8 : ∀ x ∈ envelope_703_i8,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_703_i8 j := by decide +kernel
theorem envelope_exact_703_i8 : envelope_703_i8 =
    insert (4, 6) (Finset.univ.biUnion childrenD_703_i8) := by
  exact envelope_eq_combination childrenD_703_i8 (4, 6) envelope_703_i8
    pivot_mem_703_i8 child_envelope_sub_703_i8 envelope_origin_703_i8
def checked_703_i8 : CheckedCard where
  required := required_703_i8
  envelope := envelope_703_i8
  height := height_703_i8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_703_i8
def height_703 : ℕ := 8
def childrenH_703 : Fin 6 → ℕ := ![height_13, height_369, height_703_i0, height_516, height_703_i4, height_703_i8]
theorem height_exact_703 : height_703 = 1 + Finset.univ.sup childrenH_703 := by decide +kernel
theorem required_origin_703 : ∀ x ∈ required_703,
    (∃ j, x ∈ childrenC_703 j) ∨ ∀ j, x ∈ childrenD_703 j := by decide +kernel
theorem required_exact_703 : required_703 =
    ((Finset.univ.biUnion childrenC_703) ∪ commonEnvelope childrenD_703).erase (4, 3) := by
  exact required_eq_combination childrenC_703 childrenD_703 (4, 3) required_703
    (by decide +kernel) child_required_sub_703 common_sub_703 required_origin_703
theorem envelope_origin_703 : ∀ x ∈ envelope_703,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_703 j := by decide +kernel
theorem envelope_exact_703 : envelope_703 =
    insert (4, 3) (Finset.univ.biUnion childrenD_703) := by
  exact envelope_eq_combination childrenD_703 (4, 3) envelope_703
    pivot_mem_703 child_envelope_sub_703 envelope_origin_703
def checked_703 : CheckedCard where
  required := required_703
  envelope := envelope_703
  height := height_703
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_703
end SnakyPrototype.Certificate21

end OAI
