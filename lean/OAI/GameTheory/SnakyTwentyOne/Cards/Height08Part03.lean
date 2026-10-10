import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part04
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_518_i1 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (3, 6), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_518_i1 : Finset Cell := ⟨(([(0, 5), (1, 5), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 5), (4, 6), (5, 6), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_518_i1 : Fin 3 → Finset Cell := ![(placed21 2 (3, 3) required_6), (placed21 5 (6, 4) required_213), (placed21 1 (1, 4) required_278)]
def childrenD_518_i1 : Fin 3 → Finset Cell := ![(placed21 2 (3, 3) envelope_6), (placed21 5 (6, 4) envelope_213), (placed21 1 (1, 4) envelope_278)]
theorem common_sub_518_i1 : commonEnvelope childrenD_518_i1 ⊆ insert (3, 7) required_518_i1 := by decide +kernel
theorem child_required_sub_518_i1 : ∀ j, childrenC_518_i1 j ⊆ insert (3, 7) required_518_i1 := by decide +kernel
theorem child_envelope_sub_518_i1 : ∀ j, childrenD_518_i1 j ⊆ envelope_518_i1 := by decide +kernel
theorem pivot_mem_518_i1 : (3, 7) ∈ envelope_518_i1 := by decide +kernel
theorem children_work_518_i1 : ∀ j, Template HasSnaky 5 (childrenC_518_i1 j) (childrenD_518_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 2 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_213 5 (6, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_278 1 (1, 4)).mono (by decide +kernel)
theorem row_works_518_i1 : Template HasSnaky 6 required_518_i1 envelope_518_i1 := by
  refine compose HasSnaky 5 childrenC_518_i1 childrenD_518_i1 children_work_518_i1 (3, 7)
    required_518_i1 envelope_518_i1 pivot_mem_518_i1 child_required_sub_518_i1 child_envelope_sub_518_i1 ?_
  intro b hb
  exact common_sub_518_i1 (mem_commonEnvelope childrenD_518_i1 b hb)
def required_518_i0 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_518_i0 : Finset Cell := ⟨(([(0, 5), (1, 5), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 5), (4, 6), (4, 7), (5, 6), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_518_i0 : Fin 2 → Finset Cell := ![(placed21 1 (3, 3) required_5), required_518_i1]
def childrenD_518_i0 : Fin 2 → Finset Cell := ![(placed21 1 (3, 3) envelope_5), envelope_518_i1]
theorem common_sub_518_i0 : commonEnvelope childrenD_518_i0 ⊆ insert (3, 6) required_518_i0 := by decide +kernel
theorem child_required_sub_518_i0 : ∀ j, childrenC_518_i0 j ⊆ insert (3, 6) required_518_i0 := by decide +kernel
theorem child_envelope_sub_518_i0 : ∀ j, childrenD_518_i0 j ⊆ envelope_518_i0 := by decide +kernel
theorem pivot_mem_518_i0 : (3, 6) ∈ envelope_518_i0 := by decide +kernel
theorem children_work_518_i0 : ∀ j, Template HasSnaky 6 (childrenC_518_i0 j) (childrenD_518_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (3, 3)).mono (by decide +kernel)
  · exact row_works_518_i1.mono (by decide +kernel)
theorem row_works_518_i0 : Template HasSnaky 7 required_518_i0 envelope_518_i0 := by
  refine compose HasSnaky 6 childrenC_518_i0 childrenD_518_i0 children_work_518_i0 (3, 6)
    required_518_i0 envelope_518_i0 pivot_mem_518_i0 child_required_sub_518_i0 child_envelope_sub_518_i0 ?_
  intro b hb
  exact common_sub_518_i0 (mem_commonEnvelope childrenD_518_i0 b hb)
def required_518 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_518 : Finset Cell := ⟨(([(0, 5), (1, 5), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 5), (4, 6), (4, 7), (4, 8), (5, 6), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_518 : Fin 4 → Finset Cell := ![(placed21 0 (3, 2) required_61), (placed21 6 (4, 6) required_89), (placed21 1 (1, 2) required_183), required_518_i0]
def childrenD_518 : Fin 4 → Finset Cell := ![(placed21 0 (3, 2) envelope_61), (placed21 6 (4, 6) envelope_89), (placed21 1 (1, 2) envelope_183), envelope_518_i0]
theorem common_sub_518 : commonEnvelope childrenD_518 ⊆ insert (4, 6) required_518 := by decide +kernel
theorem child_required_sub_518 : ∀ j, childrenC_518 j ⊆ insert (4, 6) required_518 := by decide +kernel
theorem child_envelope_sub_518 : ∀ j, childrenD_518 j ⊆ envelope_518 := by decide +kernel
theorem pivot_mem_518 : (4, 6) ∈ envelope_518 := by decide +kernel
theorem children_work_518 : ∀ j, Template HasSnaky 7 (childrenC_518 j) (childrenD_518 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_61 0 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_89 6 (4, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_183 1 (1, 2)).mono (by decide +kernel)
  · exact row_works_518_i0.mono (by decide +kernel)
theorem row_works_518 : Template HasSnaky 8 required_518 envelope_518 := by
  refine compose HasSnaky 7 childrenC_518 childrenD_518 children_work_518 (4, 6)
    required_518 envelope_518 pivot_mem_518 child_required_sub_518 child_envelope_sub_518 ?_
  intro b hb
  exact common_sub_518 (mem_commonEnvelope childrenD_518 b hb)
def required_523 : Finset Cell := ⟨(([(2, 4), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_523 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 6), (4, 7), (4, 8), (5, 3), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_523 : Fin 5 → Finset Cell := ![(placed21 0 (2, 1) required_14), (placed21 0 (1, 2) required_122), (placed21 4 (1, 6) required_136), (placed21 2 (4, 1) required_367), (placed21 7 (5, 6) required_522)]
def childrenD_523 : Fin 5 → Finset Cell := ![(placed21 0 (2, 1) envelope_14), (placed21 0 (1, 2) envelope_122), (placed21 4 (1, 6) envelope_136), (placed21 2 (4, 1) envelope_367), (placed21 7 (5, 6) envelope_522)]
theorem common_sub_523 : commonEnvelope childrenD_523 ⊆ insert (3, 5) required_523 := by decide +kernel
theorem child_required_sub_523 : ∀ j, childrenC_523 j ⊆ insert (3, 5) required_523 := by decide +kernel
theorem child_envelope_sub_523 : ∀ j, childrenD_523 j ⊆ envelope_523 := by decide +kernel
theorem pivot_mem_523 : (3, 5) ∈ envelope_523 := by decide +kernel
theorem children_work_523 : ∀ j, Template HasSnaky 7 (childrenC_523 j) (childrenD_523 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_14 0 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_122 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_136 4 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_367 2 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_522 7 (5, 6)).mono (by decide +kernel)
theorem row_works_523 : Template HasSnaky 8 required_523 envelope_523 := by
  refine compose HasSnaky 7 childrenC_523 childrenD_523 children_work_523 (3, 5)
    required_523 envelope_523 pivot_mem_523 child_required_sub_523 child_envelope_sub_523 ?_
  intro b hb
  exact common_sub_523 (mem_commonEnvelope childrenD_523 b hb)
def required_524 : Finset Cell := ⟨(([(2, 4), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_524 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (1, 1), (1, 2), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 6), (4, 7), (4, 8), (5, 3), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_524 : Fin 4 → Finset Cell := ![(placed21 3 (0, 6) required_88), (placed21 1 (0, 2) required_213), (placed21 0 (2, 1) required_254), (placed21 7 (5, 6) required_522)]
def childrenD_524 : Fin 4 → Finset Cell := ![(placed21 3 (0, 6) envelope_88), (placed21 1 (0, 2) envelope_213), (placed21 0 (2, 1) envelope_254), (placed21 7 (5, 6) envelope_522)]
theorem common_sub_524 : commonEnvelope childrenD_524 ⊆ insert (3, 5) required_524 := by decide +kernel
theorem child_required_sub_524 : ∀ j, childrenC_524 j ⊆ insert (3, 5) required_524 := by decide +kernel
theorem child_envelope_sub_524 : ∀ j, childrenD_524 j ⊆ envelope_524 := by decide +kernel
theorem pivot_mem_524 : (3, 5) ∈ envelope_524 := by decide +kernel
theorem children_work_524 : ∀ j, Template HasSnaky 7 (childrenC_524 j) (childrenD_524 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_88 3 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_213 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_254 0 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_522 7 (5, 6)).mono (by decide +kernel)
theorem row_works_524 : Template HasSnaky 8 required_524 envelope_524 := by
  refine compose HasSnaky 7 childrenC_524 childrenD_524 children_work_524 (3, 5)
    required_524 envelope_524 pivot_mem_524 child_required_sub_524 child_envelope_sub_524 ?_
  intro b hb
  exact common_sub_524 (mem_commonEnvelope childrenD_524 b hb)
def required_530_i2 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_530_i2 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 5), (3, 6), (3, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_530_i2 : Fin 2 → Finset Cell := ![(placed21 3 (2, 5) required_5), (placed21 0 (1, 2) required_20)]
def childrenD_530_i2 : Fin 2 → Finset Cell := ![(placed21 3 (2, 5) envelope_5), (placed21 0 (1, 2) envelope_20)]
theorem common_sub_530_i2 : commonEnvelope childrenD_530_i2 ⊆ insert (2, 5) required_530_i2 := by decide +kernel
theorem child_required_sub_530_i2 : ∀ j, childrenC_530_i2 j ⊆ insert (2, 5) required_530_i2 := by decide +kernel
theorem child_envelope_sub_530_i2 : ∀ j, childrenD_530_i2 j ⊆ envelope_530_i2 := by decide +kernel
theorem pivot_mem_530_i2 : (2, 5) ∈ envelope_530_i2 := by decide +kernel
theorem children_work_530_i2 : ∀ j, Template HasSnaky 3 (childrenC_530_i2 j) (childrenD_530_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (2, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_20 0 (1, 2)).mono (by decide +kernel)
theorem row_works_530_i2 : Template HasSnaky 4 required_530_i2 envelope_530_i2 := by
  refine compose HasSnaky 3 childrenC_530_i2 childrenD_530_i2 children_work_530_i2 (2, 5)
    required_530_i2 envelope_530_i2 pivot_mem_530_i2 child_required_sub_530_i2 child_envelope_sub_530_i2 ?_
  intro b hb
  exact common_sub_530_i2 (mem_commonEnvelope childrenD_530_i2 b hb)
def required_530_i1 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_530_i1 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 5), (3, 6), (3, 7), (4, 2), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_530_i1 : Fin 2 → Finset Cell := ![(placed21 3 (0, 3) required_51), required_530_i2]
def childrenD_530_i1 : Fin 2 → Finset Cell := ![(placed21 3 (0, 3) envelope_51), envelope_530_i2]
theorem common_sub_530_i1 : commonEnvelope childrenD_530_i1 ⊆ insert (3, 2) required_530_i1 := by decide +kernel
theorem child_required_sub_530_i1 : ∀ j, childrenC_530_i1 j ⊆ insert (3, 2) required_530_i1 := by decide +kernel
theorem child_envelope_sub_530_i1 : ∀ j, childrenD_530_i1 j ⊆ envelope_530_i1 := by decide +kernel
theorem pivot_mem_530_i1 : (3, 2) ∈ envelope_530_i1 := by decide +kernel
theorem children_work_530_i1 : ∀ j, Template HasSnaky 4 (childrenC_530_i1 j) (childrenD_530_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_51 3 (0, 3)).mono (by decide +kernel)
  · exact row_works_530_i2.mono (by decide +kernel)
theorem row_works_530_i1 : Template HasSnaky 5 required_530_i1 envelope_530_i1 := by
  refine compose HasSnaky 4 childrenC_530_i1 childrenD_530_i1 children_work_530_i1 (3, 2)
    required_530_i1 envelope_530_i1 pivot_mem_530_i1 child_required_sub_530_i1 child_envelope_sub_530_i1 ?_
  intro b hb
  exact common_sub_530_i1 (mem_commonEnvelope childrenD_530_i1 b hb)
def required_530_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_530_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 5), (3, 6), (3, 7), (4, 2), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_530_i0 : Fin 2 → Finset Cell := ![(placed21 6 (2, 5) required_23), required_530_i1]
def childrenD_530_i0 : Fin 2 → Finset Cell := ![(placed21 6 (2, 5) envelope_23), envelope_530_i1]
theorem common_sub_530_i0 : commonEnvelope childrenD_530_i0 ⊆ insert (2, 2) required_530_i0 := by decide +kernel
theorem child_required_sub_530_i0 : ∀ j, childrenC_530_i0 j ⊆ insert (2, 2) required_530_i0 := by decide +kernel
theorem child_envelope_sub_530_i0 : ∀ j, childrenD_530_i0 j ⊆ envelope_530_i0 := by decide +kernel
theorem pivot_mem_530_i0 : (2, 2) ∈ envelope_530_i0 := by decide +kernel
theorem children_work_530_i0 : ∀ j, Template HasSnaky 5 (childrenC_530_i0 j) (childrenD_530_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_23 6 (2, 5)).mono (by decide +kernel)
  · exact row_works_530_i1.mono (by decide +kernel)
theorem row_works_530_i0 : Template HasSnaky 6 required_530_i0 envelope_530_i0 := by
  refine compose HasSnaky 5 childrenC_530_i0 childrenD_530_i0 children_work_530_i0 (2, 2)
    required_530_i0 envelope_530_i0 pivot_mem_530_i0 child_required_sub_530_i0 child_envelope_sub_530_i0 ?_
  intro b hb
  exact common_sub_530_i0 (mem_commonEnvelope childrenD_530_i0 b hb)
def required_530 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_530 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (5, 2), (5, 3), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_530 : Fin 4 → Finset Cell := ![(placed21 4 (0, 5) required_72), (placed21 4 (0, 5) required_360), (placed21 0 (0, 1) required_499), required_530_i0]
def childrenD_530 : Fin 4 → Finset Cell := ![(placed21 4 (0, 5) envelope_72), (placed21 4 (0, 5) envelope_360), (placed21 0 (0, 1) envelope_499), envelope_530_i0]
theorem common_sub_530 : commonEnvelope childrenD_530 ⊆ insert (2, 4) required_530 := by decide +kernel
theorem child_required_sub_530 : ∀ j, childrenC_530 j ⊆ insert (2, 4) required_530 := by decide +kernel
theorem child_envelope_sub_530 : ∀ j, childrenD_530 j ⊆ envelope_530 := by decide +kernel
theorem pivot_mem_530 : (2, 4) ∈ envelope_530 := by decide +kernel
theorem children_work_530 : ∀ j, Template HasSnaky 7 (childrenC_530 j) (childrenD_530 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_72 4 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_360 4 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_499 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_530_i0.mono (by decide +kernel)
theorem row_works_530 : Template HasSnaky 8 required_530 envelope_530 := by
  refine compose HasSnaky 7 childrenC_530 childrenD_530 children_work_530 (2, 4)
    required_530 envelope_530 pivot_mem_530 child_required_sub_530 child_envelope_sub_530 ?_
  intro b hb
  exact common_sub_530 (mem_commonEnvelope childrenD_530 b hb)
def required_532_i0 : Finset Cell := ⟨(([(2, 3), (2, 4), (2, 5), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_532_i0 : Finset Cell := ⟨(([(1, 4), (1, 5), (1, 7), (1, 8), (1, 9), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 2), (4, 3), (4, 6), (4, 7), (5, 3), (5, 6), (6, 3), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_532_i0 : Fin 4 → Finset Cell := ![(placed21 2 (3, 2) required_19), (placed21 2 (3, 2) required_84), (placed21 5 (3, 3) required_314), (placed21 4 (1, 7) required_521)]
def childrenD_532_i0 : Fin 4 → Finset Cell := ![(placed21 2 (3, 2) envelope_19), (placed21 2 (3, 2) envelope_84), (placed21 5 (3, 3) envelope_314), (placed21 4 (1, 7) envelope_521)]
theorem common_sub_532_i0 : commonEnvelope childrenD_532_i0 ⊆ insert (2, 6) required_532_i0 := by decide +kernel
theorem child_required_sub_532_i0 : ∀ j, childrenC_532_i0 j ⊆ insert (2, 6) required_532_i0 := by decide +kernel
theorem child_envelope_sub_532_i0 : ∀ j, childrenD_532_i0 j ⊆ envelope_532_i0 := by decide +kernel
theorem pivot_mem_532_i0 : (2, 6) ∈ envelope_532_i0 := by decide +kernel
theorem children_work_532_i0 : ∀ j, Template HasSnaky 6 (childrenC_532_i0 j) (childrenD_532_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_19 2 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_84 2 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_314 5 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_521 4 (1, 7)).mono (by decide +kernel)
theorem row_works_532_i0 : Template HasSnaky 7 required_532_i0 envelope_532_i0 := by
  refine compose HasSnaky 6 childrenC_532_i0 childrenD_532_i0 children_work_532_i0 (2, 6)
    required_532_i0 envelope_532_i0 pivot_mem_532_i0 child_required_sub_532_i0 child_envelope_sub_532_i0 ?_
  intro b hb
  exact common_sub_532_i0 (mem_commonEnvelope childrenD_532_i0 b hb)
def required_532 : Finset Cell := ⟨(([(2, 4), (2, 5), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_532 : Finset Cell := ⟨(([(0, 2), (1, 0), (1, 1), (1, 2), (1, 4), (1, 5), (1, 7), (1, 8), (1, 9), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 2), (4, 3), (4, 6), (4, 7), (5, 3), (5, 6), (6, 3), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_532 : Fin 4 → Finset Cell := ![(placed21 0 (2, 2) required_44), (placed21 0 (2, 2) required_52), (placed21 3 (0, 6) required_134), required_532_i0]
def childrenD_532 : Fin 4 → Finset Cell := ![(placed21 0 (2, 2) envelope_44), (placed21 0 (2, 2) envelope_52), (placed21 3 (0, 6) envelope_134), envelope_532_i0]
theorem common_sub_532 : commonEnvelope childrenD_532 ⊆ insert (2, 3) required_532 := by decide +kernel
theorem child_required_sub_532 : ∀ j, childrenC_532 j ⊆ insert (2, 3) required_532 := by decide +kernel
theorem child_envelope_sub_532 : ∀ j, childrenD_532 j ⊆ envelope_532 := by decide +kernel
theorem pivot_mem_532 : (2, 3) ∈ envelope_532 := by decide +kernel
theorem children_work_532 : ∀ j, Template HasSnaky 7 (childrenC_532 j) (childrenD_532 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_134 3 (0, 6)).mono (by decide +kernel)
  · exact row_works_532_i0.mono (by decide +kernel)
theorem row_works_532 : Template HasSnaky 8 required_532 envelope_532 := by
  refine compose HasSnaky 7 childrenC_532 childrenD_532 children_work_532 (2, 3)
    required_532 envelope_532 pivot_mem_532 child_required_sub_532 child_envelope_sub_532 ?_
  intro b hb
  exact common_sub_532 (mem_commonEnvelope childrenD_532 b hb)
def required_533_i0 : Finset Cell := ⟨(([(1, 3), (2, 2), (2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_533_i0 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (5, 1), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_533_i0 : Fin 3 → Finset Cell := ![(placed21 0 (2, 0) required_53), (placed21 4 (1, 6) required_55), (placed21 7 (5, 4) required_392)]
def childrenD_533_i0 : Fin 3 → Finset Cell := ![(placed21 0 (2, 0) envelope_53), (placed21 4 (1, 6) envelope_55), (placed21 7 (5, 4) envelope_392)]
theorem common_sub_533_i0 : commonEnvelope childrenD_533_i0 ⊆ insert (3, 4) required_533_i0 := by decide +kernel
theorem child_required_sub_533_i0 : ∀ j, childrenC_533_i0 j ⊆ insert (3, 4) required_533_i0 := by decide +kernel
theorem child_envelope_sub_533_i0 : ∀ j, childrenD_533_i0 j ⊆ envelope_533_i0 := by decide +kernel
theorem pivot_mem_533_i0 : (3, 4) ∈ envelope_533_i0 := by decide +kernel
theorem children_work_533_i0 : ∀ j, Template HasSnaky 6 (childrenC_533_i0 j) (childrenD_533_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_53 0 (2, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_55 4 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_392 7 (5, 4)).mono (by decide +kernel)
theorem row_works_533_i0 : Template HasSnaky 7 required_533_i0 envelope_533_i0 := by
  refine compose HasSnaky 6 childrenC_533_i0 childrenD_533_i0 children_work_533_i0 (3, 4)
    required_533_i0 envelope_533_i0 pivot_mem_533_i0 child_required_sub_533_i0 child_envelope_sub_533_i0 ?_
  intro b hb
  exact common_sub_533_i0 (mem_commonEnvelope childrenD_533_i0 b hb)
def required_533 : Finset Cell := ⟨(([(1, 3), (2, 2), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_533 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (5, 1), (5, 2), (5, 3), (6, 2), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_533 : Fin 3 → Finset Cell := ![(placed21 3 (0, 3) required_11), (placed21 0 (1, 0) required_279), required_533_i0]
def childrenD_533 : Fin 3 → Finset Cell := ![(placed21 3 (0, 3) envelope_11), (placed21 0 (1, 0) envelope_279), envelope_533_i0]
theorem common_sub_533 : commonEnvelope childrenD_533 ⊆ insert (4, 3) required_533 := by decide +kernel
theorem child_required_sub_533 : ∀ j, childrenC_533 j ⊆ insert (4, 3) required_533 := by decide +kernel
theorem child_envelope_sub_533 : ∀ j, childrenD_533 j ⊆ envelope_533 := by decide +kernel
theorem pivot_mem_533 : (4, 3) ∈ envelope_533 := by decide +kernel
theorem children_work_533 : ∀ j, Template HasSnaky 7 (childrenC_533 j) (childrenD_533 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 3 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_279 0 (1, 0)).mono (by decide +kernel)
  · exact row_works_533_i0.mono (by decide +kernel)
theorem row_works_533 : Template HasSnaky 8 required_533 envelope_533 := by
  refine compose HasSnaky 7 childrenC_533 childrenD_533 children_work_533 (4, 3)
    required_533 envelope_533 pivot_mem_533 child_required_sub_533 child_envelope_sub_533 ?_
  intro b hb
  exact common_sub_533 (mem_commonEnvelope childrenD_533 b hb)
def required_534_i1 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 4), (2, 5), (3, 3), (3, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_534_i1 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 3), (3, 6), (3, 7), (4, 3), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_534_i1 : Fin 2 → Finset Cell := ![(placed21 1 (2, 3) required_5), (placed21 1 (0, 3) required_177)]
def childrenD_534_i1 : Fin 2 → Finset Cell := ![(placed21 1 (2, 3) envelope_5), (placed21 1 (0, 3) envelope_177)]
theorem common_sub_534_i1 : commonEnvelope childrenD_534_i1 ⊆ insert (2, 6) required_534_i1 := by decide +kernel
theorem child_required_sub_534_i1 : ∀ j, childrenC_534_i1 j ⊆ insert (2, 6) required_534_i1 := by decide +kernel
theorem child_envelope_sub_534_i1 : ∀ j, childrenD_534_i1 j ⊆ envelope_534_i1 := by decide +kernel
theorem pivot_mem_534_i1 : (2, 6) ∈ envelope_534_i1 := by decide +kernel
theorem children_work_534_i1 : ∀ j, Template HasSnaky 3 (childrenC_534_i1 j) (childrenD_534_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_177 1 (0, 3)).mono (by decide +kernel)
theorem row_works_534_i1 : Template HasSnaky 4 required_534_i1 envelope_534_i1 := by
  refine compose HasSnaky 3 childrenC_534_i1 childrenD_534_i1 children_work_534_i1 (2, 6)
    required_534_i1 envelope_534_i1 pivot_mem_534_i1 child_required_sub_534_i1 child_envelope_sub_534_i1 ?_
  intro b hb
  exact common_sub_534_i1 (mem_commonEnvelope childrenD_534_i1 b hb)
def required_534_i2 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 4), (2, 5), (3, 3), (3, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_534_i2 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (3, 6), (4, 2), (4, 3), (5, 2), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_534_i2 : Fin 2 → Finset Cell := ![(placed21 1 (2, 2) required_0), (placed21 7 (5, 6) required_239)]
def childrenD_534_i2 : Fin 2 → Finset Cell := ![(placed21 1 (2, 2) envelope_0), (placed21 7 (5, 6) envelope_239)]
theorem common_sub_534_i2 : commonEnvelope childrenD_534_i2 ⊆ insert (3, 5) required_534_i2 := by decide +kernel
theorem child_required_sub_534_i2 : ∀ j, childrenC_534_i2 j ⊆ insert (3, 5) required_534_i2 := by decide +kernel
theorem child_envelope_sub_534_i2 : ∀ j, childrenD_534_i2 j ⊆ envelope_534_i2 := by decide +kernel
theorem pivot_mem_534_i2 : (3, 5) ∈ envelope_534_i2 := by decide +kernel
theorem children_work_534_i2 : ∀ j, Template HasSnaky 3 (childrenC_534_i2 j) (childrenD_534_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 1 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_239 7 (5, 6)).mono (by decide +kernel)
theorem row_works_534_i2 : Template HasSnaky 4 required_534_i2 envelope_534_i2 := by
  refine compose HasSnaky 3 childrenC_534_i2 childrenD_534_i2 children_work_534_i2 (3, 5)
    required_534_i2 envelope_534_i2 pivot_mem_534_i2 child_required_sub_534_i2 child_envelope_sub_534_i2 ?_
  intro b hb
  exact common_sub_534_i2 (mem_commonEnvelope childrenD_534_i2 b hb)
def required_534_i0 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 4), (2, 5), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_534_i0 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (5, 2), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_534_i0 : Fin 3 → Finset Cell := ![(placed21 0 (2, 2) required_139), required_534_i1, required_534_i2]
def childrenD_534_i0 : Fin 3 → Finset Cell := ![(placed21 0 (2, 2) envelope_139), envelope_534_i1, envelope_534_i2]
theorem common_sub_534_i0 : commonEnvelope childrenD_534_i0 ⊆ insert (3, 6) required_534_i0 := by decide +kernel
theorem child_required_sub_534_i0 : ∀ j, childrenC_534_i0 j ⊆ insert (3, 6) required_534_i0 := by decide +kernel
theorem child_envelope_sub_534_i0 : ∀ j, childrenD_534_i0 j ⊆ envelope_534_i0 := by decide +kernel
theorem pivot_mem_534_i0 : (3, 6) ∈ envelope_534_i0 := by decide +kernel
theorem children_work_534_i0 : ∀ j, Template HasSnaky 4 (childrenC_534_i0 j) (childrenD_534_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_139 0 (2, 2)).mono (by decide +kernel)
  · exact row_works_534_i1.mono (by decide +kernel)
  · exact row_works_534_i2.mono (by decide +kernel)
theorem row_works_534_i0 : Template HasSnaky 5 required_534_i0 envelope_534_i0 := by
  refine compose HasSnaky 4 childrenC_534_i0 childrenD_534_i0 children_work_534_i0 (3, 6)
    required_534_i0 envelope_534_i0 pivot_mem_534_i0 child_required_sub_534_i0 child_envelope_sub_534_i0 ?_
  intro b hb
  exact common_sub_534_i0 (mem_commonEnvelope childrenD_534_i0 b hb)
def required_534 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 4), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_534 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 2), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_534 : Fin 4 → Finset Cell := ![(placed21 4 (2, 6) required_44), (placed21 4 (2, 6) required_52), (placed21 3 (0, 5) required_388), required_534_i0]
def childrenD_534 : Fin 4 → Finset Cell := ![(placed21 4 (2, 6) envelope_44), (placed21 4 (2, 6) envelope_52), (placed21 3 (0, 5) envelope_388), envelope_534_i0]
theorem common_sub_534 : commonEnvelope childrenD_534 ⊆ insert (2, 5) required_534 := by decide +kernel
theorem child_required_sub_534 : ∀ j, childrenC_534 j ⊆ insert (2, 5) required_534 := by decide +kernel
theorem child_envelope_sub_534 : ∀ j, childrenD_534 j ⊆ envelope_534 := by decide +kernel
theorem pivot_mem_534 : (2, 5) ∈ envelope_534 := by decide +kernel
theorem children_work_534 : ∀ j, Template HasSnaky 7 (childrenC_534 j) (childrenD_534 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 4 (2, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 4 (2, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_388 3 (0, 5)).mono (by decide +kernel)
  · exact row_works_534_i0.mono (by decide +kernel)
theorem row_works_534 : Template HasSnaky 8 required_534 envelope_534 := by
  refine compose HasSnaky 7 childrenC_534 childrenD_534 children_work_534 (2, 5)
    required_534 envelope_534 pivot_mem_534 child_required_sub_534 child_envelope_sub_534 ?_
  intro b hb
  exact common_sub_534 (mem_commonEnvelope childrenD_534 b hb)
def required_547_i0 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_547_i0 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 6), (2, 7), (2, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_547_i0 : Fin 2 → Finset Cell := ![(placed21 6 (1, 5) required_6), (placed21 2 (2, 2) required_17)]
def childrenD_547_i0 : Fin 2 → Finset Cell := ![(placed21 6 (1, 5) envelope_6), (placed21 2 (2, 2) envelope_17)]
theorem common_sub_547_i0 : commonEnvelope childrenD_547_i0 ⊆ insert (1, 5) required_547_i0 := by decide +kernel
theorem child_required_sub_547_i0 : ∀ j, childrenC_547_i0 j ⊆ insert (1, 5) required_547_i0 := by decide +kernel
theorem child_envelope_sub_547_i0 : ∀ j, childrenD_547_i0 j ⊆ envelope_547_i0 := by decide +kernel
theorem pivot_mem_547_i0 : (1, 5) ∈ envelope_547_i0 := by decide +kernel
theorem children_work_547_i0 : ∀ j, Template HasSnaky 4 (childrenC_547_i0 j) (childrenD_547_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 6 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_17 2 (2, 2)).mono (by decide +kernel)
theorem row_works_547_i0 : Template HasSnaky 5 required_547_i0 envelope_547_i0 := by
  refine compose HasSnaky 4 childrenC_547_i0 childrenD_547_i0 children_work_547_i0 (1, 5)
    required_547_i0 envelope_547_i0 pivot_mem_547_i0 child_required_sub_547_i0 child_envelope_sub_547_i0 ?_
  intro b hb
  exact common_sub_547_i0 (mem_commonEnvelope childrenD_547_i0 b hb)
def required_547_i1 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_547_i1 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2), (5, 0), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_547_i1 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) required_5), (placed21 3 (0, 4) required_525)]
def childrenD_547_i1 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) envelope_5), (placed21 3 (0, 4) envelope_525)]
theorem common_sub_547_i1 : commonEnvelope childrenD_547_i1 ⊆ insert (2, 4) required_547_i1 := by decide +kernel
theorem child_required_sub_547_i1 : ∀ j, childrenC_547_i1 j ⊆ insert (2, 4) required_547_i1 := by decide +kernel
theorem child_envelope_sub_547_i1 : ∀ j, childrenD_547_i1 j ⊆ envelope_547_i1 := by decide +kernel
theorem pivot_mem_547_i1 : (2, 4) ∈ envelope_547_i1 := by decide +kernel
theorem children_work_547_i1 : ∀ j, Template HasSnaky 6 (childrenC_547_i1 j) (childrenD_547_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_525 3 (0, 4)).mono (by decide +kernel)
theorem row_works_547_i1 : Template HasSnaky 7 required_547_i1 envelope_547_i1 := by
  refine compose HasSnaky 6 childrenC_547_i1 childrenD_547_i1 children_work_547_i1 (2, 4)
    required_547_i1 envelope_547_i1 pivot_mem_547_i1 child_required_sub_547_i1 child_envelope_sub_547_i1 ?_
  intro b hb
  exact common_sub_547_i1 (mem_commonEnvelope childrenD_547_i1 b hb)
def required_547 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_547 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2), (5, 0), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_547 : Fin 4 → Finset Cell := ![required_19, (placed21 5 (2, 1) required_314), required_547_i0, required_547_i1]
def childrenD_547 : Fin 4 → Finset Cell := ![envelope_19, (placed21 5 (2, 1) envelope_314), envelope_547_i0, envelope_547_i1]
theorem common_sub_547 : commonEnvelope childrenD_547 ⊆ insert (1, 4) required_547 := by decide +kernel
theorem child_required_sub_547 : ∀ j, childrenC_547 j ⊆ insert (1, 4) required_547 := by decide +kernel
theorem child_envelope_sub_547 : ∀ j, childrenD_547 j ⊆ envelope_547 := by decide +kernel
theorem pivot_mem_547 : (1, 4) ∈ envelope_547 := by decide +kernel
theorem children_work_547 : ∀ j, Template HasSnaky 7 (childrenC_547 j) (childrenD_547 j) := by
  intro j
  fin_cases j
  · exact row_works_19.mono (by decide +kernel)
  · exact (placed21_template row_works_314 5 (2, 1)).mono (by decide +kernel)
  · exact row_works_547_i0.mono (by decide +kernel)
  · exact row_works_547_i1.mono (by decide +kernel)
theorem row_works_547 : Template HasSnaky 8 required_547 envelope_547 := by
  refine compose HasSnaky 7 childrenC_547 childrenD_547 children_work_547 (1, 4)
    required_547 envelope_547 pivot_mem_547 child_required_sub_547 child_envelope_sub_547 ?_
  intro b hb
  exact common_sub_547 (mem_commonEnvelope childrenD_547 b hb)
def required_558_i0 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (2, 2), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_558_i0 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_558_i0 : Fin 2 → Finset Cell := ![(placed21 4 (0, 2) required_5), required_471]
def childrenD_558_i0 : Fin 2 → Finset Cell := ![(placed21 4 (0, 2) envelope_5), envelope_471]
theorem common_sub_558_i0 : commonEnvelope childrenD_558_i0 ⊆ insert (3, 1) required_558_i0 := by decide +kernel
theorem child_required_sub_558_i0 : ∀ j, childrenC_558_i0 j ⊆ insert (3, 1) required_558_i0 := by decide +kernel
theorem child_envelope_sub_558_i0 : ∀ j, childrenD_558_i0 j ⊆ envelope_558_i0 := by decide +kernel
theorem pivot_mem_558_i0 : (3, 1) ∈ envelope_558_i0 := by decide +kernel
theorem children_work_558_i0 : ∀ j, Template HasSnaky 6 (childrenC_558_i0 j) (childrenD_558_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 2)).mono (by decide +kernel)
  · exact row_works_471.mono (by decide +kernel)
theorem row_works_558_i0 : Template HasSnaky 7 required_558_i0 envelope_558_i0 := by
  refine compose HasSnaky 6 childrenC_558_i0 childrenD_558_i0 children_work_558_i0 (3, 1)
    required_558_i0 envelope_558_i0 pivot_mem_558_i0 child_required_sub_558_i0 child_envelope_sub_558_i0 ?_
  intro b hb
  exact common_sub_558_i0 (mem_commonEnvelope childrenD_558_i0 b hb)
def required_558 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_558 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_558 : Fin 4 → Finset Cell := ![(placed21 0 (0, 1) required_8), (placed21 1 (0, 2) required_16), (placed21 4 (0, 3) required_24), required_558_i0]
def childrenD_558 : Fin 4 → Finset Cell := ![(placed21 0 (0, 1) envelope_8), (placed21 1 (0, 2) envelope_16), (placed21 4 (0, 3) envelope_24), envelope_558_i0]
theorem common_sub_558 : commonEnvelope childrenD_558 ⊆ insert (3, 2) required_558 := by decide +kernel
theorem child_required_sub_558 : ∀ j, childrenC_558 j ⊆ insert (3, 2) required_558 := by decide +kernel
theorem child_envelope_sub_558 : ∀ j, childrenD_558 j ⊆ envelope_558 := by decide +kernel
theorem pivot_mem_558 : (3, 2) ∈ envelope_558 := by decide +kernel
theorem children_work_558 : ∀ j, Template HasSnaky 7 (childrenC_558 j) (childrenD_558 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_16 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_24 4 (0, 3)).mono (by decide +kernel)
  · exact row_works_558_i0.mono (by decide +kernel)
theorem row_works_558 : Template HasSnaky 8 required_558 envelope_558 := by
  refine compose HasSnaky 7 childrenC_558 childrenD_558 children_work_558 (3, 2)
    required_558 envelope_558 pivot_mem_558 child_required_sub_558 child_envelope_sub_558 ?_
  intro b hb
  exact common_sub_558 (mem_commonEnvelope childrenD_558 b hb)
def height_518_i1 : ℕ := 6
def childrenH_518_i1 : Fin 3 → ℕ := ![height_6, height_213, height_278]
theorem height_exact_518_i1 : height_518_i1 = 1 + Finset.univ.sup childrenH_518_i1 := by decide +kernel
theorem required_origin_518_i1 : ∀ x ∈ required_518_i1,
    (∃ j, x ∈ childrenC_518_i1 j) ∨ ∀ j, x ∈ childrenD_518_i1 j := by decide +kernel
theorem required_exact_518_i1 : required_518_i1 =
    ((Finset.univ.biUnion childrenC_518_i1) ∪ commonEnvelope childrenD_518_i1).erase (3, 7) := by
  exact required_eq_combination childrenC_518_i1 childrenD_518_i1 (3, 7) required_518_i1
    (by decide +kernel) child_required_sub_518_i1 common_sub_518_i1 required_origin_518_i1
theorem envelope_origin_518_i1 : ∀ x ∈ envelope_518_i1,
    x = (3, 7) ∨ ∃ j, x ∈ childrenD_518_i1 j := by decide +kernel
theorem envelope_exact_518_i1 : envelope_518_i1 =
    insert (3, 7) (Finset.univ.biUnion childrenD_518_i1) := by
  exact envelope_eq_combination childrenD_518_i1 (3, 7) envelope_518_i1
    pivot_mem_518_i1 child_envelope_sub_518_i1 envelope_origin_518_i1
def checked_518_i1 : CheckedCard where
  required := required_518_i1
  envelope := envelope_518_i1
  height := height_518_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_518_i1
def height_518_i0 : ℕ := 7
def childrenH_518_i0 : Fin 2 → ℕ := ![height_5, height_518_i1]
theorem height_exact_518_i0 : height_518_i0 = 1 + Finset.univ.sup childrenH_518_i0 := by decide +kernel
theorem required_origin_518_i0 : ∀ x ∈ required_518_i0,
    (∃ j, x ∈ childrenC_518_i0 j) ∨ ∀ j, x ∈ childrenD_518_i0 j := by decide +kernel
theorem required_exact_518_i0 : required_518_i0 =
    ((Finset.univ.biUnion childrenC_518_i0) ∪ commonEnvelope childrenD_518_i0).erase (3, 6) := by
  exact required_eq_combination childrenC_518_i0 childrenD_518_i0 (3, 6) required_518_i0
    (by decide +kernel) child_required_sub_518_i0 common_sub_518_i0 required_origin_518_i0
theorem envelope_origin_518_i0 : ∀ x ∈ envelope_518_i0,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_518_i0 j := by decide +kernel
theorem envelope_exact_518_i0 : envelope_518_i0 =
    insert (3, 6) (Finset.univ.biUnion childrenD_518_i0) := by
  exact envelope_eq_combination childrenD_518_i0 (3, 6) envelope_518_i0
    pivot_mem_518_i0 child_envelope_sub_518_i0 envelope_origin_518_i0
def checked_518_i0 : CheckedCard where
  required := required_518_i0
  envelope := envelope_518_i0
  height := height_518_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_518_i0
def height_518 : ℕ := 8
def childrenH_518 : Fin 4 → ℕ := ![height_61, height_89, height_183, height_518_i0]
theorem height_exact_518 : height_518 = 1 + Finset.univ.sup childrenH_518 := by decide +kernel
theorem required_origin_518 : ∀ x ∈ required_518,
    (∃ j, x ∈ childrenC_518 j) ∨ ∀ j, x ∈ childrenD_518 j := by decide +kernel
theorem required_exact_518 : required_518 =
    ((Finset.univ.biUnion childrenC_518) ∪ commonEnvelope childrenD_518).erase (4, 6) := by
  exact required_eq_combination childrenC_518 childrenD_518 (4, 6) required_518
    (by decide +kernel) child_required_sub_518 common_sub_518 required_origin_518
theorem envelope_origin_518 : ∀ x ∈ envelope_518,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_518 j := by decide +kernel
theorem envelope_exact_518 : envelope_518 =
    insert (4, 6) (Finset.univ.biUnion childrenD_518) := by
  exact envelope_eq_combination childrenD_518 (4, 6) envelope_518
    pivot_mem_518 child_envelope_sub_518 envelope_origin_518
def checked_518 : CheckedCard where
  required := required_518
  envelope := envelope_518
  height := height_518
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_518
def height_523 : ℕ := 8
def childrenH_523 : Fin 5 → ℕ := ![height_14, height_122, height_136, height_367, height_522]
theorem height_exact_523 : height_523 = 1 + Finset.univ.sup childrenH_523 := by decide +kernel
theorem required_origin_523 : ∀ x ∈ required_523,
    (∃ j, x ∈ childrenC_523 j) ∨ ∀ j, x ∈ childrenD_523 j := by decide +kernel
theorem required_exact_523 : required_523 =
    ((Finset.univ.biUnion childrenC_523) ∪ commonEnvelope childrenD_523).erase (3, 5) := by
  exact required_eq_combination childrenC_523 childrenD_523 (3, 5) required_523
    (by decide +kernel) child_required_sub_523 common_sub_523 required_origin_523
theorem envelope_origin_523 : ∀ x ∈ envelope_523,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_523 j := by decide +kernel
theorem envelope_exact_523 : envelope_523 =
    insert (3, 5) (Finset.univ.biUnion childrenD_523) := by
  exact envelope_eq_combination childrenD_523 (3, 5) envelope_523
    pivot_mem_523 child_envelope_sub_523 envelope_origin_523
def checked_523 : CheckedCard where
  required := required_523
  envelope := envelope_523
  height := height_523
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_523
def height_524 : ℕ := 8
def childrenH_524 : Fin 4 → ℕ := ![height_88, height_213, height_254, height_522]
theorem height_exact_524 : height_524 = 1 + Finset.univ.sup childrenH_524 := by decide +kernel
theorem required_origin_524 : ∀ x ∈ required_524,
    (∃ j, x ∈ childrenC_524 j) ∨ ∀ j, x ∈ childrenD_524 j := by decide +kernel
theorem required_exact_524 : required_524 =
    ((Finset.univ.biUnion childrenC_524) ∪ commonEnvelope childrenD_524).erase (3, 5) := by
  exact required_eq_combination childrenC_524 childrenD_524 (3, 5) required_524
    (by decide +kernel) child_required_sub_524 common_sub_524 required_origin_524
theorem envelope_origin_524 : ∀ x ∈ envelope_524,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_524 j := by decide +kernel
theorem envelope_exact_524 : envelope_524 =
    insert (3, 5) (Finset.univ.biUnion childrenD_524) := by
  exact envelope_eq_combination childrenD_524 (3, 5) envelope_524
    pivot_mem_524 child_envelope_sub_524 envelope_origin_524
def checked_524 : CheckedCard where
  required := required_524
  envelope := envelope_524
  height := height_524
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_524
def height_530_i2 : ℕ := 4
def childrenH_530_i2 : Fin 2 → ℕ := ![height_5, height_20]
theorem height_exact_530_i2 : height_530_i2 = 1 + Finset.univ.sup childrenH_530_i2 := by decide +kernel
theorem required_origin_530_i2 : ∀ x ∈ required_530_i2,
    (∃ j, x ∈ childrenC_530_i2 j) ∨ ∀ j, x ∈ childrenD_530_i2 j := by decide +kernel
theorem required_exact_530_i2 : required_530_i2 =
    ((Finset.univ.biUnion childrenC_530_i2) ∪ commonEnvelope childrenD_530_i2).erase (2, 5) := by
  exact required_eq_combination childrenC_530_i2 childrenD_530_i2 (2, 5) required_530_i2
    (by decide +kernel) child_required_sub_530_i2 common_sub_530_i2 required_origin_530_i2
theorem envelope_origin_530_i2 : ∀ x ∈ envelope_530_i2,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_530_i2 j := by decide +kernel
theorem envelope_exact_530_i2 : envelope_530_i2 =
    insert (2, 5) (Finset.univ.biUnion childrenD_530_i2) := by
  exact envelope_eq_combination childrenD_530_i2 (2, 5) envelope_530_i2
    pivot_mem_530_i2 child_envelope_sub_530_i2 envelope_origin_530_i2
def checked_530_i2 : CheckedCard where
  required := required_530_i2
  envelope := envelope_530_i2
  height := height_530_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_530_i2
def height_530_i1 : ℕ := 5
def childrenH_530_i1 : Fin 2 → ℕ := ![height_51, height_530_i2]
theorem height_exact_530_i1 : height_530_i1 = 1 + Finset.univ.sup childrenH_530_i1 := by decide +kernel
theorem required_origin_530_i1 : ∀ x ∈ required_530_i1,
    (∃ j, x ∈ childrenC_530_i1 j) ∨ ∀ j, x ∈ childrenD_530_i1 j := by decide +kernel
theorem required_exact_530_i1 : required_530_i1 =
    ((Finset.univ.biUnion childrenC_530_i1) ∪ commonEnvelope childrenD_530_i1).erase (3, 2) := by
  exact required_eq_combination childrenC_530_i1 childrenD_530_i1 (3, 2) required_530_i1
    (by decide +kernel) child_required_sub_530_i1 common_sub_530_i1 required_origin_530_i1
theorem envelope_origin_530_i1 : ∀ x ∈ envelope_530_i1,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_530_i1 j := by decide +kernel
theorem envelope_exact_530_i1 : envelope_530_i1 =
    insert (3, 2) (Finset.univ.biUnion childrenD_530_i1) := by
  exact envelope_eq_combination childrenD_530_i1 (3, 2) envelope_530_i1
    pivot_mem_530_i1 child_envelope_sub_530_i1 envelope_origin_530_i1
def checked_530_i1 : CheckedCard where
  required := required_530_i1
  envelope := envelope_530_i1
  height := height_530_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_530_i1
def height_530_i0 : ℕ := 6
def childrenH_530_i0 : Fin 2 → ℕ := ![height_23, height_530_i1]
theorem height_exact_530_i0 : height_530_i0 = 1 + Finset.univ.sup childrenH_530_i0 := by decide +kernel
theorem required_origin_530_i0 : ∀ x ∈ required_530_i0,
    (∃ j, x ∈ childrenC_530_i0 j) ∨ ∀ j, x ∈ childrenD_530_i0 j := by decide +kernel
theorem required_exact_530_i0 : required_530_i0 =
    ((Finset.univ.biUnion childrenC_530_i0) ∪ commonEnvelope childrenD_530_i0).erase (2, 2) := by
  exact required_eq_combination childrenC_530_i0 childrenD_530_i0 (2, 2) required_530_i0
    (by decide +kernel) child_required_sub_530_i0 common_sub_530_i0 required_origin_530_i0
theorem envelope_origin_530_i0 : ∀ x ∈ envelope_530_i0,
    x = (2, 2) ∨ ∃ j, x ∈ childrenD_530_i0 j := by decide +kernel
theorem envelope_exact_530_i0 : envelope_530_i0 =
    insert (2, 2) (Finset.univ.biUnion childrenD_530_i0) := by
  exact envelope_eq_combination childrenD_530_i0 (2, 2) envelope_530_i0
    pivot_mem_530_i0 child_envelope_sub_530_i0 envelope_origin_530_i0
def checked_530_i0 : CheckedCard where
  required := required_530_i0
  envelope := envelope_530_i0
  height := height_530_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_530_i0
def height_530 : ℕ := 8
def childrenH_530 : Fin 4 → ℕ := ![height_72, height_360, height_499, height_530_i0]
theorem height_exact_530 : height_530 = 1 + Finset.univ.sup childrenH_530 := by decide +kernel
theorem required_origin_530 : ∀ x ∈ required_530,
    (∃ j, x ∈ childrenC_530 j) ∨ ∀ j, x ∈ childrenD_530 j := by decide +kernel
theorem required_exact_530 : required_530 =
    ((Finset.univ.biUnion childrenC_530) ∪ commonEnvelope childrenD_530).erase (2, 4) := by
  exact required_eq_combination childrenC_530 childrenD_530 (2, 4) required_530
    (by decide +kernel) child_required_sub_530 common_sub_530 required_origin_530
theorem envelope_origin_530 : ∀ x ∈ envelope_530,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_530 j := by decide +kernel
theorem envelope_exact_530 : envelope_530 =
    insert (2, 4) (Finset.univ.biUnion childrenD_530) := by
  exact envelope_eq_combination childrenD_530 (2, 4) envelope_530
    pivot_mem_530 child_envelope_sub_530 envelope_origin_530
def checked_530 : CheckedCard where
  required := required_530
  envelope := envelope_530
  height := height_530
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_530
def height_532_i0 : ℕ := 7
def childrenH_532_i0 : Fin 4 → ℕ := ![height_19, height_84, height_314, height_521]
theorem height_exact_532_i0 : height_532_i0 = 1 + Finset.univ.sup childrenH_532_i0 := by decide +kernel
theorem required_origin_532_i0 : ∀ x ∈ required_532_i0,
    (∃ j, x ∈ childrenC_532_i0 j) ∨ ∀ j, x ∈ childrenD_532_i0 j := by decide +kernel
theorem required_exact_532_i0 : required_532_i0 =
    ((Finset.univ.biUnion childrenC_532_i0) ∪ commonEnvelope childrenD_532_i0).erase (2, 6) := by
  exact required_eq_combination childrenC_532_i0 childrenD_532_i0 (2, 6) required_532_i0
    (by decide +kernel) child_required_sub_532_i0 common_sub_532_i0 required_origin_532_i0
theorem envelope_origin_532_i0 : ∀ x ∈ envelope_532_i0,
    x = (2, 6) ∨ ∃ j, x ∈ childrenD_532_i0 j := by decide +kernel
theorem envelope_exact_532_i0 : envelope_532_i0 =
    insert (2, 6) (Finset.univ.biUnion childrenD_532_i0) := by
  exact envelope_eq_combination childrenD_532_i0 (2, 6) envelope_532_i0
    pivot_mem_532_i0 child_envelope_sub_532_i0 envelope_origin_532_i0
def checked_532_i0 : CheckedCard where
  required := required_532_i0
  envelope := envelope_532_i0
  height := height_532_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_532_i0
def height_532 : ℕ := 8
def childrenH_532 : Fin 4 → ℕ := ![height_44, height_52, height_134, height_532_i0]
theorem height_exact_532 : height_532 = 1 + Finset.univ.sup childrenH_532 := by decide +kernel
theorem required_origin_532 : ∀ x ∈ required_532,
    (∃ j, x ∈ childrenC_532 j) ∨ ∀ j, x ∈ childrenD_532 j := by decide +kernel
theorem required_exact_532 : required_532 =
    ((Finset.univ.biUnion childrenC_532) ∪ commonEnvelope childrenD_532).erase (2, 3) := by
  exact required_eq_combination childrenC_532 childrenD_532 (2, 3) required_532
    (by decide +kernel) child_required_sub_532 common_sub_532 required_origin_532
theorem envelope_origin_532 : ∀ x ∈ envelope_532,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_532 j := by decide +kernel
theorem envelope_exact_532 : envelope_532 =
    insert (2, 3) (Finset.univ.biUnion childrenD_532) := by
  exact envelope_eq_combination childrenD_532 (2, 3) envelope_532
    pivot_mem_532 child_envelope_sub_532 envelope_origin_532
def checked_532 : CheckedCard where
  required := required_532
  envelope := envelope_532
  height := height_532
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_532
def height_533_i0 : ℕ := 7
def childrenH_533_i0 : Fin 3 → ℕ := ![height_53, height_55, height_392]
theorem height_exact_533_i0 : height_533_i0 = 1 + Finset.univ.sup childrenH_533_i0 := by decide +kernel
theorem required_origin_533_i0 : ∀ x ∈ required_533_i0,
    (∃ j, x ∈ childrenC_533_i0 j) ∨ ∀ j, x ∈ childrenD_533_i0 j := by decide +kernel
theorem required_exact_533_i0 : required_533_i0 =
    ((Finset.univ.biUnion childrenC_533_i0) ∪ commonEnvelope childrenD_533_i0).erase (3, 4) := by
  exact required_eq_combination childrenC_533_i0 childrenD_533_i0 (3, 4) required_533_i0
    (by decide +kernel) child_required_sub_533_i0 common_sub_533_i0 required_origin_533_i0
theorem envelope_origin_533_i0 : ∀ x ∈ envelope_533_i0,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_533_i0 j := by decide +kernel
theorem envelope_exact_533_i0 : envelope_533_i0 =
    insert (3, 4) (Finset.univ.biUnion childrenD_533_i0) := by
  exact envelope_eq_combination childrenD_533_i0 (3, 4) envelope_533_i0
    pivot_mem_533_i0 child_envelope_sub_533_i0 envelope_origin_533_i0
def checked_533_i0 : CheckedCard where
  required := required_533_i0
  envelope := envelope_533_i0
  height := height_533_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_533_i0
def height_533 : ℕ := 8
def childrenH_533 : Fin 3 → ℕ := ![height_11, height_279, height_533_i0]
theorem height_exact_533 : height_533 = 1 + Finset.univ.sup childrenH_533 := by decide +kernel
theorem required_origin_533 : ∀ x ∈ required_533,
    (∃ j, x ∈ childrenC_533 j) ∨ ∀ j, x ∈ childrenD_533 j := by decide +kernel
theorem required_exact_533 : required_533 =
    ((Finset.univ.biUnion childrenC_533) ∪ commonEnvelope childrenD_533).erase (4, 3) := by
  exact required_eq_combination childrenC_533 childrenD_533 (4, 3) required_533
    (by decide +kernel) child_required_sub_533 common_sub_533 required_origin_533
theorem envelope_origin_533 : ∀ x ∈ envelope_533,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_533 j := by decide +kernel
theorem envelope_exact_533 : envelope_533 =
    insert (4, 3) (Finset.univ.biUnion childrenD_533) := by
  exact envelope_eq_combination childrenD_533 (4, 3) envelope_533
    pivot_mem_533 child_envelope_sub_533 envelope_origin_533
def checked_533 : CheckedCard where
  required := required_533
  envelope := envelope_533
  height := height_533
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_533
def height_534_i1 : ℕ := 4
def childrenH_534_i1 : Fin 2 → ℕ := ![height_5, height_177]
theorem height_exact_534_i1 : height_534_i1 = 1 + Finset.univ.sup childrenH_534_i1 := by decide +kernel
theorem required_origin_534_i1 : ∀ x ∈ required_534_i1,
    (∃ j, x ∈ childrenC_534_i1 j) ∨ ∀ j, x ∈ childrenD_534_i1 j := by decide +kernel
theorem required_exact_534_i1 : required_534_i1 =
    ((Finset.univ.biUnion childrenC_534_i1) ∪ commonEnvelope childrenD_534_i1).erase (2, 6) := by
  exact required_eq_combination childrenC_534_i1 childrenD_534_i1 (2, 6) required_534_i1
    (by decide +kernel) child_required_sub_534_i1 common_sub_534_i1 required_origin_534_i1
theorem envelope_origin_534_i1 : ∀ x ∈ envelope_534_i1,
    x = (2, 6) ∨ ∃ j, x ∈ childrenD_534_i1 j := by decide +kernel
theorem envelope_exact_534_i1 : envelope_534_i1 =
    insert (2, 6) (Finset.univ.biUnion childrenD_534_i1) := by
  exact envelope_eq_combination childrenD_534_i1 (2, 6) envelope_534_i1
    pivot_mem_534_i1 child_envelope_sub_534_i1 envelope_origin_534_i1
def checked_534_i1 : CheckedCard where
  required := required_534_i1
  envelope := envelope_534_i1
  height := height_534_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_534_i1
def height_534_i2 : ℕ := 4
def childrenH_534_i2 : Fin 2 → ℕ := ![height_0, height_239]
theorem height_exact_534_i2 : height_534_i2 = 1 + Finset.univ.sup childrenH_534_i2 := by decide +kernel
theorem required_origin_534_i2 : ∀ x ∈ required_534_i2,
    (∃ j, x ∈ childrenC_534_i2 j) ∨ ∀ j, x ∈ childrenD_534_i2 j := by decide +kernel
theorem required_exact_534_i2 : required_534_i2 =
    ((Finset.univ.biUnion childrenC_534_i2) ∪ commonEnvelope childrenD_534_i2).erase (3, 5) := by
  exact required_eq_combination childrenC_534_i2 childrenD_534_i2 (3, 5) required_534_i2
    (by decide +kernel) child_required_sub_534_i2 common_sub_534_i2 required_origin_534_i2
theorem envelope_origin_534_i2 : ∀ x ∈ envelope_534_i2,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_534_i2 j := by decide +kernel
theorem envelope_exact_534_i2 : envelope_534_i2 =
    insert (3, 5) (Finset.univ.biUnion childrenD_534_i2) := by
  exact envelope_eq_combination childrenD_534_i2 (3, 5) envelope_534_i2
    pivot_mem_534_i2 child_envelope_sub_534_i2 envelope_origin_534_i2
def checked_534_i2 : CheckedCard where
  required := required_534_i2
  envelope := envelope_534_i2
  height := height_534_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_534_i2
def height_534_i0 : ℕ := 5
def childrenH_534_i0 : Fin 3 → ℕ := ![height_139, height_534_i1, height_534_i2]
theorem height_exact_534_i0 : height_534_i0 = 1 + Finset.univ.sup childrenH_534_i0 := by decide +kernel
theorem required_origin_534_i0 : ∀ x ∈ required_534_i0,
    (∃ j, x ∈ childrenC_534_i0 j) ∨ ∀ j, x ∈ childrenD_534_i0 j := by decide +kernel
theorem required_exact_534_i0 : required_534_i0 =
    ((Finset.univ.biUnion childrenC_534_i0) ∪ commonEnvelope childrenD_534_i0).erase (3, 6) := by
  exact required_eq_combination childrenC_534_i0 childrenD_534_i0 (3, 6) required_534_i0
    (by decide +kernel) child_required_sub_534_i0 common_sub_534_i0 required_origin_534_i0
theorem envelope_origin_534_i0 : ∀ x ∈ envelope_534_i0,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_534_i0 j := by decide +kernel
theorem envelope_exact_534_i0 : envelope_534_i0 =
    insert (3, 6) (Finset.univ.biUnion childrenD_534_i0) := by
  exact envelope_eq_combination childrenD_534_i0 (3, 6) envelope_534_i0
    pivot_mem_534_i0 child_envelope_sub_534_i0 envelope_origin_534_i0
def checked_534_i0 : CheckedCard where
  required := required_534_i0
  envelope := envelope_534_i0
  height := height_534_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_534_i0
def height_534 : ℕ := 8
def childrenH_534 : Fin 4 → ℕ := ![height_44, height_52, height_388, height_534_i0]
theorem height_exact_534 : height_534 = 1 + Finset.univ.sup childrenH_534 := by decide +kernel
theorem required_origin_534 : ∀ x ∈ required_534,
    (∃ j, x ∈ childrenC_534 j) ∨ ∀ j, x ∈ childrenD_534 j := by decide +kernel
theorem required_exact_534 : required_534 =
    ((Finset.univ.biUnion childrenC_534) ∪ commonEnvelope childrenD_534).erase (2, 5) := by
  exact required_eq_combination childrenC_534 childrenD_534 (2, 5) required_534
    (by decide +kernel) child_required_sub_534 common_sub_534 required_origin_534
theorem envelope_origin_534 : ∀ x ∈ envelope_534,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_534 j := by decide +kernel
theorem envelope_exact_534 : envelope_534 =
    insert (2, 5) (Finset.univ.biUnion childrenD_534) := by
  exact envelope_eq_combination childrenD_534 (2, 5) envelope_534
    pivot_mem_534 child_envelope_sub_534 envelope_origin_534
def checked_534 : CheckedCard where
  required := required_534
  envelope := envelope_534
  height := height_534
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_534
def height_547_i0 : ℕ := 5
def childrenH_547_i0 : Fin 2 → ℕ := ![height_6, height_17]
theorem height_exact_547_i0 : height_547_i0 = 1 + Finset.univ.sup childrenH_547_i0 := by decide +kernel
theorem required_origin_547_i0 : ∀ x ∈ required_547_i0,
    (∃ j, x ∈ childrenC_547_i0 j) ∨ ∀ j, x ∈ childrenD_547_i0 j := by decide +kernel
theorem required_exact_547_i0 : required_547_i0 =
    ((Finset.univ.biUnion childrenC_547_i0) ∪ commonEnvelope childrenD_547_i0).erase (1, 5) := by
  exact required_eq_combination childrenC_547_i0 childrenD_547_i0 (1, 5) required_547_i0
    (by decide +kernel) child_required_sub_547_i0 common_sub_547_i0 required_origin_547_i0
theorem envelope_origin_547_i0 : ∀ x ∈ envelope_547_i0,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_547_i0 j := by decide +kernel
theorem envelope_exact_547_i0 : envelope_547_i0 =
    insert (1, 5) (Finset.univ.biUnion childrenD_547_i0) := by
  exact envelope_eq_combination childrenD_547_i0 (1, 5) envelope_547_i0
    pivot_mem_547_i0 child_envelope_sub_547_i0 envelope_origin_547_i0
def checked_547_i0 : CheckedCard where
  required := required_547_i0
  envelope := envelope_547_i0
  height := height_547_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_547_i0
def height_547_i1 : ℕ := 7
def childrenH_547_i1 : Fin 2 → ℕ := ![height_5, height_525]
theorem height_exact_547_i1 : height_547_i1 = 1 + Finset.univ.sup childrenH_547_i1 := by decide +kernel
theorem required_origin_547_i1 : ∀ x ∈ required_547_i1,
    (∃ j, x ∈ childrenC_547_i1 j) ∨ ∀ j, x ∈ childrenD_547_i1 j := by decide +kernel
theorem required_exact_547_i1 : required_547_i1 =
    ((Finset.univ.biUnion childrenC_547_i1) ∪ commonEnvelope childrenD_547_i1).erase (2, 4) := by
  exact required_eq_combination childrenC_547_i1 childrenD_547_i1 (2, 4) required_547_i1
    (by decide +kernel) child_required_sub_547_i1 common_sub_547_i1 required_origin_547_i1
theorem envelope_origin_547_i1 : ∀ x ∈ envelope_547_i1,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_547_i1 j := by decide +kernel
theorem envelope_exact_547_i1 : envelope_547_i1 =
    insert (2, 4) (Finset.univ.biUnion childrenD_547_i1) := by
  exact envelope_eq_combination childrenD_547_i1 (2, 4) envelope_547_i1
    pivot_mem_547_i1 child_envelope_sub_547_i1 envelope_origin_547_i1
def checked_547_i1 : CheckedCard where
  required := required_547_i1
  envelope := envelope_547_i1
  height := height_547_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_547_i1
def height_547 : ℕ := 8
def childrenH_547 : Fin 4 → ℕ := ![height_19, height_314, height_547_i0, height_547_i1]
theorem height_exact_547 : height_547 = 1 + Finset.univ.sup childrenH_547 := by decide +kernel
theorem required_origin_547 : ∀ x ∈ required_547,
    (∃ j, x ∈ childrenC_547 j) ∨ ∀ j, x ∈ childrenD_547 j := by decide +kernel
theorem required_exact_547 : required_547 =
    ((Finset.univ.biUnion childrenC_547) ∪ commonEnvelope childrenD_547).erase (1, 4) := by
  exact required_eq_combination childrenC_547 childrenD_547 (1, 4) required_547
    (by decide +kernel) child_required_sub_547 common_sub_547 required_origin_547
theorem envelope_origin_547 : ∀ x ∈ envelope_547,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_547 j := by decide +kernel
theorem envelope_exact_547 : envelope_547 =
    insert (1, 4) (Finset.univ.biUnion childrenD_547) := by
  exact envelope_eq_combination childrenD_547 (1, 4) envelope_547
    pivot_mem_547 child_envelope_sub_547 envelope_origin_547
def checked_547 : CheckedCard where
  required := required_547
  envelope := envelope_547
  height := height_547
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_547
def height_558_i0 : ℕ := 7
def childrenH_558_i0 : Fin 2 → ℕ := ![height_5, height_471]
theorem height_exact_558_i0 : height_558_i0 = 1 + Finset.univ.sup childrenH_558_i0 := by decide +kernel
theorem required_origin_558_i0 : ∀ x ∈ required_558_i0,
    (∃ j, x ∈ childrenC_558_i0 j) ∨ ∀ j, x ∈ childrenD_558_i0 j := by decide +kernel
theorem required_exact_558_i0 : required_558_i0 =
    ((Finset.univ.biUnion childrenC_558_i0) ∪ commonEnvelope childrenD_558_i0).erase (3, 1) := by
  exact required_eq_combination childrenC_558_i0 childrenD_558_i0 (3, 1) required_558_i0
    (by decide +kernel) child_required_sub_558_i0 common_sub_558_i0 required_origin_558_i0
theorem envelope_origin_558_i0 : ∀ x ∈ envelope_558_i0,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_558_i0 j := by decide +kernel
theorem envelope_exact_558_i0 : envelope_558_i0 =
    insert (3, 1) (Finset.univ.biUnion childrenD_558_i0) := by
  exact envelope_eq_combination childrenD_558_i0 (3, 1) envelope_558_i0
    pivot_mem_558_i0 child_envelope_sub_558_i0 envelope_origin_558_i0
def checked_558_i0 : CheckedCard where
  required := required_558_i0
  envelope := envelope_558_i0
  height := height_558_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_558_i0
def height_558 : ℕ := 8
def childrenH_558 : Fin 4 → ℕ := ![height_8, height_16, height_24, height_558_i0]
theorem height_exact_558 : height_558 = 1 + Finset.univ.sup childrenH_558 := by decide +kernel
theorem required_origin_558 : ∀ x ∈ required_558,
    (∃ j, x ∈ childrenC_558 j) ∨ ∀ j, x ∈ childrenD_558 j := by decide +kernel
theorem required_exact_558 : required_558 =
    ((Finset.univ.biUnion childrenC_558) ∪ commonEnvelope childrenD_558).erase (3, 2) := by
  exact required_eq_combination childrenC_558 childrenD_558 (3, 2) required_558
    (by decide +kernel) child_required_sub_558 common_sub_558 required_origin_558
theorem envelope_origin_558 : ∀ x ∈ envelope_558,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_558 j := by decide +kernel
theorem envelope_exact_558 : envelope_558 =
    insert (3, 2) (Finset.univ.biUnion childrenD_558) := by
  exact envelope_eq_combination childrenD_558 (3, 2) envelope_558
    pivot_mem_558 child_envelope_sub_558 envelope_origin_558
def checked_558 : CheckedCard where
  required := required_558
  envelope := envelope_558
  height := height_558
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_558
end SnakyPrototype.Certificate21

end OAI
