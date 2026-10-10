import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part05
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_569_i2 : Finset Cell := ⟨(([(3, 5), (4, 5), (5, 3), (5, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_569_i2 : Finset Cell := ⟨(([(3, 5), (4, 5), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 5), (6, 6), (6, 7), (6, 8), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_569_i2 : Fin 2 → Finset Cell := ![(placed21 0 (3, 5) required_5), (placed21 0 (5, 2) required_54)]
def childrenD_569_i2 : Fin 2 → Finset Cell := ![(placed21 0 (3, 5) envelope_5), (placed21 0 (5, 2) envelope_54)]
theorem common_sub_569_i2 : commonEnvelope childrenD_569_i2 ⊆ insert (6, 6) required_569_i2 := by decide +kernel
theorem child_required_sub_569_i2 : ∀ j, childrenC_569_i2 j ⊆ insert (6, 6) required_569_i2 := by decide +kernel
theorem child_envelope_sub_569_i2 : ∀ j, childrenD_569_i2 j ⊆ envelope_569_i2 := by decide +kernel
theorem pivot_mem_569_i2 : (6, 6) ∈ envelope_569_i2 := by decide +kernel
theorem children_work_569_i2 : ∀ j, Template HasSnaky 3 (childrenC_569_i2 j) (childrenD_569_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (3, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_54 0 (5, 2)).mono (by decide +kernel)
theorem row_works_569_i2 : Template HasSnaky 4 required_569_i2 envelope_569_i2 := by
  refine compose HasSnaky 3 childrenC_569_i2 childrenD_569_i2 children_work_569_i2 (6, 6)
    required_569_i2 envelope_569_i2 pivot_mem_569_i2 child_required_sub_569_i2 child_envelope_sub_569_i2 ?_
  intro b hb
  exact common_sub_569_i2 (mem_commonEnvelope childrenD_569_i2 b hb)
def required_569_i1 : Finset Cell := ⟨(([(0, 2), (3, 2), (3, 3), (3, 5), (4, 3), (4, 5), (5, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_569_i1 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (3, 2), (3, 3), (3, 5), (4, 3), (4, 5), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 3), (6, 5), (6, 6), (6, 7), (6, 8), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_569_i1 : Fin 2 → Finset Cell := ![(placed21 1 (0, 2) required_68), required_569_i2]
def childrenD_569_i1 : Fin 2 → Finset Cell := ![(placed21 1 (0, 2) envelope_68), envelope_569_i2]
theorem common_sub_569_i1 : commonEnvelope childrenD_569_i1 ⊆ insert (5, 3) required_569_i1 := by decide +kernel
theorem child_required_sub_569_i1 : ∀ j, childrenC_569_i1 j ⊆ insert (5, 3) required_569_i1 := by decide +kernel
theorem child_envelope_sub_569_i1 : ∀ j, childrenD_569_i1 j ⊆ envelope_569_i1 := by decide +kernel
theorem pivot_mem_569_i1 : (5, 3) ∈ envelope_569_i1 := by decide +kernel
theorem children_work_569_i1 : ∀ j, Template HasSnaky 4 (childrenC_569_i1 j) (childrenD_569_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_68 1 (0, 2)).mono (by decide +kernel)
  · exact row_works_569_i2.mono (by decide +kernel)
theorem row_works_569_i1 : Template HasSnaky 5 required_569_i1 envelope_569_i1 := by
  refine compose HasSnaky 4 childrenC_569_i1 childrenD_569_i1 children_work_569_i1 (5, 3)
    required_569_i1 envelope_569_i1 pivot_mem_569_i1 child_required_sub_569_i1 child_envelope_sub_569_i1 ?_
  intro b hb
  exact common_sub_569_i1 (mem_commonEnvelope childrenD_569_i1 b hb)
def required_569_i3 : Finset Cell := ⟨(([(0, 2), (3, 2), (3, 3), (3, 5), (4, 3), (4, 5), (5, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_569_i3 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (3, 2), (3, 3), (3, 5), (4, 3), (4, 5), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_569_i3 : Fin 2 → Finset Cell := ![(placed21 7 (6, 3) required_169), (placed21 4 (3, 6) required_202)]
def childrenD_569_i3 : Fin 2 → Finset Cell := ![(placed21 7 (6, 3) envelope_169), (placed21 4 (3, 6) envelope_202)]
theorem common_sub_569_i3 : commonEnvelope childrenD_569_i3 ⊆ insert (6, 3) required_569_i3 := by decide +kernel
theorem child_required_sub_569_i3 : ∀ j, childrenC_569_i3 j ⊆ insert (6, 3) required_569_i3 := by decide +kernel
theorem child_envelope_sub_569_i3 : ∀ j, childrenD_569_i3 j ⊆ envelope_569_i3 := by decide +kernel
theorem pivot_mem_569_i3 : (6, 3) ∈ envelope_569_i3 := by decide +kernel
theorem children_work_569_i3 : ∀ j, Template HasSnaky 5 (childrenC_569_i3 j) (childrenD_569_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_169 7 (6, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_202 4 (3, 6)).mono (by decide +kernel)
theorem row_works_569_i3 : Template HasSnaky 6 required_569_i3 envelope_569_i3 := by
  refine compose HasSnaky 5 childrenC_569_i3 childrenD_569_i3 children_work_569_i3 (6, 3)
    required_569_i3 envelope_569_i3 pivot_mem_569_i3 child_required_sub_569_i3 child_envelope_sub_569_i3 ?_
  intro b hb
  exact common_sub_569_i3 (mem_commonEnvelope childrenD_569_i3 b hb)
def required_569_i0 : Finset Cell := ⟨(([(0, 2), (3, 2), (3, 3), (3, 5), (4, 3), (4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_569_i0 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (3, 2), (3, 3), (3, 5), (4, 3), (4, 5), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 4), (7, 5), (7, 6), (8, 4), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_569_i0 : Fin 3 → Finset Cell := ![(placed21 0 (3, 4) required_8), required_569_i1, required_569_i3]
def childrenD_569_i0 : Fin 3 → Finset Cell := ![(placed21 0 (3, 4) envelope_8), envelope_569_i1, envelope_569_i3]
theorem common_sub_569_i0 : commonEnvelope childrenD_569_i0 ⊆ insert (6, 5) required_569_i0 := by decide +kernel
theorem child_required_sub_569_i0 : ∀ j, childrenC_569_i0 j ⊆ insert (6, 5) required_569_i0 := by decide +kernel
theorem child_envelope_sub_569_i0 : ∀ j, childrenD_569_i0 j ⊆ envelope_569_i0 := by decide +kernel
theorem pivot_mem_569_i0 : (6, 5) ∈ envelope_569_i0 := by decide +kernel
theorem children_work_569_i0 : ∀ j, Template HasSnaky 6 (childrenC_569_i0 j) (childrenD_569_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 0 (3, 4)).mono (by decide +kernel)
  · exact row_works_569_i1.mono (by decide +kernel)
  · exact row_works_569_i3.mono (by decide +kernel)
theorem row_works_569_i0 : Template HasSnaky 7 required_569_i0 envelope_569_i0 := by
  refine compose HasSnaky 6 childrenC_569_i0 childrenD_569_i0 children_work_569_i0 (6, 5)
    required_569_i0 envelope_569_i0 pivot_mem_569_i0 child_required_sub_569_i0 child_envelope_sub_569_i0 ?_
  intro b hb
  exact common_sub_569_i0 (mem_commonEnvelope childrenD_569_i0 b hb)
def required_569_i4 : Finset Cell := ⟨(([(0, 2), (3, 2), (3, 3), (4, 3), (4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_569_i4 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 1), (6, 2), (6, 3), (6, 6), (6, 7), (6, 8), (7, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_569_i4 : Fin 2 → Finset Cell := ![(placed21 1 (0, 2) required_68), (placed21 0 (3, 0) required_495)]
def childrenD_569_i4 : Fin 2 → Finset Cell := ![(placed21 1 (0, 2) envelope_68), (placed21 0 (3, 0) envelope_495)]
theorem common_sub_569_i4 : commonEnvelope childrenD_569_i4 ⊆ insert (5, 3) required_569_i4 := by decide +kernel
theorem child_required_sub_569_i4 : ∀ j, childrenC_569_i4 j ⊆ insert (5, 3) required_569_i4 := by decide +kernel
theorem child_envelope_sub_569_i4 : ∀ j, childrenD_569_i4 j ⊆ envelope_569_i4 := by decide +kernel
theorem pivot_mem_569_i4 : (5, 3) ∈ envelope_569_i4 := by decide +kernel
theorem children_work_569_i4 : ∀ j, Template HasSnaky 5 (childrenC_569_i4 j) (childrenD_569_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_68 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_495 0 (3, 0)).mono (by decide +kernel)
theorem row_works_569_i4 : Template HasSnaky 6 required_569_i4 envelope_569_i4 := by
  refine compose HasSnaky 5 childrenC_569_i4 childrenD_569_i4 children_work_569_i4 (5, 3)
    required_569_i4 envelope_569_i4 pivot_mem_569_i4 child_required_sub_569_i4 child_envelope_sub_569_i4 ?_
  intro b hb
  exact common_sub_569_i4 (mem_commonEnvelope childrenD_569_i4 b hb)
def required_569_i6 : Finset Cell := ⟨(([(0, 2), (3, 2), (3, 3), (3, 5), (4, 3), (4, 5), (5, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_569_i6 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (3, 2), (3, 3), (3, 5), (4, 3), (4, 5), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 2), (6, 3), (6, 4), (6, 5), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_569_i6 : Fin 2 → Finset Cell := ![(placed21 0 (3, 2) required_99), (placed21 7 (6, 3) required_169)]
def childrenD_569_i6 : Fin 2 → Finset Cell := ![(placed21 0 (3, 2) envelope_99), (placed21 7 (6, 3) envelope_169)]
theorem common_sub_569_i6 : commonEnvelope childrenD_569_i6 ⊆ insert (6, 3) required_569_i6 := by decide +kernel
theorem child_required_sub_569_i6 : ∀ j, childrenC_569_i6 j ⊆ insert (6, 3) required_569_i6 := by decide +kernel
theorem child_envelope_sub_569_i6 : ∀ j, childrenD_569_i6 j ⊆ envelope_569_i6 := by decide +kernel
theorem pivot_mem_569_i6 : (6, 3) ∈ envelope_569_i6 := by decide +kernel
theorem children_work_569_i6 : ∀ j, Template HasSnaky 4 (childrenC_569_i6 j) (childrenD_569_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_99 0 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_169 7 (6, 3)).mono (by decide +kernel)
theorem row_works_569_i6 : Template HasSnaky 5 required_569_i6 envelope_569_i6 := by
  refine compose HasSnaky 4 childrenC_569_i6 childrenD_569_i6 children_work_569_i6 (6, 3)
    required_569_i6 envelope_569_i6 pivot_mem_569_i6 child_required_sub_569_i6 child_envelope_sub_569_i6 ?_
  intro b hb
  exact common_sub_569_i6 (mem_commonEnvelope childrenD_569_i6 b hb)
def required_569_i7 : Finset Cell := ⟨(([(0, 2), (3, 2), (3, 3), (3, 5), (4, 3), (4, 5), (5, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_569_i7 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (2, 6), (3, 2), (3, 3), (3, 5), (3, 6), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 3), (6, 5), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_569_i7 : Fin 2 → Finset Cell := ![(placed21 1 (2, 5) required_11), (placed21 1 (0, 2) required_288)]
def childrenD_569_i7 : Fin 2 → Finset Cell := ![(placed21 1 (2, 5) envelope_11), (placed21 1 (0, 2) envelope_288)]
theorem common_sub_569_i7 : commonEnvelope childrenD_569_i7 ⊆ insert (4, 6) required_569_i7 := by decide +kernel
theorem child_required_sub_569_i7 : ∀ j, childrenC_569_i7 j ⊆ insert (4, 6) required_569_i7 := by decide +kernel
theorem child_envelope_sub_569_i7 : ∀ j, childrenD_569_i7 j ⊆ envelope_569_i7 := by decide +kernel
theorem pivot_mem_569_i7 : (4, 6) ∈ envelope_569_i7 := by decide +kernel
theorem children_work_569_i7 : ∀ j, Template HasSnaky 4 (childrenC_569_i7 j) (childrenD_569_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 1 (2, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_288 1 (0, 2)).mono (by decide +kernel)
theorem row_works_569_i7 : Template HasSnaky 5 required_569_i7 envelope_569_i7 := by
  refine compose HasSnaky 4 childrenC_569_i7 childrenD_569_i7 children_work_569_i7 (4, 6)
    required_569_i7 envelope_569_i7 pivot_mem_569_i7 child_required_sub_569_i7 child_envelope_sub_569_i7 ?_
  intro b hb
  exact common_sub_569_i7 (mem_commonEnvelope childrenD_569_i7 b hb)
def required_569_i5 : Finset Cell := ⟨(([(0, 2), (3, 2), (3, 3), (3, 5), (4, 3), (4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_569_i5 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (2, 6), (3, 2), (3, 3), (3, 5), (3, 6), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 2), (6, 3), (6, 4), (6, 5), (7, 4), (7, 5), (8, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_569_i5 : Fin 3 → Finset Cell := ![(placed21 3 (2, 6) required_9), required_569_i6, required_569_i7]
def childrenD_569_i5 : Fin 3 → Finset Cell := ![(placed21 3 (2, 6) envelope_9), envelope_569_i6, envelope_569_i7]
theorem common_sub_569_i5 : commonEnvelope childrenD_569_i5 ⊆ insert (6, 5) required_569_i5 := by decide +kernel
theorem child_required_sub_569_i5 : ∀ j, childrenC_569_i5 j ⊆ insert (6, 5) required_569_i5 := by decide +kernel
theorem child_envelope_sub_569_i5 : ∀ j, childrenD_569_i5 j ⊆ envelope_569_i5 := by decide +kernel
theorem pivot_mem_569_i5 : (6, 5) ∈ envelope_569_i5 := by decide +kernel
theorem children_work_569_i5 : ∀ j, Template HasSnaky 5 (childrenC_569_i5 j) (childrenD_569_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_9 3 (2, 6)).mono (by decide +kernel)
  · exact row_works_569_i6.mono (by decide +kernel)
  · exact row_works_569_i7.mono (by decide +kernel)
theorem row_works_569_i5 : Template HasSnaky 6 required_569_i5 envelope_569_i5 := by
  refine compose HasSnaky 5 childrenC_569_i5 childrenD_569_i5 children_work_569_i5 (6, 5)
    required_569_i5 envelope_569_i5 pivot_mem_569_i5 child_required_sub_569_i5 child_envelope_sub_569_i5 ?_
  intro b hb
  exact common_sub_569_i5 (mem_commonEnvelope childrenD_569_i5 b hb)
def required_569 : Finset Cell := ⟨(([(0, 2), (3, 2), (3, 3), (3, 5), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_569 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (2, 6), (3, 2), (3, 3), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 4), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_569 : Fin 6 → Finset Cell := ![(placed21 1 (0, 2) required_287), (placed21 4 (2, 9) required_322), (placed21 1 (2, 4) required_457), required_569_i0, required_569_i4, required_569_i5]
def childrenD_569 : Fin 6 → Finset Cell := ![(placed21 1 (0, 2) envelope_287), (placed21 4 (2, 9) envelope_322), (placed21 1 (2, 4) envelope_457), envelope_569_i0, envelope_569_i4, envelope_569_i5]
theorem common_sub_569 : commonEnvelope childrenD_569 ⊆ insert (5, 5) required_569 := by decide +kernel
theorem child_required_sub_569 : ∀ j, childrenC_569 j ⊆ insert (5, 5) required_569 := by decide +kernel
theorem child_envelope_sub_569 : ∀ j, childrenD_569 j ⊆ envelope_569 := by decide +kernel
theorem pivot_mem_569 : (5, 5) ∈ envelope_569 := by decide +kernel
theorem children_work_569 : ∀ j, Template HasSnaky 9 (childrenC_569 j) (childrenD_569 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_287 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_322 4 (2, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_457 1 (2, 4)).mono (by decide +kernel)
  · exact row_works_569_i0.mono (by decide +kernel)
  · exact row_works_569_i4.mono (by decide +kernel)
  · exact row_works_569_i5.mono (by decide +kernel)
theorem row_works_569 : Template HasSnaky 10 required_569 envelope_569 := by
  refine compose HasSnaky 9 childrenC_569 childrenD_569 children_work_569 (5, 5)
    required_569 envelope_569 pivot_mem_569 child_required_sub_569 child_envelope_sub_569 ?_
  intro b hb
  exact common_sub_569 (mem_commonEnvelope childrenD_569 b hb)
def required_575_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (3, 4), (4, 4), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_575_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (2, 4), (3, 4), (4, 4), (5, 3), (5, 4), (5, 5), (6, 3), (6, 4), (6, 5), (7, 3), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_575_i0 : Fin 2 → Finset Cell := ![(placed21 6 (4, 4) required_3), (placed21 0 (2, 3) required_8)]
def childrenD_575_i0 : Fin 2 → Finset Cell := ![(placed21 6 (4, 4) envelope_3), (placed21 0 (2, 3) envelope_8)]
theorem common_sub_575_i0 : commonEnvelope childrenD_575_i0 ⊆ insert (2, 4) required_575_i0 := by decide +kernel
theorem child_required_sub_575_i0 : ∀ j, childrenC_575_i0 j ⊆ insert (2, 4) required_575_i0 := by decide +kernel
theorem child_envelope_sub_575_i0 : ∀ j, childrenD_575_i0 j ⊆ envelope_575_i0 := by decide +kernel
theorem pivot_mem_575_i0 : (2, 4) ∈ envelope_575_i0 := by decide +kernel
theorem children_work_575_i0 : ∀ j, Template HasSnaky 3 (childrenC_575_i0 j) (childrenD_575_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 6 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 0 (2, 3)).mono (by decide +kernel)
theorem row_works_575_i0 : Template HasSnaky 4 required_575_i0 envelope_575_i0 := by
  refine compose HasSnaky 3 childrenC_575_i0 childrenD_575_i0 children_work_575_i0 (2, 4)
    required_575_i0 envelope_575_i0 pivot_mem_575_i0 child_required_sub_575_i0 child_envelope_sub_575_i0 ?_
  intro b hb
  exact common_sub_575_i0 (mem_commonEnvelope childrenD_575_i0 b hb)
def required_575_i2 : Finset Cell := ⟨(([(0, 3), (1, 3), (3, 4), (4, 4), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_575_i2 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (2, 4), (3, 4), (4, 4), (5, 3), (5, 4), (6, 3), (6, 4), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_575_i2 : Fin 2 → Finset Cell := ![(placed21 6 (4, 4) required_3), (placed21 3 (2, 4) required_6)]
def childrenD_575_i2 : Fin 2 → Finset Cell := ![(placed21 6 (4, 4) envelope_3), (placed21 3 (2, 4) envelope_6)]
theorem common_sub_575_i2 : commonEnvelope childrenD_575_i2 ⊆ insert (2, 4) required_575_i2 := by decide +kernel
theorem child_required_sub_575_i2 : ∀ j, childrenC_575_i2 j ⊆ insert (2, 4) required_575_i2 := by decide +kernel
theorem child_envelope_sub_575_i2 : ∀ j, childrenD_575_i2 j ⊆ envelope_575_i2 := by decide +kernel
theorem pivot_mem_575_i2 : (2, 4) ∈ envelope_575_i2 := by decide +kernel
theorem children_work_575_i2 : ∀ j, Template HasSnaky 2 (childrenC_575_i2 j) (childrenD_575_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 6 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_6 3 (2, 4)).mono (by decide +kernel)
theorem row_works_575_i2 : Template HasSnaky 3 required_575_i2 envelope_575_i2 := by
  refine compose HasSnaky 2 childrenC_575_i2 childrenD_575_i2 children_work_575_i2 (2, 4)
    required_575_i2 envelope_575_i2 pivot_mem_575_i2 child_required_sub_575_i2 child_envelope_sub_575_i2 ?_
  intro b hb
  exact common_sub_575_i2 (mem_commonEnvelope childrenD_575_i2 b hb)
def required_575_i1 : Finset Cell := ⟨(([(0, 3), (0, 6), (1, 3), (1, 6), (3, 4), (4, 4), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_575_i1 : Finset Cell := ⟨(([(0, 3), (0, 6), (1, 3), (1, 4), (1, 6), (1, 7), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (4, 7), (4, 8), (5, 3), (5, 4), (6, 3), (6, 4), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_575_i1 : Fin 2 → Finset Cell := ![required_575_i2, (placed21 5 (7, 4) required_554)]
def childrenD_575_i1 : Fin 2 → Finset Cell := ![envelope_575_i2, (placed21 5 (7, 4) envelope_554)]
theorem common_sub_575_i1 : commonEnvelope childrenD_575_i1 ⊆ insert (6, 4) required_575_i1 := by decide +kernel
theorem child_required_sub_575_i1 : ∀ j, childrenC_575_i1 j ⊆ insert (6, 4) required_575_i1 := by decide +kernel
theorem child_envelope_sub_575_i1 : ∀ j, childrenD_575_i1 j ⊆ envelope_575_i1 := by decide +kernel
theorem pivot_mem_575_i1 : (6, 4) ∈ envelope_575_i1 := by decide +kernel
theorem children_work_575_i1 : ∀ j, Template HasSnaky 7 (childrenC_575_i1 j) (childrenD_575_i1 j) := by
  intro j
  fin_cases j
  · exact row_works_575_i2.mono (by decide +kernel)
  · exact (placed21_template row_works_554 5 (7, 4)).mono (by decide +kernel)
theorem row_works_575_i1 : Template HasSnaky 8 required_575_i1 envelope_575_i1 := by
  refine compose HasSnaky 7 childrenC_575_i1 childrenD_575_i1 children_work_575_i1 (6, 4)
    required_575_i1 envelope_575_i1 pivot_mem_575_i1 child_required_sub_575_i1 child_envelope_sub_575_i1 ?_
  intro b hb
  exact common_sub_575_i1 (mem_commonEnvelope childrenD_575_i1 b hb)
def required_575_i3 : Finset Cell := ⟨(([(0, 3), (0, 6), (1, 3), (1, 6), (3, 4), (4, 4), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_575_i3 : Finset Cell := ⟨(([(0, 3), (0, 6), (1, 3), (1, 4), (1, 6), (1, 7), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (4, 7), (4, 8), (5, 4), (5, 5), (6, 4), (6, 5), (7, 4), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_575_i3 : Fin 2 → Finset Cell := ![(placed21 1 (0, 3) required_280), (placed21 5 (7, 4) required_554)]
def childrenD_575_i3 : Fin 2 → Finset Cell := ![(placed21 1 (0, 3) envelope_280), (placed21 5 (7, 4) envelope_554)]
theorem common_sub_575_i3 : commonEnvelope childrenD_575_i3 ⊆ insert (6, 4) required_575_i3 := by decide +kernel
theorem child_required_sub_575_i3 : ∀ j, childrenC_575_i3 j ⊆ insert (6, 4) required_575_i3 := by decide +kernel
theorem child_envelope_sub_575_i3 : ∀ j, childrenD_575_i3 j ⊆ envelope_575_i3 := by decide +kernel
theorem pivot_mem_575_i3 : (6, 4) ∈ envelope_575_i3 := by decide +kernel
theorem children_work_575_i3 : ∀ j, Template HasSnaky 7 (childrenC_575_i3 j) (childrenD_575_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_280 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_554 5 (7, 4)).mono (by decide +kernel)
theorem row_works_575_i3 : Template HasSnaky 8 required_575_i3 envelope_575_i3 := by
  refine compose HasSnaky 7 childrenC_575_i3 childrenD_575_i3 children_work_575_i3 (6, 4)
    required_575_i3 envelope_575_i3 pivot_mem_575_i3 child_required_sub_575_i3 child_envelope_sub_575_i3 ?_
  intro b hb
  exact common_sub_575_i3 (mem_commonEnvelope childrenD_575_i3 b hb)
def required_575 : Finset Cell := ⟨(([(0, 3), (0, 6), (1, 3), (1, 6), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_575 : Finset Cell := ⟨(([(0, 3), (0, 6), (1, 3), (1, 4), (1, 6), (1, 7), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (8, 3), (8, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_575 : Fin 5 → Finset Cell := ![(placed21 0 (2, 1) required_257), required_326, required_575_i0, required_575_i1, required_575_i3]
def childrenD_575 : Fin 5 → Finset Cell := ![(placed21 0 (2, 1) envelope_257), envelope_326, envelope_575_i0, envelope_575_i1, envelope_575_i3]
theorem common_sub_575 : commonEnvelope childrenD_575 ⊆ insert (5, 4) required_575 := by decide +kernel
theorem child_required_sub_575 : ∀ j, childrenC_575 j ⊆ insert (5, 4) required_575 := by decide +kernel
theorem child_envelope_sub_575 : ∀ j, childrenD_575 j ⊆ envelope_575 := by decide +kernel
theorem pivot_mem_575 : (5, 4) ∈ envelope_575 := by decide +kernel
theorem children_work_575 : ∀ j, Template HasSnaky 9 (childrenC_575 j) (childrenD_575 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_257 0 (2, 1)).mono (by decide +kernel)
  · exact row_works_326.mono (by decide +kernel)
  · exact row_works_575_i0.mono (by decide +kernel)
  · exact row_works_575_i1.mono (by decide +kernel)
  · exact row_works_575_i3.mono (by decide +kernel)
theorem row_works_575 : Template HasSnaky 10 required_575 envelope_575 := by
  refine compose HasSnaky 9 childrenC_575 childrenD_575 children_work_575 (5, 4)
    required_575 envelope_575 pivot_mem_575 child_required_sub_575 child_envelope_sub_575 ?_
  intro b hb
  exact common_sub_575 (mem_commonEnvelope childrenD_575 b hb)
def required_578 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_578 : Finset Cell := ⟨(([(0, 3), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 3), (4, 4), (4, 5), (4, 6), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4), (7, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_578 : Fin 4 → Finset Cell := ![(placed21 0 (1, 2) required_26), (placed21 4 (1, 4) required_49), (placed21 0 (1, 0) required_117), (placed21 0 (0, 1) required_577)]
def childrenD_578 : Fin 4 → Finset Cell := ![(placed21 0 (1, 2) envelope_26), (placed21 4 (1, 4) envelope_49), (placed21 0 (1, 0) envelope_117), (placed21 0 (0, 1) envelope_577)]
theorem common_sub_578 : commonEnvelope childrenD_578 ⊆ insert (4, 3) required_578 := by decide +kernel
theorem child_required_sub_578 : ∀ j, childrenC_578 j ⊆ insert (4, 3) required_578 := by decide +kernel
theorem child_envelope_sub_578 : ∀ j, childrenD_578 j ⊆ envelope_578 := by decide +kernel
theorem pivot_mem_578 : (4, 3) ∈ envelope_578 := by decide +kernel
theorem children_work_578 : ∀ j, Template HasSnaky 9 (childrenC_578 j) (childrenD_578 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_26 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_49 4 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_117 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_577 0 (0, 1)).mono (by decide +kernel)
theorem row_works_578 : Template HasSnaky 10 required_578 envelope_578 := by
  refine compose HasSnaky 9 childrenC_578 childrenD_578 children_work_578 (4, 3)
    required_578 envelope_578 pivot_mem_578 child_required_sub_578 child_envelope_sub_578 ?_
  intro b hb
  exact common_sub_578 (mem_commonEnvelope childrenD_578 b hb)
def required_580 : Finset Cell := ⟨(([(1, 1), (1, 2), (2, 2), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_580 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (6, 1), (6, 2), (6, 3), (7, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_580 : Fin 4 → Finset Cell := ![(placed21 0 (1, 1) required_24), (placed21 4 (1, 3) required_49), (placed21 1 (1, 1) required_194), required_577]
def childrenD_580 : Fin 4 → Finset Cell := ![(placed21 0 (1, 1) envelope_24), (placed21 4 (1, 3) envelope_49), (placed21 1 (1, 1) envelope_194), envelope_577]
theorem common_sub_580 : commonEnvelope childrenD_580 ⊆ insert (4, 2) required_580 := by decide +kernel
theorem child_required_sub_580 : ∀ j, childrenC_580 j ⊆ insert (4, 2) required_580 := by decide +kernel
theorem child_envelope_sub_580 : ∀ j, childrenD_580 j ⊆ envelope_580 := by decide +kernel
theorem pivot_mem_580 : (4, 2) ∈ envelope_580 := by decide +kernel
theorem children_work_580 : ∀ j, Template HasSnaky 9 (childrenC_580 j) (childrenD_580 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_24 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_49 4 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_194 1 (1, 1)).mono (by decide +kernel)
  · exact row_works_577.mono (by decide +kernel)
theorem row_works_580 : Template HasSnaky 10 required_580 envelope_580 := by
  refine compose HasSnaky 9 childrenC_580 childrenD_580 children_work_580 (4, 2)
    required_580 envelope_580 pivot_mem_580 child_required_sub_580 child_envelope_sub_580 ?_
  intro b hb
  exact common_sub_580 (mem_commonEnvelope childrenD_580 b hb)
def required_585_i2 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (2, 2), (3, 2), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_585_i2 : Finset Cell := ⟨(([(0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_585_i2 : Fin 2 → Finset Cell := ![(placed21 0 (1, 0) required_11), (placed21 1 (0, 1) required_358)]
def childrenD_585_i2 : Fin 2 → Finset Cell := ![(placed21 0 (1, 0) envelope_11), (placed21 1 (0, 1) envelope_358)]
theorem common_sub_585_i2 : commonEnvelope childrenD_585_i2 ⊆ insert (1, 4) required_585_i2 := by decide +kernel
theorem child_required_sub_585_i2 : ∀ j, childrenC_585_i2 j ⊆ insert (1, 4) required_585_i2 := by decide +kernel
theorem child_envelope_sub_585_i2 : ∀ j, childrenD_585_i2 j ⊆ envelope_585_i2 := by decide +kernel
theorem pivot_mem_585_i2 : (1, 4) ∈ envelope_585_i2 := by decide +kernel
theorem children_work_585_i2 : ∀ j, Template HasSnaky 6 (childrenC_585_i2 j) (childrenD_585_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_358 1 (0, 1)).mono (by decide +kernel)
theorem row_works_585_i2 : Template HasSnaky 7 required_585_i2 envelope_585_i2 := by
  refine compose HasSnaky 6 childrenC_585_i2 childrenD_585_i2 children_work_585_i2 (1, 4)
    required_585_i2 envelope_585_i2 pivot_mem_585_i2 child_required_sub_585_i2 child_envelope_sub_585_i2 ?_
  intro b hb
  exact common_sub_585_i2 (mem_commonEnvelope childrenD_585_i2 b hb)
def required_585_i1 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (2, 2), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_585_i1 : Finset Cell := ⟨(([(0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_585_i1 : Fin 2 → Finset Cell := ![(placed21 4 (1, 2) required_5), required_585_i2]
def childrenD_585_i1 : Fin 2 → Finset Cell := ![(placed21 4 (1, 2) envelope_5), envelope_585_i2]
theorem common_sub_585_i1 : commonEnvelope childrenD_585_i1 ⊆ insert (4, 1) required_585_i1 := by decide +kernel
theorem child_required_sub_585_i1 : ∀ j, childrenC_585_i1 j ⊆ insert (4, 1) required_585_i1 := by decide +kernel
theorem child_envelope_sub_585_i1 : ∀ j, childrenD_585_i1 j ⊆ envelope_585_i1 := by decide +kernel
theorem pivot_mem_585_i1 : (4, 1) ∈ envelope_585_i1 := by decide +kernel
theorem children_work_585_i1 : ∀ j, Template HasSnaky 7 (childrenC_585_i1 j) (childrenD_585_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (1, 2)).mono (by decide +kernel)
  · exact row_works_585_i2.mono (by decide +kernel)
theorem row_works_585_i1 : Template HasSnaky 8 required_585_i1 envelope_585_i1 := by
  refine compose HasSnaky 7 childrenC_585_i1 childrenD_585_i1 children_work_585_i1 (4, 1)
    required_585_i1 envelope_585_i1 pivot_mem_585_i1 child_required_sub_585_i1 child_envelope_sub_585_i1 ?_
  intro b hb
  exact common_sub_585_i1 (mem_commonEnvelope childrenD_585_i1 b hb)
def required_585_i0 : Finset Cell := ⟨(([(1, 2), (1, 3), (2, 2), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_585_i0 : Finset Cell := ⟨(([(0, 1), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_585_i0 : Fin 2 → Finset Cell := ![(placed21 6 (4, 2) required_5), required_585_i1]
def childrenD_585_i0 : Fin 2 → Finset Cell := ![(placed21 6 (4, 2) envelope_5), envelope_585_i1]
theorem common_sub_585_i0 : commonEnvelope childrenD_585_i0 ⊆ insert (1, 1) required_585_i0 := by decide +kernel
theorem child_required_sub_585_i0 : ∀ j, childrenC_585_i0 j ⊆ insert (1, 1) required_585_i0 := by decide +kernel
theorem child_envelope_sub_585_i0 : ∀ j, childrenD_585_i0 j ⊆ envelope_585_i0 := by decide +kernel
theorem pivot_mem_585_i0 : (1, 1) ∈ envelope_585_i0 := by decide +kernel
theorem children_work_585_i0 : ∀ j, Template HasSnaky 8 (childrenC_585_i0 j) (childrenD_585_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 6 (4, 2)).mono (by decide +kernel)
  · exact row_works_585_i1.mono (by decide +kernel)
theorem row_works_585_i0 : Template HasSnaky 9 required_585_i0 envelope_585_i0 := by
  refine compose HasSnaky 8 childrenC_585_i0 childrenD_585_i0 children_work_585_i0 (1, 1)
    required_585_i0 envelope_585_i0 pivot_mem_585_i0 child_required_sub_585_i0 child_envelope_sub_585_i0 ?_
  intro b hb
  exact common_sub_585_i0 (mem_commonEnvelope childrenD_585_i0 b hb)
def required_585 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_585 : Finset Cell := ⟨(([(0, 1), (0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_585 : Fin 2 → Finset Cell := ![(placed21 2 (4, 2) required_5), required_585_i0]
def childrenD_585 : Fin 2 → Finset Cell := ![(placed21 2 (4, 2) envelope_5), envelope_585_i0]
theorem common_sub_585 : commonEnvelope childrenD_585 ⊆ insert (1, 3) required_585 := by decide +kernel
theorem child_required_sub_585 : ∀ j, childrenC_585 j ⊆ insert (1, 3) required_585 := by decide +kernel
theorem child_envelope_sub_585 : ∀ j, childrenD_585 j ⊆ envelope_585 := by decide +kernel
theorem pivot_mem_585 : (1, 3) ∈ envelope_585 := by decide +kernel
theorem children_work_585 : ∀ j, Template HasSnaky 9 (childrenC_585 j) (childrenD_585 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 2 (4, 2)).mono (by decide +kernel)
  · exact row_works_585_i0.mono (by decide +kernel)
theorem row_works_585 : Template HasSnaky 10 required_585 envelope_585 := by
  refine compose HasSnaky 9 childrenC_585 childrenD_585 children_work_585 (1, 3)
    required_585 envelope_585 pivot_mem_585 child_required_sub_585 child_envelope_sub_585 ?_
  intro b hb
  exact common_sub_585 (mem_commonEnvelope childrenD_585 b hb)
def height_569_i2 : ℕ := 4
def childrenH_569_i2 : Fin 2 → ℕ := ![height_5, height_54]
theorem height_exact_569_i2 : height_569_i2 = 1 + Finset.univ.sup childrenH_569_i2 := by decide +kernel
theorem required_origin_569_i2 : ∀ x ∈ required_569_i2,
    (∃ j, x ∈ childrenC_569_i2 j) ∨ ∀ j, x ∈ childrenD_569_i2 j := by decide +kernel
theorem required_exact_569_i2 : required_569_i2 =
    ((Finset.univ.biUnion childrenC_569_i2) ∪ commonEnvelope childrenD_569_i2).erase (6, 6) := by
  exact required_eq_combination childrenC_569_i2 childrenD_569_i2 (6, 6) required_569_i2
    (by decide +kernel) child_required_sub_569_i2 common_sub_569_i2 required_origin_569_i2
theorem envelope_origin_569_i2 : ∀ x ∈ envelope_569_i2,
    x = (6, 6) ∨ ∃ j, x ∈ childrenD_569_i2 j := by decide +kernel
theorem envelope_exact_569_i2 : envelope_569_i2 =
    insert (6, 6) (Finset.univ.biUnion childrenD_569_i2) := by
  exact envelope_eq_combination childrenD_569_i2 (6, 6) envelope_569_i2
    pivot_mem_569_i2 child_envelope_sub_569_i2 envelope_origin_569_i2
def checked_569_i2 : CheckedCard where
  required := required_569_i2
  envelope := envelope_569_i2
  height := height_569_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_569_i2
def height_569_i1 : ℕ := 5
def childrenH_569_i1 : Fin 2 → ℕ := ![height_68, height_569_i2]
theorem height_exact_569_i1 : height_569_i1 = 1 + Finset.univ.sup childrenH_569_i1 := by decide +kernel
theorem required_origin_569_i1 : ∀ x ∈ required_569_i1,
    (∃ j, x ∈ childrenC_569_i1 j) ∨ ∀ j, x ∈ childrenD_569_i1 j := by decide +kernel
theorem required_exact_569_i1 : required_569_i1 =
    ((Finset.univ.biUnion childrenC_569_i1) ∪ commonEnvelope childrenD_569_i1).erase (5, 3) := by
  exact required_eq_combination childrenC_569_i1 childrenD_569_i1 (5, 3) required_569_i1
    (by decide +kernel) child_required_sub_569_i1 common_sub_569_i1 required_origin_569_i1
theorem envelope_origin_569_i1 : ∀ x ∈ envelope_569_i1,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_569_i1 j := by decide +kernel
theorem envelope_exact_569_i1 : envelope_569_i1 =
    insert (5, 3) (Finset.univ.biUnion childrenD_569_i1) := by
  exact envelope_eq_combination childrenD_569_i1 (5, 3) envelope_569_i1
    pivot_mem_569_i1 child_envelope_sub_569_i1 envelope_origin_569_i1
def checked_569_i1 : CheckedCard where
  required := required_569_i1
  envelope := envelope_569_i1
  height := height_569_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_569_i1
def height_569_i3 : ℕ := 6
def childrenH_569_i3 : Fin 2 → ℕ := ![height_169, height_202]
theorem height_exact_569_i3 : height_569_i3 = 1 + Finset.univ.sup childrenH_569_i3 := by decide +kernel
theorem required_origin_569_i3 : ∀ x ∈ required_569_i3,
    (∃ j, x ∈ childrenC_569_i3 j) ∨ ∀ j, x ∈ childrenD_569_i3 j := by decide +kernel
theorem required_exact_569_i3 : required_569_i3 =
    ((Finset.univ.biUnion childrenC_569_i3) ∪ commonEnvelope childrenD_569_i3).erase (6, 3) := by
  exact required_eq_combination childrenC_569_i3 childrenD_569_i3 (6, 3) required_569_i3
    (by decide +kernel) child_required_sub_569_i3 common_sub_569_i3 required_origin_569_i3
theorem envelope_origin_569_i3 : ∀ x ∈ envelope_569_i3,
    x = (6, 3) ∨ ∃ j, x ∈ childrenD_569_i3 j := by decide +kernel
theorem envelope_exact_569_i3 : envelope_569_i3 =
    insert (6, 3) (Finset.univ.biUnion childrenD_569_i3) := by
  exact envelope_eq_combination childrenD_569_i3 (6, 3) envelope_569_i3
    pivot_mem_569_i3 child_envelope_sub_569_i3 envelope_origin_569_i3
def checked_569_i3 : CheckedCard where
  required := required_569_i3
  envelope := envelope_569_i3
  height := height_569_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_569_i3
def height_569_i0 : ℕ := 7
def childrenH_569_i0 : Fin 3 → ℕ := ![height_8, height_569_i1, height_569_i3]
theorem height_exact_569_i0 : height_569_i0 = 1 + Finset.univ.sup childrenH_569_i0 := by decide +kernel
theorem required_origin_569_i0 : ∀ x ∈ required_569_i0,
    (∃ j, x ∈ childrenC_569_i0 j) ∨ ∀ j, x ∈ childrenD_569_i0 j := by decide +kernel
theorem required_exact_569_i0 : required_569_i0 =
    ((Finset.univ.biUnion childrenC_569_i0) ∪ commonEnvelope childrenD_569_i0).erase (6, 5) := by
  exact required_eq_combination childrenC_569_i0 childrenD_569_i0 (6, 5) required_569_i0
    (by decide +kernel) child_required_sub_569_i0 common_sub_569_i0 required_origin_569_i0
theorem envelope_origin_569_i0 : ∀ x ∈ envelope_569_i0,
    x = (6, 5) ∨ ∃ j, x ∈ childrenD_569_i0 j := by decide +kernel
theorem envelope_exact_569_i0 : envelope_569_i0 =
    insert (6, 5) (Finset.univ.biUnion childrenD_569_i0) := by
  exact envelope_eq_combination childrenD_569_i0 (6, 5) envelope_569_i0
    pivot_mem_569_i0 child_envelope_sub_569_i0 envelope_origin_569_i0
def checked_569_i0 : CheckedCard where
  required := required_569_i0
  envelope := envelope_569_i0
  height := height_569_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_569_i0
def height_569_i4 : ℕ := 6
def childrenH_569_i4 : Fin 2 → ℕ := ![height_68, height_495]
theorem height_exact_569_i4 : height_569_i4 = 1 + Finset.univ.sup childrenH_569_i4 := by decide +kernel
theorem required_origin_569_i4 : ∀ x ∈ required_569_i4,
    (∃ j, x ∈ childrenC_569_i4 j) ∨ ∀ j, x ∈ childrenD_569_i4 j := by decide +kernel
theorem required_exact_569_i4 : required_569_i4 =
    ((Finset.univ.biUnion childrenC_569_i4) ∪ commonEnvelope childrenD_569_i4).erase (5, 3) := by
  exact required_eq_combination childrenC_569_i4 childrenD_569_i4 (5, 3) required_569_i4
    (by decide +kernel) child_required_sub_569_i4 common_sub_569_i4 required_origin_569_i4
theorem envelope_origin_569_i4 : ∀ x ∈ envelope_569_i4,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_569_i4 j := by decide +kernel
theorem envelope_exact_569_i4 : envelope_569_i4 =
    insert (5, 3) (Finset.univ.biUnion childrenD_569_i4) := by
  exact envelope_eq_combination childrenD_569_i4 (5, 3) envelope_569_i4
    pivot_mem_569_i4 child_envelope_sub_569_i4 envelope_origin_569_i4
def checked_569_i4 : CheckedCard where
  required := required_569_i4
  envelope := envelope_569_i4
  height := height_569_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_569_i4
def height_569_i6 : ℕ := 5
def childrenH_569_i6 : Fin 2 → ℕ := ![height_99, height_169]
theorem height_exact_569_i6 : height_569_i6 = 1 + Finset.univ.sup childrenH_569_i6 := by decide +kernel
theorem required_origin_569_i6 : ∀ x ∈ required_569_i6,
    (∃ j, x ∈ childrenC_569_i6 j) ∨ ∀ j, x ∈ childrenD_569_i6 j := by decide +kernel
theorem required_exact_569_i6 : required_569_i6 =
    ((Finset.univ.biUnion childrenC_569_i6) ∪ commonEnvelope childrenD_569_i6).erase (6, 3) := by
  exact required_eq_combination childrenC_569_i6 childrenD_569_i6 (6, 3) required_569_i6
    (by decide +kernel) child_required_sub_569_i6 common_sub_569_i6 required_origin_569_i6
theorem envelope_origin_569_i6 : ∀ x ∈ envelope_569_i6,
    x = (6, 3) ∨ ∃ j, x ∈ childrenD_569_i6 j := by decide +kernel
theorem envelope_exact_569_i6 : envelope_569_i6 =
    insert (6, 3) (Finset.univ.biUnion childrenD_569_i6) := by
  exact envelope_eq_combination childrenD_569_i6 (6, 3) envelope_569_i6
    pivot_mem_569_i6 child_envelope_sub_569_i6 envelope_origin_569_i6
def checked_569_i6 : CheckedCard where
  required := required_569_i6
  envelope := envelope_569_i6
  height := height_569_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_569_i6
def height_569_i7 : ℕ := 5
def childrenH_569_i7 : Fin 2 → ℕ := ![height_11, height_288]
theorem height_exact_569_i7 : height_569_i7 = 1 + Finset.univ.sup childrenH_569_i7 := by decide +kernel
theorem required_origin_569_i7 : ∀ x ∈ required_569_i7,
    (∃ j, x ∈ childrenC_569_i7 j) ∨ ∀ j, x ∈ childrenD_569_i7 j := by decide +kernel
theorem required_exact_569_i7 : required_569_i7 =
    ((Finset.univ.biUnion childrenC_569_i7) ∪ commonEnvelope childrenD_569_i7).erase (4, 6) := by
  exact required_eq_combination childrenC_569_i7 childrenD_569_i7 (4, 6) required_569_i7
    (by decide +kernel) child_required_sub_569_i7 common_sub_569_i7 required_origin_569_i7
theorem envelope_origin_569_i7 : ∀ x ∈ envelope_569_i7,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_569_i7 j := by decide +kernel
theorem envelope_exact_569_i7 : envelope_569_i7 =
    insert (4, 6) (Finset.univ.biUnion childrenD_569_i7) := by
  exact envelope_eq_combination childrenD_569_i7 (4, 6) envelope_569_i7
    pivot_mem_569_i7 child_envelope_sub_569_i7 envelope_origin_569_i7
def checked_569_i7 : CheckedCard where
  required := required_569_i7
  envelope := envelope_569_i7
  height := height_569_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_569_i7
def height_569_i5 : ℕ := 6
def childrenH_569_i5 : Fin 3 → ℕ := ![height_9, height_569_i6, height_569_i7]
theorem height_exact_569_i5 : height_569_i5 = 1 + Finset.univ.sup childrenH_569_i5 := by decide +kernel
theorem required_origin_569_i5 : ∀ x ∈ required_569_i5,
    (∃ j, x ∈ childrenC_569_i5 j) ∨ ∀ j, x ∈ childrenD_569_i5 j := by decide +kernel
theorem required_exact_569_i5 : required_569_i5 =
    ((Finset.univ.biUnion childrenC_569_i5) ∪ commonEnvelope childrenD_569_i5).erase (6, 5) := by
  exact required_eq_combination childrenC_569_i5 childrenD_569_i5 (6, 5) required_569_i5
    (by decide +kernel) child_required_sub_569_i5 common_sub_569_i5 required_origin_569_i5
theorem envelope_origin_569_i5 : ∀ x ∈ envelope_569_i5,
    x = (6, 5) ∨ ∃ j, x ∈ childrenD_569_i5 j := by decide +kernel
theorem envelope_exact_569_i5 : envelope_569_i5 =
    insert (6, 5) (Finset.univ.biUnion childrenD_569_i5) := by
  exact envelope_eq_combination childrenD_569_i5 (6, 5) envelope_569_i5
    pivot_mem_569_i5 child_envelope_sub_569_i5 envelope_origin_569_i5
def checked_569_i5 : CheckedCard where
  required := required_569_i5
  envelope := envelope_569_i5
  height := height_569_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_569_i5
def height_569 : ℕ := 10
def childrenH_569 : Fin 6 → ℕ := ![height_287, height_322, height_457, height_569_i0, height_569_i4, height_569_i5]
theorem height_exact_569 : height_569 = 1 + Finset.univ.sup childrenH_569 := by decide +kernel
theorem required_origin_569 : ∀ x ∈ required_569,
    (∃ j, x ∈ childrenC_569 j) ∨ ∀ j, x ∈ childrenD_569 j := by decide +kernel
theorem required_exact_569 : required_569 =
    ((Finset.univ.biUnion childrenC_569) ∪ commonEnvelope childrenD_569).erase (5, 5) := by
  exact required_eq_combination childrenC_569 childrenD_569 (5, 5) required_569
    (by decide +kernel) child_required_sub_569 common_sub_569 required_origin_569
theorem envelope_origin_569 : ∀ x ∈ envelope_569,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_569 j := by decide +kernel
theorem envelope_exact_569 : envelope_569 =
    insert (5, 5) (Finset.univ.biUnion childrenD_569) := by
  exact envelope_eq_combination childrenD_569 (5, 5) envelope_569
    pivot_mem_569 child_envelope_sub_569 envelope_origin_569
def checked_569 : CheckedCard where
  required := required_569
  envelope := envelope_569
  height := height_569
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_569
def height_575_i0 : ℕ := 4
def childrenH_575_i0 : Fin 2 → ℕ := ![height_3, height_8]
theorem height_exact_575_i0 : height_575_i0 = 1 + Finset.univ.sup childrenH_575_i0 := by decide +kernel
theorem required_origin_575_i0 : ∀ x ∈ required_575_i0,
    (∃ j, x ∈ childrenC_575_i0 j) ∨ ∀ j, x ∈ childrenD_575_i0 j := by decide +kernel
theorem required_exact_575_i0 : required_575_i0 =
    ((Finset.univ.biUnion childrenC_575_i0) ∪ commonEnvelope childrenD_575_i0).erase (2, 4) := by
  exact required_eq_combination childrenC_575_i0 childrenD_575_i0 (2, 4) required_575_i0
    (by decide +kernel) child_required_sub_575_i0 common_sub_575_i0 required_origin_575_i0
theorem envelope_origin_575_i0 : ∀ x ∈ envelope_575_i0,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_575_i0 j := by decide +kernel
theorem envelope_exact_575_i0 : envelope_575_i0 =
    insert (2, 4) (Finset.univ.biUnion childrenD_575_i0) := by
  exact envelope_eq_combination childrenD_575_i0 (2, 4) envelope_575_i0
    pivot_mem_575_i0 child_envelope_sub_575_i0 envelope_origin_575_i0
def checked_575_i0 : CheckedCard where
  required := required_575_i0
  envelope := envelope_575_i0
  height := height_575_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_575_i0
def height_575_i2 : ℕ := 3
def childrenH_575_i2 : Fin 2 → ℕ := ![height_3, height_6]
theorem height_exact_575_i2 : height_575_i2 = 1 + Finset.univ.sup childrenH_575_i2 := by decide +kernel
theorem required_origin_575_i2 : ∀ x ∈ required_575_i2,
    (∃ j, x ∈ childrenC_575_i2 j) ∨ ∀ j, x ∈ childrenD_575_i2 j := by decide +kernel
theorem required_exact_575_i2 : required_575_i2 =
    ((Finset.univ.biUnion childrenC_575_i2) ∪ commonEnvelope childrenD_575_i2).erase (2, 4) := by
  exact required_eq_combination childrenC_575_i2 childrenD_575_i2 (2, 4) required_575_i2
    (by decide +kernel) child_required_sub_575_i2 common_sub_575_i2 required_origin_575_i2
theorem envelope_origin_575_i2 : ∀ x ∈ envelope_575_i2,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_575_i2 j := by decide +kernel
theorem envelope_exact_575_i2 : envelope_575_i2 =
    insert (2, 4) (Finset.univ.biUnion childrenD_575_i2) := by
  exact envelope_eq_combination childrenD_575_i2 (2, 4) envelope_575_i2
    pivot_mem_575_i2 child_envelope_sub_575_i2 envelope_origin_575_i2
def checked_575_i2 : CheckedCard where
  required := required_575_i2
  envelope := envelope_575_i2
  height := height_575_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_575_i2
def height_575_i1 : ℕ := 8
def childrenH_575_i1 : Fin 2 → ℕ := ![height_575_i2, height_554]
theorem height_exact_575_i1 : height_575_i1 = 1 + Finset.univ.sup childrenH_575_i1 := by decide +kernel
theorem required_origin_575_i1 : ∀ x ∈ required_575_i1,
    (∃ j, x ∈ childrenC_575_i1 j) ∨ ∀ j, x ∈ childrenD_575_i1 j := by decide +kernel
theorem required_exact_575_i1 : required_575_i1 =
    ((Finset.univ.biUnion childrenC_575_i1) ∪ commonEnvelope childrenD_575_i1).erase (6, 4) := by
  exact required_eq_combination childrenC_575_i1 childrenD_575_i1 (6, 4) required_575_i1
    (by decide +kernel) child_required_sub_575_i1 common_sub_575_i1 required_origin_575_i1
theorem envelope_origin_575_i1 : ∀ x ∈ envelope_575_i1,
    x = (6, 4) ∨ ∃ j, x ∈ childrenD_575_i1 j := by decide +kernel
theorem envelope_exact_575_i1 : envelope_575_i1 =
    insert (6, 4) (Finset.univ.biUnion childrenD_575_i1) := by
  exact envelope_eq_combination childrenD_575_i1 (6, 4) envelope_575_i1
    pivot_mem_575_i1 child_envelope_sub_575_i1 envelope_origin_575_i1
def checked_575_i1 : CheckedCard where
  required := required_575_i1
  envelope := envelope_575_i1
  height := height_575_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_575_i1
def height_575_i3 : ℕ := 8
def childrenH_575_i3 : Fin 2 → ℕ := ![height_280, height_554]
theorem height_exact_575_i3 : height_575_i3 = 1 + Finset.univ.sup childrenH_575_i3 := by decide +kernel
theorem required_origin_575_i3 : ∀ x ∈ required_575_i3,
    (∃ j, x ∈ childrenC_575_i3 j) ∨ ∀ j, x ∈ childrenD_575_i3 j := by decide +kernel
theorem required_exact_575_i3 : required_575_i3 =
    ((Finset.univ.biUnion childrenC_575_i3) ∪ commonEnvelope childrenD_575_i3).erase (6, 4) := by
  exact required_eq_combination childrenC_575_i3 childrenD_575_i3 (6, 4) required_575_i3
    (by decide +kernel) child_required_sub_575_i3 common_sub_575_i3 required_origin_575_i3
theorem envelope_origin_575_i3 : ∀ x ∈ envelope_575_i3,
    x = (6, 4) ∨ ∃ j, x ∈ childrenD_575_i3 j := by decide +kernel
theorem envelope_exact_575_i3 : envelope_575_i3 =
    insert (6, 4) (Finset.univ.biUnion childrenD_575_i3) := by
  exact envelope_eq_combination childrenD_575_i3 (6, 4) envelope_575_i3
    pivot_mem_575_i3 child_envelope_sub_575_i3 envelope_origin_575_i3
def checked_575_i3 : CheckedCard where
  required := required_575_i3
  envelope := envelope_575_i3
  height := height_575_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_575_i3
def height_575 : ℕ := 10
def childrenH_575 : Fin 5 → ℕ := ![height_257, height_326, height_575_i0, height_575_i1, height_575_i3]
theorem height_exact_575 : height_575 = 1 + Finset.univ.sup childrenH_575 := by decide +kernel
theorem required_origin_575 : ∀ x ∈ required_575,
    (∃ j, x ∈ childrenC_575 j) ∨ ∀ j, x ∈ childrenD_575 j := by decide +kernel
theorem required_exact_575 : required_575 =
    ((Finset.univ.biUnion childrenC_575) ∪ commonEnvelope childrenD_575).erase (5, 4) := by
  exact required_eq_combination childrenC_575 childrenD_575 (5, 4) required_575
    (by decide +kernel) child_required_sub_575 common_sub_575 required_origin_575
theorem envelope_origin_575 : ∀ x ∈ envelope_575,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_575 j := by decide +kernel
theorem envelope_exact_575 : envelope_575 =
    insert (5, 4) (Finset.univ.biUnion childrenD_575) := by
  exact envelope_eq_combination childrenD_575 (5, 4) envelope_575
    pivot_mem_575 child_envelope_sub_575 envelope_origin_575
def checked_575 : CheckedCard where
  required := required_575
  envelope := envelope_575
  height := height_575
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_575
def height_578 : ℕ := 10
def childrenH_578 : Fin 4 → ℕ := ![height_26, height_49, height_117, height_577]
theorem height_exact_578 : height_578 = 1 + Finset.univ.sup childrenH_578 := by decide +kernel
theorem required_origin_578 : ∀ x ∈ required_578,
    (∃ j, x ∈ childrenC_578 j) ∨ ∀ j, x ∈ childrenD_578 j := by decide +kernel
theorem required_exact_578 : required_578 =
    ((Finset.univ.biUnion childrenC_578) ∪ commonEnvelope childrenD_578).erase (4, 3) := by
  exact required_eq_combination childrenC_578 childrenD_578 (4, 3) required_578
    (by decide +kernel) child_required_sub_578 common_sub_578 required_origin_578
theorem envelope_origin_578 : ∀ x ∈ envelope_578,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_578 j := by decide +kernel
theorem envelope_exact_578 : envelope_578 =
    insert (4, 3) (Finset.univ.biUnion childrenD_578) := by
  exact envelope_eq_combination childrenD_578 (4, 3) envelope_578
    pivot_mem_578 child_envelope_sub_578 envelope_origin_578
def checked_578 : CheckedCard where
  required := required_578
  envelope := envelope_578
  height := height_578
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_578
def height_580 : ℕ := 10
def childrenH_580 : Fin 4 → ℕ := ![height_24, height_49, height_194, height_577]
theorem height_exact_580 : height_580 = 1 + Finset.univ.sup childrenH_580 := by decide +kernel
theorem required_origin_580 : ∀ x ∈ required_580,
    (∃ j, x ∈ childrenC_580 j) ∨ ∀ j, x ∈ childrenD_580 j := by decide +kernel
theorem required_exact_580 : required_580 =
    ((Finset.univ.biUnion childrenC_580) ∪ commonEnvelope childrenD_580).erase (4, 2) := by
  exact required_eq_combination childrenC_580 childrenD_580 (4, 2) required_580
    (by decide +kernel) child_required_sub_580 common_sub_580 required_origin_580
theorem envelope_origin_580 : ∀ x ∈ envelope_580,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_580 j := by decide +kernel
theorem envelope_exact_580 : envelope_580 =
    insert (4, 2) (Finset.univ.biUnion childrenD_580) := by
  exact envelope_eq_combination childrenD_580 (4, 2) envelope_580
    pivot_mem_580 child_envelope_sub_580 envelope_origin_580
def checked_580 : CheckedCard where
  required := required_580
  envelope := envelope_580
  height := height_580
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_580
def height_585_i2 : ℕ := 7
def childrenH_585_i2 : Fin 2 → ℕ := ![height_11, height_358]
theorem height_exact_585_i2 : height_585_i2 = 1 + Finset.univ.sup childrenH_585_i2 := by decide +kernel
theorem required_origin_585_i2 : ∀ x ∈ required_585_i2,
    (∃ j, x ∈ childrenC_585_i2 j) ∨ ∀ j, x ∈ childrenD_585_i2 j := by decide +kernel
theorem required_exact_585_i2 : required_585_i2 =
    ((Finset.univ.biUnion childrenC_585_i2) ∪ commonEnvelope childrenD_585_i2).erase (1, 4) := by
  exact required_eq_combination childrenC_585_i2 childrenD_585_i2 (1, 4) required_585_i2
    (by decide +kernel) child_required_sub_585_i2 common_sub_585_i2 required_origin_585_i2
theorem envelope_origin_585_i2 : ∀ x ∈ envelope_585_i2,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_585_i2 j := by decide +kernel
theorem envelope_exact_585_i2 : envelope_585_i2 =
    insert (1, 4) (Finset.univ.biUnion childrenD_585_i2) := by
  exact envelope_eq_combination childrenD_585_i2 (1, 4) envelope_585_i2
    pivot_mem_585_i2 child_envelope_sub_585_i2 envelope_origin_585_i2
def checked_585_i2 : CheckedCard where
  required := required_585_i2
  envelope := envelope_585_i2
  height := height_585_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_585_i2
def height_585_i1 : ℕ := 8
def childrenH_585_i1 : Fin 2 → ℕ := ![height_5, height_585_i2]
theorem height_exact_585_i1 : height_585_i1 = 1 + Finset.univ.sup childrenH_585_i1 := by decide +kernel
theorem required_origin_585_i1 : ∀ x ∈ required_585_i1,
    (∃ j, x ∈ childrenC_585_i1 j) ∨ ∀ j, x ∈ childrenD_585_i1 j := by decide +kernel
theorem required_exact_585_i1 : required_585_i1 =
    ((Finset.univ.biUnion childrenC_585_i1) ∪ commonEnvelope childrenD_585_i1).erase (4, 1) := by
  exact required_eq_combination childrenC_585_i1 childrenD_585_i1 (4, 1) required_585_i1
    (by decide +kernel) child_required_sub_585_i1 common_sub_585_i1 required_origin_585_i1
theorem envelope_origin_585_i1 : ∀ x ∈ envelope_585_i1,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_585_i1 j := by decide +kernel
theorem envelope_exact_585_i1 : envelope_585_i1 =
    insert (4, 1) (Finset.univ.biUnion childrenD_585_i1) := by
  exact envelope_eq_combination childrenD_585_i1 (4, 1) envelope_585_i1
    pivot_mem_585_i1 child_envelope_sub_585_i1 envelope_origin_585_i1
def checked_585_i1 : CheckedCard where
  required := required_585_i1
  envelope := envelope_585_i1
  height := height_585_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_585_i1
def height_585_i0 : ℕ := 9
def childrenH_585_i0 : Fin 2 → ℕ := ![height_5, height_585_i1]
theorem height_exact_585_i0 : height_585_i0 = 1 + Finset.univ.sup childrenH_585_i0 := by decide +kernel
theorem required_origin_585_i0 : ∀ x ∈ required_585_i0,
    (∃ j, x ∈ childrenC_585_i0 j) ∨ ∀ j, x ∈ childrenD_585_i0 j := by decide +kernel
theorem required_exact_585_i0 : required_585_i0 =
    ((Finset.univ.biUnion childrenC_585_i0) ∪ commonEnvelope childrenD_585_i0).erase (1, 1) := by
  exact required_eq_combination childrenC_585_i0 childrenD_585_i0 (1, 1) required_585_i0
    (by decide +kernel) child_required_sub_585_i0 common_sub_585_i0 required_origin_585_i0
theorem envelope_origin_585_i0 : ∀ x ∈ envelope_585_i0,
    x = (1, 1) ∨ ∃ j, x ∈ childrenD_585_i0 j := by decide +kernel
theorem envelope_exact_585_i0 : envelope_585_i0 =
    insert (1, 1) (Finset.univ.biUnion childrenD_585_i0) := by
  exact envelope_eq_combination childrenD_585_i0 (1, 1) envelope_585_i0
    pivot_mem_585_i0 child_envelope_sub_585_i0 envelope_origin_585_i0
def checked_585_i0 : CheckedCard where
  required := required_585_i0
  envelope := envelope_585_i0
  height := height_585_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_585_i0
def height_585 : ℕ := 10
def childrenH_585 : Fin 2 → ℕ := ![height_5, height_585_i0]
theorem height_exact_585 : height_585 = 1 + Finset.univ.sup childrenH_585 := by decide +kernel
theorem required_origin_585 : ∀ x ∈ required_585,
    (∃ j, x ∈ childrenC_585 j) ∨ ∀ j, x ∈ childrenD_585 j := by decide +kernel
theorem required_exact_585 : required_585 =
    ((Finset.univ.biUnion childrenC_585) ∪ commonEnvelope childrenD_585).erase (1, 3) := by
  exact required_eq_combination childrenC_585 childrenD_585 (1, 3) required_585
    (by decide +kernel) child_required_sub_585 common_sub_585 required_origin_585
theorem envelope_origin_585 : ∀ x ∈ envelope_585,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_585 j := by decide +kernel
theorem envelope_exact_585 : envelope_585 =
    insert (1, 3) (Finset.univ.biUnion childrenD_585) := by
  exact envelope_eq_combination childrenD_585 (1, 3) envelope_585
    pivot_mem_585 child_envelope_sub_585 envelope_origin_585
def checked_585 : CheckedCard where
  required := required_585
  envelope := envelope_585
  height := height_585
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_585
end SnakyPrototype.Certificate21

end OAI
