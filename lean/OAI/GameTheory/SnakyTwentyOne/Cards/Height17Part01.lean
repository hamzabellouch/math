import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part07
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height16Part01
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_623_i0 : Finset Cell := ⟨(([(5, 6), (5, 7), (8, 6), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_623_i0 : Finset Cell := ⟨(([(2, 7), (3, 7), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 8), (6, 9), (6, 10), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 3), (8, 4), (8, 6), (8, 7), (8, 8), (8, 9), (9, 3), (9, 4), (9, 5), (9, 6), (9, 9), (10, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_623_i0 : Fin 4 → Finset Cell := ![(placed21 2 (7, 3) required_188), (placed21 0 (4, 4) required_444), (placed21 4 (4, 9) required_606), (placed21 4 (4, 9) required_610)]
def childrenD_623_i0 : Fin 4 → Finset Cell := ![(placed21 2 (7, 3) envelope_188), (placed21 0 (4, 4) envelope_444), (placed21 4 (4, 9) envelope_606), (placed21 4 (4, 9) envelope_610)]
theorem common_sub_623_i0 : commonEnvelope childrenD_623_i0 ⊆ insert (5, 5) required_623_i0 := by decide +kernel
theorem child_required_sub_623_i0 : ∀ j, childrenC_623_i0 j ⊆ insert (5, 5) required_623_i0 := by decide +kernel
theorem child_envelope_sub_623_i0 : ∀ j, childrenD_623_i0 j ⊆ envelope_623_i0 := by decide +kernel
theorem pivot_mem_623_i0 : (5, 5) ∈ envelope_623_i0 := by decide +kernel
theorem children_work_623_i0 : ∀ j, Template HasSnaky 10 (childrenC_623_i0 j) (childrenD_623_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_188 2 (7, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_444 0 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_606 4 (4, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_610 4 (4, 9)).mono (by decide +kernel)
theorem row_works_623_i0 : Template HasSnaky 11 required_623_i0 envelope_623_i0 := by
  refine compose HasSnaky 10 childrenC_623_i0 childrenD_623_i0 children_work_623_i0 (5, 5)
    required_623_i0 envelope_623_i0 pivot_mem_623_i0 child_required_sub_623_i0 child_envelope_sub_623_i0 ?_
  intro b hb
  exact common_sub_623_i0 (mem_commonEnvelope childrenD_623_i0 b hb)
def required_623_i1 : Finset Cell := ⟨(([(5, 6), (5, 7), (8, 6), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_623_i1 : Finset Cell := ⟨(([(2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (3, 6), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 6), (8, 7), (8, 8), (8, 9), (9, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_623_i1 : Fin 5 → Finset Cell := ![(placed21 7 (7, 8) required_137), (placed21 7 (7, 8) required_181), (placed21 6 (8, 9) required_363), (placed21 7 (7, 8) required_474), (placed21 4 (4, 9) required_606)]
def childrenD_623_i1 : Fin 5 → Finset Cell := ![(placed21 7 (7, 8) envelope_137), (placed21 7 (7, 8) envelope_181), (placed21 6 (8, 9) envelope_363), (placed21 7 (7, 8) envelope_474), (placed21 4 (4, 9) envelope_606)]
theorem common_sub_623_i1 : commonEnvelope childrenD_623_i1 ⊆ insert (5, 5) required_623_i1 := by decide +kernel
theorem child_required_sub_623_i1 : ∀ j, childrenC_623_i1 j ⊆ insert (5, 5) required_623_i1 := by decide +kernel
theorem child_envelope_sub_623_i1 : ∀ j, childrenD_623_i1 j ⊆ envelope_623_i1 := by decide +kernel
theorem pivot_mem_623_i1 : (5, 5) ∈ envelope_623_i1 := by decide +kernel
theorem children_work_623_i1 : ∀ j, Template HasSnaky 9 (childrenC_623_i1 j) (childrenD_623_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_137 7 (7, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_181 7 (7, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_363 6 (8, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_474 7 (7, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_606 4 (4, 9)).mono (by decide +kernel)
theorem row_works_623_i1 : Template HasSnaky 10 required_623_i1 envelope_623_i1 := by
  refine compose HasSnaky 9 childrenC_623_i1 childrenD_623_i1 children_work_623_i1 (5, 5)
    required_623_i1 envelope_623_i1 pivot_mem_623_i1 child_required_sub_623_i1 child_envelope_sub_623_i1 ?_
  intro b hb
  exact common_sub_623_i1 (mem_commonEnvelope childrenD_623_i1 b hb)
def required_623_i4 : Finset Cell := ⟨(([(5, 6), (5, 7), (5, 8), (5, 9), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_623_i4 : Finset Cell := ⟨(([(4, 6), (4, 7), (4, 8), (4, 10), (4, 11), (4, 12), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 5), (6, 6), (7, 6), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_623_i4 : Fin 2 → Finset Cell := ![(placed21 2 (5, 6) required_27), (placed21 3 (4, 9) required_35)]
def childrenD_623_i4 : Fin 2 → Finset Cell := ![(placed21 2 (5, 6) envelope_27), (placed21 3 (4, 9) envelope_35)]
theorem common_sub_623_i4 : commonEnvelope childrenD_623_i4 ⊆ insert (4, 7) required_623_i4 := by decide +kernel
theorem child_required_sub_623_i4 : ∀ j, childrenC_623_i4 j ⊆ insert (4, 7) required_623_i4 := by decide +kernel
theorem child_envelope_sub_623_i4 : ∀ j, childrenD_623_i4 j ⊆ envelope_623_i4 := by decide +kernel
theorem pivot_mem_623_i4 : (4, 7) ∈ envelope_623_i4 := by decide +kernel
theorem children_work_623_i4 : ∀ j, Template HasSnaky 4 (childrenC_623_i4 j) (childrenD_623_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_27 2 (5, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_35 3 (4, 9)).mono (by decide +kernel)
theorem row_works_623_i4 : Template HasSnaky 5 required_623_i4 envelope_623_i4 := by
  refine compose HasSnaky 4 childrenC_623_i4 childrenD_623_i4 children_work_623_i4 (4, 7)
    required_623_i4 envelope_623_i4 pivot_mem_623_i4 child_required_sub_623_i4 child_envelope_sub_623_i4 ?_
  intro b hb
  exact common_sub_623_i4 (mem_commonEnvelope childrenD_623_i4 b hb)
def required_623_i3 : Finset Cell := ⟨(([(5, 6), (5, 7), (5, 8), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_623_i3 : Finset Cell := ⟨(([(4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 4), (6, 5), (6, 6), (7, 6), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_623_i3 : Fin 5 → Finset Cell := ![(placed21 4 (4, 10) required_9), (placed21 2 (8, 5) required_151), (placed21 2 (6, 4) required_186), (placed21 2 (5, 4) required_187), required_623_i4]
def childrenD_623_i3 : Fin 5 → Finset Cell := ![(placed21 4 (4, 10) envelope_9), (placed21 2 (8, 5) envelope_151), (placed21 2 (6, 4) envelope_186), (placed21 2 (5, 4) envelope_187), envelope_623_i4]
theorem common_sub_623_i3 : commonEnvelope childrenD_623_i3 ⊆ insert (5, 9) required_623_i3 := by decide +kernel
theorem child_required_sub_623_i3 : ∀ j, childrenC_623_i3 j ⊆ insert (5, 9) required_623_i3 := by decide +kernel
theorem child_envelope_sub_623_i3 : ∀ j, childrenD_623_i3 j ⊆ envelope_623_i3 := by decide +kernel
theorem pivot_mem_623_i3 : (5, 9) ∈ envelope_623_i3 := by decide +kernel
theorem children_work_623_i3 : ∀ j, Template HasSnaky 5 (childrenC_623_i3 j) (childrenD_623_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_9 4 (4, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_151 2 (8, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_186 2 (6, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_187 2 (5, 4)).mono (by decide +kernel)
  · exact row_works_623_i4.mono (by decide +kernel)
theorem row_works_623_i3 : Template HasSnaky 6 required_623_i3 envelope_623_i3 := by
  refine compose HasSnaky 5 childrenC_623_i3 childrenD_623_i3 children_work_623_i3 (5, 9)
    required_623_i3 envelope_623_i3 pivot_mem_623_i3 child_required_sub_623_i3 child_envelope_sub_623_i3 ?_
  intro b hb
  exact common_sub_623_i3 (mem_commonEnvelope childrenD_623_i3 b hb)
def required_623_i5 : Finset Cell := ⟨(([(5, 6), (5, 7), (5, 8), (8, 6), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_623_i5 : Finset Cell := ⟨(([(3, 7), (4, 2), (4, 3), (4, 4), (4, 6), (4, 7), (4, 8), (4, 9), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 8), (6, 9), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 6), (8, 7), (8, 8), (8, 9), (9, 5), (9, 6), (9, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_623_i5 : Fin 3 → Finset Cell := ![(placed21 3 (3, 9) required_179), (placed21 3 (4, 8) required_371), (placed21 4 (4, 9) required_443)]
def childrenD_623_i5 : Fin 3 → Finset Cell := ![(placed21 3 (3, 9) envelope_179), (placed21 3 (4, 8) envelope_371), (placed21 4 (4, 9) envelope_443)]
theorem common_sub_623_i5 : commonEnvelope childrenD_623_i5 ⊆ insert (5, 5) required_623_i5 := by decide +kernel
theorem child_required_sub_623_i5 : ∀ j, childrenC_623_i5 j ⊆ insert (5, 5) required_623_i5 := by decide +kernel
theorem child_envelope_sub_623_i5 : ∀ j, childrenD_623_i5 j ⊆ envelope_623_i5 := by decide +kernel
theorem pivot_mem_623_i5 : (5, 5) ∈ envelope_623_i5 := by decide +kernel
theorem children_work_623_i5 : ∀ j, Template HasSnaky 9 (childrenC_623_i5 j) (childrenD_623_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_179 3 (3, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_371 3 (4, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_443 4 (4, 9)).mono (by decide +kernel)
theorem row_works_623_i5 : Template HasSnaky 10 required_623_i5 envelope_623_i5 := by
  refine compose HasSnaky 9 childrenC_623_i5 childrenD_623_i5 children_work_623_i5 (5, 5)
    required_623_i5 envelope_623_i5 pivot_mem_623_i5 child_required_sub_623_i5 child_envelope_sub_623_i5 ?_
  intro b hb
  exact common_sub_623_i5 (mem_commonEnvelope childrenD_623_i5 b hb)
def required_623_i2 : Finset Cell := ⟨(([(5, 6), (5, 7), (8, 6), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_623_i2 : Finset Cell := ⟨(([(2, 7), (2, 8), (2, 9), (3, 7), (3, 8), (3, 9), (4, 2), (4, 3), (4, 4), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 5), (9, 6), (9, 8), (9, 9), (9, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_623_i2 : Fin 7 → Finset Cell := ![(placed21 2 (6, 4) required_12), (placed21 2 (7, 4) required_188), (placed21 2 (8, 4) required_211), required_623_i3, (placed21 1 (2, 5) required_619), required_623_i5, (placed21 2 (8, 2) required_620)]
def childrenD_623_i2 : Fin 7 → Finset Cell := ![(placed21 2 (6, 4) envelope_12), (placed21 2 (7, 4) envelope_188), (placed21 2 (8, 4) envelope_211), envelope_623_i3, (placed21 1 (2, 5) envelope_619), envelope_623_i5, (placed21 2 (8, 2) envelope_620)]
theorem common_sub_623_i2 : commonEnvelope childrenD_623_i2 ⊆ insert (5, 8) required_623_i2 := by decide +kernel
theorem child_required_sub_623_i2 : ∀ j, childrenC_623_i2 j ⊆ insert (5, 8) required_623_i2 := by decide +kernel
theorem child_envelope_sub_623_i2 : ∀ j, childrenD_623_i2 j ⊆ envelope_623_i2 := by decide +kernel
theorem pivot_mem_623_i2 : (5, 8) ∈ envelope_623_i2 := by decide +kernel
theorem children_work_623_i2 : ∀ j, Template HasSnaky 10 (childrenC_623_i2 j) (childrenD_623_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 2 (6, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_188 2 (7, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_211 2 (8, 4)).mono (by decide +kernel)
  · exact row_works_623_i3.mono (by decide +kernel)
  · exact (placed21_template row_works_619 1 (2, 5)).mono (by decide +kernel)
  · exact row_works_623_i5.mono (by decide +kernel)
  · exact (placed21_template row_works_620 2 (8, 2)).mono (by decide +kernel)
theorem row_works_623_i2 : Template HasSnaky 11 required_623_i2 envelope_623_i2 := by
  refine compose HasSnaky 10 childrenC_623_i2 childrenD_623_i2 children_work_623_i2 (5, 8)
    required_623_i2 envelope_623_i2 pivot_mem_623_i2 child_required_sub_623_i2 child_envelope_sub_623_i2 ?_
  intro b hb
  exact common_sub_623_i2 (mem_commonEnvelope childrenD_623_i2 b hb)
def required_623_i7 : Finset Cell := ⟨(([(5, 6), (5, 7), (5, 8), (8, 6), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_623_i7 : Finset Cell := ⟨(([(3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 2), (6, 3), (6, 4), (6, 6), (6, 8), (6, 9), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 9), (9, 10), (9, 11)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_623_i7 : Fin 3 → Finset Cell := ![(placed21 3 (3, 9) required_179), (placed21 3 (4, 8) required_197), (placed21 0 (4, 4) required_465)]
def childrenD_623_i7 : Fin 3 → Finset Cell := ![(placed21 3 (3, 9) envelope_179), (placed21 3 (4, 8) envelope_197), (placed21 0 (4, 4) envelope_465)]
theorem common_sub_623_i7 : commonEnvelope childrenD_623_i7 ⊆ insert (5, 5) required_623_i7 := by decide +kernel
theorem child_required_sub_623_i7 : ∀ j, childrenC_623_i7 j ⊆ insert (5, 5) required_623_i7 := by decide +kernel
theorem child_envelope_sub_623_i7 : ∀ j, childrenD_623_i7 j ⊆ envelope_623_i7 := by decide +kernel
theorem pivot_mem_623_i7 : (5, 5) ∈ envelope_623_i7 := by decide +kernel
theorem children_work_623_i7 : ∀ j, Template HasSnaky 6 (childrenC_623_i7 j) (childrenD_623_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_179 3 (3, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_197 3 (4, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_465 0 (4, 4)).mono (by decide +kernel)
theorem row_works_623_i7 : Template HasSnaky 7 required_623_i7 envelope_623_i7 := by
  refine compose HasSnaky 6 childrenC_623_i7 childrenD_623_i7 children_work_623_i7 (5, 5)
    required_623_i7 envelope_623_i7 pivot_mem_623_i7 child_required_sub_623_i7 child_envelope_sub_623_i7 ?_
  intro b hb
  exact common_sub_623_i7 (mem_commonEnvelope childrenD_623_i7 b hb)
def required_623_i6 : Finset Cell := ⟨(([(5, 6), (5, 7), (8, 6), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_623_i6 : Finset Cell := ⟨(([(1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 2), (6, 3), (6, 4), (6, 6), (6, 8), (6, 9), (6, 10), (6, 11), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 8), (9, 9), (9, 10), (9, 11), (10, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_623_i6 : Fin 6 → Finset Cell := ![(placed21 0 (4, 4) required_12), (placed21 1 (1, 5) required_322), (placed21 4 (4, 11) required_369), (placed21 1 (2, 5) required_435), required_623_i7, (placed21 6 (8, 11) required_622)]
def childrenD_623_i6 : Fin 6 → Finset Cell := ![(placed21 0 (4, 4) envelope_12), (placed21 1 (1, 5) envelope_322), (placed21 4 (4, 11) envelope_369), (placed21 1 (2, 5) envelope_435), envelope_623_i7, (placed21 6 (8, 11) envelope_622)]
theorem common_sub_623_i6 : commonEnvelope childrenD_623_i6 ⊆ insert (5, 8) required_623_i6 := by decide +kernel
theorem child_required_sub_623_i6 : ∀ j, childrenC_623_i6 j ⊆ insert (5, 8) required_623_i6 := by decide +kernel
theorem child_envelope_sub_623_i6 : ∀ j, childrenD_623_i6 j ⊆ envelope_623_i6 := by decide +kernel
theorem pivot_mem_623_i6 : (5, 8) ∈ envelope_623_i6 := by decide +kernel
theorem children_work_623_i6 : ∀ j, Template HasSnaky 9 (childrenC_623_i6 j) (childrenD_623_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 0 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_322 1 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_369 4 (4, 11)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 1 (2, 5)).mono (by decide +kernel)
  · exact row_works_623_i7.mono (by decide +kernel)
  · exact (placed21_template row_works_622 6 (8, 11)).mono (by decide +kernel)
theorem row_works_623_i6 : Template HasSnaky 10 required_623_i6 envelope_623_i6 := by
  refine compose HasSnaky 9 childrenC_623_i6 childrenD_623_i6 children_work_623_i6 (5, 8)
    required_623_i6 envelope_623_i6 pivot_mem_623_i6 child_required_sub_623_i6 child_envelope_sub_623_i6 ?_
  intro b hb
  exact common_sub_623_i6 (mem_commonEnvelope childrenD_623_i6 b hb)
def required_623 : Finset Cell := ⟨(([(5, 7), (8, 6), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_623 : Finset Cell := ⟨(([(0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 15), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (8, 3), (8, 4), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14), (8, 15), (9, 3), (9, 4), (9, 5), (9, 6), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (10, 3), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (10, 13), (10, 14), (10, 15), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 10), (11, 11), (11, 12), (11, 13), (11, 14), (12, 8), (12, 9), (12, 10), (12, 11), (12, 12), (12, 13), (13, 8), (13, 9), (13, 10), (13, 11), (13, 12), (14, 10), (14, 12)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_623 : Fin 11 → Finset Cell := ![(placed21 6 (9, 11) required_467), (placed21 1 (0, 3) required_602), (placed21 2 (6, 3) required_603), (placed21 5 (8, 4) required_605), (placed21 6 (9, 11) required_607), (placed21 6 (9, 11) required_608), required_623_i0, (placed21 6 (10, 10) required_618), required_623_i1, required_623_i2, required_623_i6]
def childrenD_623 : Fin 11 → Finset Cell := ![(placed21 6 (9, 11) envelope_467), (placed21 1 (0, 3) envelope_602), (placed21 2 (6, 3) envelope_603), (placed21 5 (8, 4) envelope_605), (placed21 6 (9, 11) envelope_607), (placed21 6 (9, 11) envelope_608), envelope_623_i0, (placed21 6 (10, 10) envelope_618), envelope_623_i1, envelope_623_i2, envelope_623_i6]
theorem common_sub_623 : commonEnvelope childrenD_623 ⊆ insert (5, 6) required_623 := by decide +kernel
theorem child_required_sub_623 : ∀ j, childrenC_623 j ⊆ insert (5, 6) required_623 := by decide +kernel
theorem child_envelope_sub_623 : ∀ j, childrenD_623 j ⊆ envelope_623 := by decide +kernel
theorem pivot_mem_623 : (5, 6) ∈ envelope_623 := by decide +kernel
theorem children_work_623 : ∀ j, Template HasSnaky 16 (childrenC_623 j) (childrenD_623 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_467 6 (9, 11)).mono (by decide +kernel)
  · exact (placed21_template row_works_602 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_603 2 (6, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_605 5 (8, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_607 6 (9, 11)).mono (by decide +kernel)
  · exact (placed21_template row_works_608 6 (9, 11)).mono (by decide +kernel)
  · exact row_works_623_i0.mono (by decide +kernel)
  · exact (placed21_template row_works_618 6 (10, 10)).mono (by decide +kernel)
  · exact row_works_623_i1.mono (by decide +kernel)
  · exact row_works_623_i2.mono (by decide +kernel)
  · exact row_works_623_i6.mono (by decide +kernel)
theorem row_works_623 : Template HasSnaky 17 required_623 envelope_623 := by
  refine compose HasSnaky 16 childrenC_623 childrenD_623 children_work_623 (5, 6)
    required_623 envelope_623 pivot_mem_623 child_required_sub_623 child_envelope_sub_623 ?_
  intro b hb
  exact common_sub_623 (mem_commonEnvelope childrenD_623 b hb)
def required_630_i0 : Finset Cell := ⟨(([(4, 6), (4, 7), (7, 6), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_630_i0 : Finset Cell := ⟨(([(1, 8), (1, 9), (2, 8), (2, 9), (3, 3), (3, 4), (3, 5), (3, 6), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, 3), (5, 4), (5, 5), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 8), (8, 9), (8, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_630_i0 : Fin 7 → Finset Cell := ![(placed21 0 (3, 4) required_12), (placed21 6 (5, 10) required_13), (placed21 6 (7, 9) required_355), (placed21 6 (7, 10) required_356), (placed21 2 (8, 5) required_434), (placed21 5 (7, 5) required_435), (placed21 4 (3, 10) required_441)]
def childrenD_630_i0 : Fin 7 → Finset Cell := ![(placed21 0 (3, 4) envelope_12), (placed21 6 (5, 10) envelope_13), (placed21 6 (7, 9) envelope_355), (placed21 6 (7, 10) envelope_356), (placed21 2 (8, 5) envelope_434), (placed21 5 (7, 5) envelope_435), (placed21 4 (3, 10) envelope_441)]
theorem common_sub_630_i0 : commonEnvelope childrenD_630_i0 ⊆ insert (4, 8) required_630_i0 := by decide +kernel
theorem child_required_sub_630_i0 : ∀ j, childrenC_630_i0 j ⊆ insert (4, 8) required_630_i0 := by decide +kernel
theorem child_envelope_sub_630_i0 : ∀ j, childrenD_630_i0 j ⊆ envelope_630_i0 := by decide +kernel
theorem pivot_mem_630_i0 : (4, 8) ∈ envelope_630_i0 := by decide +kernel
theorem children_work_630_i0 : ∀ j, Template HasSnaky 9 (childrenC_630_i0 j) (childrenD_630_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 0 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_13 6 (5, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_355 6 (7, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_356 6 (7, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_434 2 (8, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 5 (7, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_441 4 (3, 10)).mono (by decide +kernel)
theorem row_works_630_i0 : Template HasSnaky 10 required_630_i0 envelope_630_i0 := by
  refine compose HasSnaky 9 childrenC_630_i0 childrenD_630_i0 children_work_630_i0 (4, 8)
    required_630_i0 envelope_630_i0 pivot_mem_630_i0 child_required_sub_630_i0 child_envelope_sub_630_i0 ?_
  intro b hb
  exact common_sub_630_i0 (mem_commonEnvelope childrenD_630_i0 b hb)
def required_630_i1 : Finset Cell := ⟨(([(4, 6), (4, 7), (7, 6), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_630_i1 : Finset Cell := ⟨(([(3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 8), (3, 9), (3, 10), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 6), (7, 7), (7, 8), (7, 9), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_630_i1 : Fin 4 → Finset Cell := ![(placed21 0 (3, 3) required_13), (placed21 0 (3, 4) required_112), (placed21 6 (7, 9) required_363), (placed21 6 (7, 9) required_364)]
def childrenD_630_i1 : Fin 4 → Finset Cell := ![(placed21 0 (3, 3) envelope_13), (placed21 0 (3, 4) envelope_112), (placed21 6 (7, 9) envelope_363), (placed21 6 (7, 9) envelope_364)]
theorem common_sub_630_i1 : commonEnvelope childrenD_630_i1 ⊆ insert (4, 5) required_630_i1 := by decide +kernel
theorem child_required_sub_630_i1 : ∀ j, childrenC_630_i1 j ⊆ insert (4, 5) required_630_i1 := by decide +kernel
theorem child_envelope_sub_630_i1 : ∀ j, childrenD_630_i1 j ⊆ envelope_630_i1 := by decide +kernel
theorem pivot_mem_630_i1 : (4, 5) ∈ envelope_630_i1 := by decide +kernel
theorem children_work_630_i1 : ∀ j, Template HasSnaky 6 (childrenC_630_i1 j) (childrenD_630_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 0 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_112 0 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_363 6 (7, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_364 6 (7, 9)).mono (by decide +kernel)
theorem row_works_630_i1 : Template HasSnaky 7 required_630_i1 envelope_630_i1 := by
  refine compose HasSnaky 6 childrenC_630_i1 childrenD_630_i1 children_work_630_i1 (4, 5)
    required_630_i1 envelope_630_i1 pivot_mem_630_i1 child_required_sub_630_i1 child_envelope_sub_630_i1 ?_
  intro b hb
  exact common_sub_630_i1 (mem_commonEnvelope childrenD_630_i1 b hb)
def required_630_i2 : Finset Cell := ⟨(([(4, 6), (4, 7), (7, 6), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_630_i2 : Finset Cell := ⟨(([(1, 8), (2, 5), (2, 8), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 8), (3, 9), (3, 10), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 4), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 6), (8, 9), (8, 10), (8, 11)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_630_i2 : Fin 5 → Finset Cell := ![(placed21 0 (3, 4) required_112), (placed21 5 (6, 4) required_181), (placed21 3 (2, 8) required_181), (placed21 6 (8, 8) required_295), (placed21 0 (3, 4) required_466)]
def childrenD_630_i2 : Fin 5 → Finset Cell := ![(placed21 0 (3, 4) envelope_112), (placed21 5 (6, 4) envelope_181), (placed21 3 (2, 8) envelope_181), (placed21 6 (8, 8) envelope_295), (placed21 0 (3, 4) envelope_466)]
theorem common_sub_630_i2 : commonEnvelope childrenD_630_i2 ⊆ insert (4, 5) required_630_i2 := by decide +kernel
theorem child_required_sub_630_i2 : ∀ j, childrenC_630_i2 j ⊆ insert (4, 5) required_630_i2 := by decide +kernel
theorem child_envelope_sub_630_i2 : ∀ j, childrenD_630_i2 j ⊆ envelope_630_i2 := by decide +kernel
theorem pivot_mem_630_i2 : (4, 5) ∈ envelope_630_i2 := by decide +kernel
theorem children_work_630_i2 : ∀ j, Template HasSnaky 7 (childrenC_630_i2 j) (childrenD_630_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_112 0 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_181 5 (6, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_181 3 (2, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_295 6 (8, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_466 0 (3, 4)).mono (by decide +kernel)
theorem row_works_630_i2 : Template HasSnaky 8 required_630_i2 envelope_630_i2 := by
  refine compose HasSnaky 7 childrenC_630_i2 childrenD_630_i2 children_work_630_i2 (4, 5)
    required_630_i2 envelope_630_i2 pivot_mem_630_i2 child_required_sub_630_i2 child_envelope_sub_630_i2 ?_
  intro b hb
  exact common_sub_630_i2 (mem_commonEnvelope childrenD_630_i2 b hb)
def required_630_i4 : Finset Cell := ⟨(([(4, 5), (4, 6), (4, 7), (7, 6), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_630_i4 : Finset Cell := ⟨(([(3, 2), (3, 3), (3, 4), (3, 6), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 7), (5, 8), (6, 7), (7, 6), (7, 7), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_630_i4 : Fin 2 → Finset Cell := ![(placed21 6 (5, 8) required_10), (placed21 3 (3, 7) required_34)]
def childrenD_630_i4 : Fin 2 → Finset Cell := ![(placed21 6 (5, 8) envelope_10), (placed21 3 (3, 7) envelope_34)]
theorem common_sub_630_i4 : commonEnvelope childrenD_630_i4 ⊆ insert (5, 7) required_630_i4 := by decide +kernel
theorem child_required_sub_630_i4 : ∀ j, childrenC_630_i4 j ⊆ insert (5, 7) required_630_i4 := by decide +kernel
theorem child_envelope_sub_630_i4 : ∀ j, childrenD_630_i4 j ⊆ envelope_630_i4 := by decide +kernel
theorem pivot_mem_630_i4 : (5, 7) ∈ envelope_630_i4 := by decide +kernel
theorem children_work_630_i4 : ∀ j, Template HasSnaky 4 (childrenC_630_i4 j) (childrenD_630_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 6 (5, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_34 3 (3, 7)).mono (by decide +kernel)
theorem row_works_630_i4 : Template HasSnaky 5 required_630_i4 envelope_630_i4 := by
  refine compose HasSnaky 4 childrenC_630_i4 childrenD_630_i4 children_work_630_i4 (5, 7)
    required_630_i4 envelope_630_i4 pivot_mem_630_i4 child_required_sub_630_i4 child_envelope_sub_630_i4 ?_
  intro b hb
  exact common_sub_630_i4 (mem_commonEnvelope childrenD_630_i4 b hb)
def required_630_i3 : Finset Cell := ⟨(([(4, 6), (4, 7), (7, 6), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_630_i3 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 3), (7, 4), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 3), (8, 4), (8, 5), (8, 6), (9, 5), (9, 6), (9, 7), (10, 5), (10, 6), (10, 7), (11, 5), (11, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_630_i3 : Fin 5 → Finset Cell := ![(placed21 0 (3, 4) required_112), (placed21 3 (1, 8) required_257), (placed21 7 (7, 7) required_398), required_630_i4, (placed21 0 (3, 3) required_628)]
def childrenD_630_i3 : Fin 5 → Finset Cell := ![(placed21 0 (3, 4) envelope_112), (placed21 3 (1, 8) envelope_257), (placed21 7 (7, 7) envelope_398), envelope_630_i4, (placed21 0 (3, 3) envelope_628)]
theorem common_sub_630_i3 : commonEnvelope childrenD_630_i3 ⊆ insert (4, 5) required_630_i3 := by decide +kernel
theorem child_required_sub_630_i3 : ∀ j, childrenC_630_i3 j ⊆ insert (4, 5) required_630_i3 := by decide +kernel
theorem child_envelope_sub_630_i3 : ∀ j, childrenD_630_i3 j ⊆ envelope_630_i3 := by decide +kernel
theorem pivot_mem_630_i3 : (4, 5) ∈ envelope_630_i3 := by decide +kernel
theorem children_work_630_i3 : ∀ j, Template HasSnaky 9 (childrenC_630_i3 j) (childrenD_630_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_112 0 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_257 3 (1, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_398 7 (7, 7)).mono (by decide +kernel)
  · exact row_works_630_i4.mono (by decide +kernel)
  · exact (placed21_template row_works_628 0 (3, 3)).mono (by decide +kernel)
theorem row_works_630_i3 : Template HasSnaky 10 required_630_i3 envelope_630_i3 := by
  refine compose HasSnaky 9 childrenC_630_i3 childrenD_630_i3 children_work_630_i3 (4, 5)
    required_630_i3 envelope_630_i3 pivot_mem_630_i3 child_required_sub_630_i3 child_envelope_sub_630_i3 ?_
  intro b hb
  exact common_sub_630_i3 (mem_commonEnvelope childrenD_630_i3 b hb)
def required_630 : Finset Cell := ⟨(([(4, 7), (7, 6), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_630 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 5), (1, 6), (1, 8), (1, 9), (1, 10), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 8), (2, 9), (2, 10), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (7, 3), (7, 4), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (8, 3), (8, 4), (8, 5), (8, 6), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (10, 13), (11, 5), (11, 7), (11, 8), (11, 9), (11, 10), (12, 8), (12, 9), (12, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_630 : Fin 9 → Finset Cell := ![(placed21 2 (8, 3) required_368), (placed21 6 (8, 10) required_368), required_630_i0, (placed21 6 (8, 11) required_467), (placed21 0 (1, 3) required_627), required_630_i1, required_630_i2, (placed21 4 (1, 10) required_629), required_630_i3]
def childrenD_630 : Fin 9 → Finset Cell := ![(placed21 2 (8, 3) envelope_368), (placed21 6 (8, 10) envelope_368), envelope_630_i0, (placed21 6 (8, 11) envelope_467), (placed21 0 (1, 3) envelope_627), envelope_630_i1, envelope_630_i2, (placed21 4 (1, 10) envelope_629), envelope_630_i3]
theorem common_sub_630 : commonEnvelope childrenD_630 ⊆ insert (4, 6) required_630 := by decide +kernel
theorem child_required_sub_630 : ∀ j, childrenC_630 j ⊆ insert (4, 6) required_630 := by decide +kernel
theorem child_envelope_sub_630 : ∀ j, childrenD_630 j ⊆ envelope_630 := by decide +kernel
theorem pivot_mem_630 : (4, 6) ∈ envelope_630 := by decide +kernel
theorem children_work_630 : ∀ j, Template HasSnaky 16 (childrenC_630 j) (childrenD_630 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_368 2 (8, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_368 6 (8, 10)).mono (by decide +kernel)
  · exact row_works_630_i0.mono (by decide +kernel)
  · exact (placed21_template row_works_467 6 (8, 11)).mono (by decide +kernel)
  · exact (placed21_template row_works_627 0 (1, 3)).mono (by decide +kernel)
  · exact row_works_630_i1.mono (by decide +kernel)
  · exact row_works_630_i2.mono (by decide +kernel)
  · exact (placed21_template row_works_629 4 (1, 10)).mono (by decide +kernel)
  · exact row_works_630_i3.mono (by decide +kernel)
theorem row_works_630 : Template HasSnaky 17 required_630 envelope_630 := by
  refine compose HasSnaky 16 childrenC_630 childrenD_630 children_work_630 (4, 6)
    required_630 envelope_630 pivot_mem_630 child_required_sub_630 child_envelope_sub_630 ?_
  intro b hb
  exact common_sub_630 (mem_commonEnvelope childrenD_630 b hb)
def height_623_i0 : ℕ := 11
def childrenH_623_i0 : Fin 4 → ℕ := ![height_188, height_444, height_606, height_610]
theorem height_exact_623_i0 : height_623_i0 = 1 + Finset.univ.sup childrenH_623_i0 := by decide +kernel
theorem required_origin_623_i0 : ∀ x ∈ required_623_i0,
    (∃ j, x ∈ childrenC_623_i0 j) ∨ ∀ j, x ∈ childrenD_623_i0 j := by decide +kernel
theorem required_exact_623_i0 : required_623_i0 =
    ((Finset.univ.biUnion childrenC_623_i0) ∪ commonEnvelope childrenD_623_i0).erase (5, 5) := by
  exact required_eq_combination childrenC_623_i0 childrenD_623_i0 (5, 5) required_623_i0
    (by decide +kernel) child_required_sub_623_i0 common_sub_623_i0 required_origin_623_i0
theorem envelope_origin_623_i0 : ∀ x ∈ envelope_623_i0,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_623_i0 j := by decide +kernel
theorem envelope_exact_623_i0 : envelope_623_i0 =
    insert (5, 5) (Finset.univ.biUnion childrenD_623_i0) := by
  exact envelope_eq_combination childrenD_623_i0 (5, 5) envelope_623_i0
    pivot_mem_623_i0 child_envelope_sub_623_i0 envelope_origin_623_i0
def checked_623_i0 : CheckedCard where
  required := required_623_i0
  envelope := envelope_623_i0
  height := height_623_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_623_i0
def height_623_i1 : ℕ := 10
def childrenH_623_i1 : Fin 5 → ℕ := ![height_137, height_181, height_363, height_474, height_606]
theorem height_exact_623_i1 : height_623_i1 = 1 + Finset.univ.sup childrenH_623_i1 := by decide +kernel
theorem required_origin_623_i1 : ∀ x ∈ required_623_i1,
    (∃ j, x ∈ childrenC_623_i1 j) ∨ ∀ j, x ∈ childrenD_623_i1 j := by decide +kernel
theorem required_exact_623_i1 : required_623_i1 =
    ((Finset.univ.biUnion childrenC_623_i1) ∪ commonEnvelope childrenD_623_i1).erase (5, 5) := by
  exact required_eq_combination childrenC_623_i1 childrenD_623_i1 (5, 5) required_623_i1
    (by decide +kernel) child_required_sub_623_i1 common_sub_623_i1 required_origin_623_i1
theorem envelope_origin_623_i1 : ∀ x ∈ envelope_623_i1,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_623_i1 j := by decide +kernel
theorem envelope_exact_623_i1 : envelope_623_i1 =
    insert (5, 5) (Finset.univ.biUnion childrenD_623_i1) := by
  exact envelope_eq_combination childrenD_623_i1 (5, 5) envelope_623_i1
    pivot_mem_623_i1 child_envelope_sub_623_i1 envelope_origin_623_i1
def checked_623_i1 : CheckedCard where
  required := required_623_i1
  envelope := envelope_623_i1
  height := height_623_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_623_i1
def height_623_i4 : ℕ := 5
def childrenH_623_i4 : Fin 2 → ℕ := ![height_27, height_35]
theorem height_exact_623_i4 : height_623_i4 = 1 + Finset.univ.sup childrenH_623_i4 := by decide +kernel
theorem required_origin_623_i4 : ∀ x ∈ required_623_i4,
    (∃ j, x ∈ childrenC_623_i4 j) ∨ ∀ j, x ∈ childrenD_623_i4 j := by decide +kernel
theorem required_exact_623_i4 : required_623_i4 =
    ((Finset.univ.biUnion childrenC_623_i4) ∪ commonEnvelope childrenD_623_i4).erase (4, 7) := by
  exact required_eq_combination childrenC_623_i4 childrenD_623_i4 (4, 7) required_623_i4
    (by decide +kernel) child_required_sub_623_i4 common_sub_623_i4 required_origin_623_i4
theorem envelope_origin_623_i4 : ∀ x ∈ envelope_623_i4,
    x = (4, 7) ∨ ∃ j, x ∈ childrenD_623_i4 j := by decide +kernel
theorem envelope_exact_623_i4 : envelope_623_i4 =
    insert (4, 7) (Finset.univ.biUnion childrenD_623_i4) := by
  exact envelope_eq_combination childrenD_623_i4 (4, 7) envelope_623_i4
    pivot_mem_623_i4 child_envelope_sub_623_i4 envelope_origin_623_i4
def checked_623_i4 : CheckedCard where
  required := required_623_i4
  envelope := envelope_623_i4
  height := height_623_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_623_i4
def height_623_i3 : ℕ := 6
def childrenH_623_i3 : Fin 5 → ℕ := ![height_9, height_151, height_186, height_187, height_623_i4]
theorem height_exact_623_i3 : height_623_i3 = 1 + Finset.univ.sup childrenH_623_i3 := by decide +kernel
theorem required_origin_623_i3 : ∀ x ∈ required_623_i3,
    (∃ j, x ∈ childrenC_623_i3 j) ∨ ∀ j, x ∈ childrenD_623_i3 j := by decide +kernel
theorem required_exact_623_i3 : required_623_i3 =
    ((Finset.univ.biUnion childrenC_623_i3) ∪ commonEnvelope childrenD_623_i3).erase (5, 9) := by
  exact required_eq_combination childrenC_623_i3 childrenD_623_i3 (5, 9) required_623_i3
    (by decide +kernel) child_required_sub_623_i3 common_sub_623_i3 required_origin_623_i3
theorem envelope_origin_623_i3 : ∀ x ∈ envelope_623_i3,
    x = (5, 9) ∨ ∃ j, x ∈ childrenD_623_i3 j := by decide +kernel
theorem envelope_exact_623_i3 : envelope_623_i3 =
    insert (5, 9) (Finset.univ.biUnion childrenD_623_i3) := by
  exact envelope_eq_combination childrenD_623_i3 (5, 9) envelope_623_i3
    pivot_mem_623_i3 child_envelope_sub_623_i3 envelope_origin_623_i3
def checked_623_i3 : CheckedCard where
  required := required_623_i3
  envelope := envelope_623_i3
  height := height_623_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_623_i3
def height_623_i5 : ℕ := 10
def childrenH_623_i5 : Fin 3 → ℕ := ![height_179, height_371, height_443]
theorem height_exact_623_i5 : height_623_i5 = 1 + Finset.univ.sup childrenH_623_i5 := by decide +kernel
theorem required_origin_623_i5 : ∀ x ∈ required_623_i5,
    (∃ j, x ∈ childrenC_623_i5 j) ∨ ∀ j, x ∈ childrenD_623_i5 j := by decide +kernel
theorem required_exact_623_i5 : required_623_i5 =
    ((Finset.univ.biUnion childrenC_623_i5) ∪ commonEnvelope childrenD_623_i5).erase (5, 5) := by
  exact required_eq_combination childrenC_623_i5 childrenD_623_i5 (5, 5) required_623_i5
    (by decide +kernel) child_required_sub_623_i5 common_sub_623_i5 required_origin_623_i5
theorem envelope_origin_623_i5 : ∀ x ∈ envelope_623_i5,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_623_i5 j := by decide +kernel
theorem envelope_exact_623_i5 : envelope_623_i5 =
    insert (5, 5) (Finset.univ.biUnion childrenD_623_i5) := by
  exact envelope_eq_combination childrenD_623_i5 (5, 5) envelope_623_i5
    pivot_mem_623_i5 child_envelope_sub_623_i5 envelope_origin_623_i5
def checked_623_i5 : CheckedCard where
  required := required_623_i5
  envelope := envelope_623_i5
  height := height_623_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_623_i5
def height_623_i2 : ℕ := 11
def childrenH_623_i2 : Fin 7 → ℕ := ![height_12, height_188, height_211, height_623_i3, height_619, height_623_i5, height_620]
theorem height_exact_623_i2 : height_623_i2 = 1 + Finset.univ.sup childrenH_623_i2 := by decide +kernel
theorem required_origin_623_i2 : ∀ x ∈ required_623_i2,
    (∃ j, x ∈ childrenC_623_i2 j) ∨ ∀ j, x ∈ childrenD_623_i2 j := by decide +kernel
theorem required_exact_623_i2 : required_623_i2 =
    ((Finset.univ.biUnion childrenC_623_i2) ∪ commonEnvelope childrenD_623_i2).erase (5, 8) := by
  exact required_eq_combination childrenC_623_i2 childrenD_623_i2 (5, 8) required_623_i2
    (by decide +kernel) child_required_sub_623_i2 common_sub_623_i2 required_origin_623_i2
theorem envelope_origin_623_i2 : ∀ x ∈ envelope_623_i2,
    x = (5, 8) ∨ ∃ j, x ∈ childrenD_623_i2 j := by decide +kernel
theorem envelope_exact_623_i2 : envelope_623_i2 =
    insert (5, 8) (Finset.univ.biUnion childrenD_623_i2) := by
  exact envelope_eq_combination childrenD_623_i2 (5, 8) envelope_623_i2
    pivot_mem_623_i2 child_envelope_sub_623_i2 envelope_origin_623_i2
def checked_623_i2 : CheckedCard where
  required := required_623_i2
  envelope := envelope_623_i2
  height := height_623_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_623_i2
def height_623_i7 : ℕ := 7
def childrenH_623_i7 : Fin 3 → ℕ := ![height_179, height_197, height_465]
theorem height_exact_623_i7 : height_623_i7 = 1 + Finset.univ.sup childrenH_623_i7 := by decide +kernel
theorem required_origin_623_i7 : ∀ x ∈ required_623_i7,
    (∃ j, x ∈ childrenC_623_i7 j) ∨ ∀ j, x ∈ childrenD_623_i7 j := by decide +kernel
theorem required_exact_623_i7 : required_623_i7 =
    ((Finset.univ.biUnion childrenC_623_i7) ∪ commonEnvelope childrenD_623_i7).erase (5, 5) := by
  exact required_eq_combination childrenC_623_i7 childrenD_623_i7 (5, 5) required_623_i7
    (by decide +kernel) child_required_sub_623_i7 common_sub_623_i7 required_origin_623_i7
theorem envelope_origin_623_i7 : ∀ x ∈ envelope_623_i7,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_623_i7 j := by decide +kernel
theorem envelope_exact_623_i7 : envelope_623_i7 =
    insert (5, 5) (Finset.univ.biUnion childrenD_623_i7) := by
  exact envelope_eq_combination childrenD_623_i7 (5, 5) envelope_623_i7
    pivot_mem_623_i7 child_envelope_sub_623_i7 envelope_origin_623_i7
def checked_623_i7 : CheckedCard where
  required := required_623_i7
  envelope := envelope_623_i7
  height := height_623_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_623_i7
def height_623_i6 : ℕ := 10
def childrenH_623_i6 : Fin 6 → ℕ := ![height_12, height_322, height_369, height_435, height_623_i7, height_622]
theorem height_exact_623_i6 : height_623_i6 = 1 + Finset.univ.sup childrenH_623_i6 := by decide +kernel
theorem required_origin_623_i6 : ∀ x ∈ required_623_i6,
    (∃ j, x ∈ childrenC_623_i6 j) ∨ ∀ j, x ∈ childrenD_623_i6 j := by decide +kernel
theorem required_exact_623_i6 : required_623_i6 =
    ((Finset.univ.biUnion childrenC_623_i6) ∪ commonEnvelope childrenD_623_i6).erase (5, 8) := by
  exact required_eq_combination childrenC_623_i6 childrenD_623_i6 (5, 8) required_623_i6
    (by decide +kernel) child_required_sub_623_i6 common_sub_623_i6 required_origin_623_i6
theorem envelope_origin_623_i6 : ∀ x ∈ envelope_623_i6,
    x = (5, 8) ∨ ∃ j, x ∈ childrenD_623_i6 j := by decide +kernel
theorem envelope_exact_623_i6 : envelope_623_i6 =
    insert (5, 8) (Finset.univ.biUnion childrenD_623_i6) := by
  exact envelope_eq_combination childrenD_623_i6 (5, 8) envelope_623_i6
    pivot_mem_623_i6 child_envelope_sub_623_i6 envelope_origin_623_i6
def checked_623_i6 : CheckedCard where
  required := required_623_i6
  envelope := envelope_623_i6
  height := height_623_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_623_i6
def height_623 : ℕ := 17
def childrenH_623 : Fin 11 → ℕ := ![height_467, height_602, height_603, height_605, height_607, height_608, height_623_i0, height_618, height_623_i1, height_623_i2, height_623_i6]
theorem height_exact_623 : height_623 = 1 + Finset.univ.sup childrenH_623 := by decide +kernel
theorem required_origin_623 : ∀ x ∈ required_623,
    (∃ j, x ∈ childrenC_623 j) ∨ ∀ j, x ∈ childrenD_623 j := by decide +kernel
theorem required_exact_623 : required_623 =
    ((Finset.univ.biUnion childrenC_623) ∪ commonEnvelope childrenD_623).erase (5, 6) := by
  exact required_eq_combination childrenC_623 childrenD_623 (5, 6) required_623
    (by decide +kernel) child_required_sub_623 common_sub_623 required_origin_623
theorem envelope_origin_623 : ∀ x ∈ envelope_623,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_623 j := by decide +kernel
theorem envelope_exact_623 : envelope_623 =
    insert (5, 6) (Finset.univ.biUnion childrenD_623) := by
  exact envelope_eq_combination childrenD_623 (5, 6) envelope_623
    pivot_mem_623 child_envelope_sub_623 envelope_origin_623
def checked_623 : CheckedCard where
  required := required_623
  envelope := envelope_623
  height := height_623
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_623
def height_630_i0 : ℕ := 10
def childrenH_630_i0 : Fin 7 → ℕ := ![height_12, height_13, height_355, height_356, height_434, height_435, height_441]
theorem height_exact_630_i0 : height_630_i0 = 1 + Finset.univ.sup childrenH_630_i0 := by decide +kernel
theorem required_origin_630_i0 : ∀ x ∈ required_630_i0,
    (∃ j, x ∈ childrenC_630_i0 j) ∨ ∀ j, x ∈ childrenD_630_i0 j := by decide +kernel
theorem required_exact_630_i0 : required_630_i0 =
    ((Finset.univ.biUnion childrenC_630_i0) ∪ commonEnvelope childrenD_630_i0).erase (4, 8) := by
  exact required_eq_combination childrenC_630_i0 childrenD_630_i0 (4, 8) required_630_i0
    (by decide +kernel) child_required_sub_630_i0 common_sub_630_i0 required_origin_630_i0
theorem envelope_origin_630_i0 : ∀ x ∈ envelope_630_i0,
    x = (4, 8) ∨ ∃ j, x ∈ childrenD_630_i0 j := by decide +kernel
theorem envelope_exact_630_i0 : envelope_630_i0 =
    insert (4, 8) (Finset.univ.biUnion childrenD_630_i0) := by
  exact envelope_eq_combination childrenD_630_i0 (4, 8) envelope_630_i0
    pivot_mem_630_i0 child_envelope_sub_630_i0 envelope_origin_630_i0
def checked_630_i0 : CheckedCard where
  required := required_630_i0
  envelope := envelope_630_i0
  height := height_630_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_630_i0
def height_630_i1 : ℕ := 7
def childrenH_630_i1 : Fin 4 → ℕ := ![height_13, height_112, height_363, height_364]
theorem height_exact_630_i1 : height_630_i1 = 1 + Finset.univ.sup childrenH_630_i1 := by decide +kernel
theorem required_origin_630_i1 : ∀ x ∈ required_630_i1,
    (∃ j, x ∈ childrenC_630_i1 j) ∨ ∀ j, x ∈ childrenD_630_i1 j := by decide +kernel
theorem required_exact_630_i1 : required_630_i1 =
    ((Finset.univ.biUnion childrenC_630_i1) ∪ commonEnvelope childrenD_630_i1).erase (4, 5) := by
  exact required_eq_combination childrenC_630_i1 childrenD_630_i1 (4, 5) required_630_i1
    (by decide +kernel) child_required_sub_630_i1 common_sub_630_i1 required_origin_630_i1
theorem envelope_origin_630_i1 : ∀ x ∈ envelope_630_i1,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_630_i1 j := by decide +kernel
theorem envelope_exact_630_i1 : envelope_630_i1 =
    insert (4, 5) (Finset.univ.biUnion childrenD_630_i1) := by
  exact envelope_eq_combination childrenD_630_i1 (4, 5) envelope_630_i1
    pivot_mem_630_i1 child_envelope_sub_630_i1 envelope_origin_630_i1
def checked_630_i1 : CheckedCard where
  required := required_630_i1
  envelope := envelope_630_i1
  height := height_630_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_630_i1
def height_630_i2 : ℕ := 8
def childrenH_630_i2 : Fin 5 → ℕ := ![height_112, height_181, height_181, height_295, height_466]
theorem height_exact_630_i2 : height_630_i2 = 1 + Finset.univ.sup childrenH_630_i2 := by decide +kernel
theorem required_origin_630_i2 : ∀ x ∈ required_630_i2,
    (∃ j, x ∈ childrenC_630_i2 j) ∨ ∀ j, x ∈ childrenD_630_i2 j := by decide +kernel
theorem required_exact_630_i2 : required_630_i2 =
    ((Finset.univ.biUnion childrenC_630_i2) ∪ commonEnvelope childrenD_630_i2).erase (4, 5) := by
  exact required_eq_combination childrenC_630_i2 childrenD_630_i2 (4, 5) required_630_i2
    (by decide +kernel) child_required_sub_630_i2 common_sub_630_i2 required_origin_630_i2
theorem envelope_origin_630_i2 : ∀ x ∈ envelope_630_i2,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_630_i2 j := by decide +kernel
theorem envelope_exact_630_i2 : envelope_630_i2 =
    insert (4, 5) (Finset.univ.biUnion childrenD_630_i2) := by
  exact envelope_eq_combination childrenD_630_i2 (4, 5) envelope_630_i2
    pivot_mem_630_i2 child_envelope_sub_630_i2 envelope_origin_630_i2
def checked_630_i2 : CheckedCard where
  required := required_630_i2
  envelope := envelope_630_i2
  height := height_630_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_630_i2
def height_630_i4 : ℕ := 5
def childrenH_630_i4 : Fin 2 → ℕ := ![height_10, height_34]
theorem height_exact_630_i4 : height_630_i4 = 1 + Finset.univ.sup childrenH_630_i4 := by decide +kernel
theorem required_origin_630_i4 : ∀ x ∈ required_630_i4,
    (∃ j, x ∈ childrenC_630_i4 j) ∨ ∀ j, x ∈ childrenD_630_i4 j := by decide +kernel
theorem required_exact_630_i4 : required_630_i4 =
    ((Finset.univ.biUnion childrenC_630_i4) ∪ commonEnvelope childrenD_630_i4).erase (5, 7) := by
  exact required_eq_combination childrenC_630_i4 childrenD_630_i4 (5, 7) required_630_i4
    (by decide +kernel) child_required_sub_630_i4 common_sub_630_i4 required_origin_630_i4
theorem envelope_origin_630_i4 : ∀ x ∈ envelope_630_i4,
    x = (5, 7) ∨ ∃ j, x ∈ childrenD_630_i4 j := by decide +kernel
theorem envelope_exact_630_i4 : envelope_630_i4 =
    insert (5, 7) (Finset.univ.biUnion childrenD_630_i4) := by
  exact envelope_eq_combination childrenD_630_i4 (5, 7) envelope_630_i4
    pivot_mem_630_i4 child_envelope_sub_630_i4 envelope_origin_630_i4
def checked_630_i4 : CheckedCard where
  required := required_630_i4
  envelope := envelope_630_i4
  height := height_630_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_630_i4
def height_630_i3 : ℕ := 10
def childrenH_630_i3 : Fin 5 → ℕ := ![height_112, height_257, height_398, height_630_i4, height_628]
theorem height_exact_630_i3 : height_630_i3 = 1 + Finset.univ.sup childrenH_630_i3 := by decide +kernel
theorem required_origin_630_i3 : ∀ x ∈ required_630_i3,
    (∃ j, x ∈ childrenC_630_i3 j) ∨ ∀ j, x ∈ childrenD_630_i3 j := by decide +kernel
theorem required_exact_630_i3 : required_630_i3 =
    ((Finset.univ.biUnion childrenC_630_i3) ∪ commonEnvelope childrenD_630_i3).erase (4, 5) := by
  exact required_eq_combination childrenC_630_i3 childrenD_630_i3 (4, 5) required_630_i3
    (by decide +kernel) child_required_sub_630_i3 common_sub_630_i3 required_origin_630_i3
theorem envelope_origin_630_i3 : ∀ x ∈ envelope_630_i3,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_630_i3 j := by decide +kernel
theorem envelope_exact_630_i3 : envelope_630_i3 =
    insert (4, 5) (Finset.univ.biUnion childrenD_630_i3) := by
  exact envelope_eq_combination childrenD_630_i3 (4, 5) envelope_630_i3
    pivot_mem_630_i3 child_envelope_sub_630_i3 envelope_origin_630_i3
def checked_630_i3 : CheckedCard where
  required := required_630_i3
  envelope := envelope_630_i3
  height := height_630_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_630_i3
def height_630 : ℕ := 17
def childrenH_630 : Fin 9 → ℕ := ![height_368, height_368, height_630_i0, height_467, height_627, height_630_i1, height_630_i2, height_629, height_630_i3]
theorem height_exact_630 : height_630 = 1 + Finset.univ.sup childrenH_630 := by decide +kernel
theorem required_origin_630 : ∀ x ∈ required_630,
    (∃ j, x ∈ childrenC_630 j) ∨ ∀ j, x ∈ childrenD_630 j := by decide +kernel
theorem required_exact_630 : required_630 =
    ((Finset.univ.biUnion childrenC_630) ∪ commonEnvelope childrenD_630).erase (4, 6) := by
  exact required_eq_combination childrenC_630 childrenD_630 (4, 6) required_630
    (by decide +kernel) child_required_sub_630 common_sub_630 required_origin_630
theorem envelope_origin_630 : ∀ x ∈ envelope_630,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_630 j := by decide +kernel
theorem envelope_exact_630 : envelope_630 =
    insert (4, 6) (Finset.univ.biUnion childrenD_630) := by
  exact envelope_eq_combination childrenD_630 (4, 6) envelope_630
    pivot_mem_630 child_envelope_sub_630 envelope_origin_630
def checked_630 : CheckedCard where
  required := required_630
  envelope := envelope_630
  height := height_630
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_630
end SnakyPrototype.Certificate21

end OAI
