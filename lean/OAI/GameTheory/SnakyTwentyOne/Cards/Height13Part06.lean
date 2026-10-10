import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part07
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part08
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part05
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_695_i6 : Finset Cell := ⟨(([(1, 4), (1, 5), (1, 7), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_695_i6 : Finset Cell := ⟨(([(0, 7), (0, 8), (0, 9), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_695_i6 : Fin 3 → Finset Cell := ![(placed21 0 (1, 3) required_11), (placed21 2 (2, 2) required_75), (placed21 4 (1, 7) required_103)]
def childrenD_695_i6 : Fin 3 → Finset Cell := ![(placed21 0 (1, 3) envelope_11), (placed21 2 (2, 2) envelope_75), (placed21 4 (1, 7) envelope_103)]
theorem common_sub_695_i6 : commonEnvelope childrenD_695_i6 ⊆ insert (1, 6) required_695_i6 := by decide +kernel
theorem child_required_sub_695_i6 : ∀ j, childrenC_695_i6 j ⊆ insert (1, 6) required_695_i6 := by decide +kernel
theorem child_envelope_sub_695_i6 : ∀ j, childrenD_695_i6 j ⊆ envelope_695_i6 := by decide +kernel
theorem pivot_mem_695_i6 : (1, 6) ∈ envelope_695_i6 := by decide +kernel
theorem children_work_695_i6 : ∀ j, Template HasSnaky 4 (childrenC_695_i6 j) (childrenD_695_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 0 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_75 2 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_103 4 (1, 7)).mono (by decide +kernel)
theorem row_works_695_i6 : Template HasSnaky 5 required_695_i6 envelope_695_i6 := by
  refine compose HasSnaky 4 childrenC_695_i6 childrenD_695_i6 children_work_695_i6 (1, 6)
    required_695_i6 envelope_695_i6 pivot_mem_695_i6 child_required_sub_695_i6 child_envelope_sub_695_i6 ?_
  intro b hb
  exact common_sub_695_i6 (mem_commonEnvelope childrenD_695_i6 b hb)
def required_695_i7 : Finset Cell := ⟨(([(1, 4), (1, 5), (1, 7), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_695_i7 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 7), (0, 8), (0, 9), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 8), (2, 9), (2, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_695_i7 : Fin 3 → Finset Cell := ![(placed21 0 (1, 3) required_11), (placed21 2 (2, 4) required_17), (placed21 7 (2, 7) required_90)]
def childrenD_695_i7 : Fin 3 → Finset Cell := ![(placed21 0 (1, 3) envelope_11), (placed21 2 (2, 4) envelope_17), (placed21 7 (2, 7) envelope_90)]
theorem common_sub_695_i7 : commonEnvelope childrenD_695_i7 ⊆ insert (1, 6) required_695_i7 := by decide +kernel
theorem child_required_sub_695_i7 : ∀ j, childrenC_695_i7 j ⊆ insert (1, 6) required_695_i7 := by decide +kernel
theorem child_envelope_sub_695_i7 : ∀ j, childrenD_695_i7 j ⊆ envelope_695_i7 := by decide +kernel
theorem pivot_mem_695_i7 : (1, 6) ∈ envelope_695_i7 := by decide +kernel
theorem children_work_695_i7 : ∀ j, Template HasSnaky 4 (childrenC_695_i7 j) (childrenD_695_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 0 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_17 2 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_90 7 (2, 7)).mono (by decide +kernel)
theorem row_works_695_i7 : Template HasSnaky 5 required_695_i7 envelope_695_i7 := by
  refine compose HasSnaky 4 childrenC_695_i7 childrenD_695_i7 children_work_695_i7 (1, 6)
    required_695_i7 envelope_695_i7 pivot_mem_695_i7 child_required_sub_695_i7 child_envelope_sub_695_i7 ?_
  intro b hb
  exact common_sub_695_i7 (mem_commonEnvelope childrenD_695_i7 b hb)
def required_695_i5 : Finset Cell := ⟨(([(1, 4), (1, 5), (2, 5), (3, 8), (4, 5), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_695_i5 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 7), (0, 8), (0, 9), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 8), (3, 9), (4, 5), (4, 6), (4, 7), (4, 8), (5, 8), (5, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_695_i5 : Fin 4 → Finset Cell := ![(placed21 6 (2, 8) required_308), (placed21 5 (5, 5) required_348), required_695_i6, required_695_i7]
def childrenD_695_i5 : Fin 4 → Finset Cell := ![(placed21 6 (2, 8) envelope_308), (placed21 5 (5, 5) envelope_348), envelope_695_i6, envelope_695_i7]
theorem common_sub_695_i5 : commonEnvelope childrenD_695_i5 ⊆ insert (1, 7) required_695_i5 := by decide +kernel
theorem child_required_sub_695_i5 : ∀ j, childrenC_695_i5 j ⊆ insert (1, 7) required_695_i5 := by decide +kernel
theorem child_envelope_sub_695_i5 : ∀ j, childrenD_695_i5 j ⊆ envelope_695_i5 := by decide +kernel
theorem pivot_mem_695_i5 : (1, 7) ∈ envelope_695_i5 := by decide +kernel
theorem children_work_695_i5 : ∀ j, Template HasSnaky 6 (childrenC_695_i5 j) (childrenD_695_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_308 6 (2, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_348 5 (5, 5)).mono (by decide +kernel)
  · exact row_works_695_i6.mono (by decide +kernel)
  · exact row_works_695_i7.mono (by decide +kernel)
theorem row_works_695_i5 : Template HasSnaky 7 required_695_i5 envelope_695_i5 := by
  refine compose HasSnaky 6 childrenC_695_i5 childrenD_695_i5 children_work_695_i5 (1, 7)
    required_695_i5 envelope_695_i5 pivot_mem_695_i5 child_required_sub_695_i5 child_envelope_sub_695_i5 ?_
  intro b hb
  exact common_sub_695_i5 (mem_commonEnvelope childrenD_695_i5 b hb)
def required_695_i4 : Finset Cell := ⟨(([(1, 5), (2, 5), (3, 5), (3, 8), (4, 5), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_695_i4 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 7), (0, 8), (0, 9), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 5), (3, 8), (3, 9), (4, 5), (4, 6), (4, 7), (4, 8), (5, 8), (5, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_695_i4 : Fin 2 → Finset Cell := ![(placed21 6 (4, 5) required_5), required_695_i5]
def childrenD_695_i4 : Fin 2 → Finset Cell := ![(placed21 6 (4, 5) envelope_5), envelope_695_i5]
theorem common_sub_695_i4 : commonEnvelope childrenD_695_i4 ⊆ insert (1, 4) required_695_i4 := by decide +kernel
theorem child_required_sub_695_i4 : ∀ j, childrenC_695_i4 j ⊆ insert (1, 4) required_695_i4 := by decide +kernel
theorem child_envelope_sub_695_i4 : ∀ j, childrenD_695_i4 j ⊆ envelope_695_i4 := by decide +kernel
theorem pivot_mem_695_i4 : (1, 4) ∈ envelope_695_i4 := by decide +kernel
theorem children_work_695_i4 : ∀ j, Template HasSnaky 7 (childrenC_695_i4 j) (childrenD_695_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 6 (4, 5)).mono (by decide +kernel)
  · exact row_works_695_i5.mono (by decide +kernel)
theorem row_works_695_i4 : Template HasSnaky 8 required_695_i4 envelope_695_i4 := by
  refine compose HasSnaky 7 childrenC_695_i4 childrenD_695_i4 children_work_695_i4 (1, 4)
    required_695_i4 envelope_695_i4 pivot_mem_695_i4 child_required_sub_695_i4 child_envelope_sub_695_i4 ?_
  intro b hb
  exact common_sub_695_i4 (mem_commonEnvelope childrenD_695_i4 b hb)
def required_695_i3 : Finset Cell := ⟨(([(1, 5), (2, 5), (3, 5), (4, 5), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_695_i3 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 7), (0, 8), (0, 9), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 5), (3, 7), (3, 8), (3, 9), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 4), (5, 8), (5, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_695_i3 : Fin 2 → Finset Cell := ![(placed21 0 (1, 4) required_96), required_695_i4]
def childrenD_695_i3 : Fin 2 → Finset Cell := ![(placed21 0 (1, 4) envelope_96), envelope_695_i4]
theorem common_sub_695_i3 : commonEnvelope childrenD_695_i3 ⊆ insert (3, 8) required_695_i3 := by decide +kernel
theorem child_required_sub_695_i3 : ∀ j, childrenC_695_i3 j ⊆ insert (3, 8) required_695_i3 := by decide +kernel
theorem child_envelope_sub_695_i3 : ∀ j, childrenD_695_i3 j ⊆ envelope_695_i3 := by decide +kernel
theorem pivot_mem_695_i3 : (3, 8) ∈ envelope_695_i3 := by decide +kernel
theorem children_work_695_i3 : ∀ j, Template HasSnaky 8 (childrenC_695_i3 j) (childrenD_695_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_96 0 (1, 4)).mono (by decide +kernel)
  · exact row_works_695_i4.mono (by decide +kernel)
theorem row_works_695_i3 : Template HasSnaky 9 required_695_i3 envelope_695_i3 := by
  refine compose HasSnaky 8 childrenC_695_i3 childrenD_695_i3 children_work_695_i3 (3, 8)
    required_695_i3 envelope_695_i3 pivot_mem_695_i3 child_required_sub_695_i3 child_envelope_sub_695_i3 ?_
  intro b hb
  exact common_sub_695_i3 (mem_commonEnvelope childrenD_695_i3 b hb)
def required_695_i2 : Finset Cell := ⟨(([(2, 5), (3, 5), (4, 5), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_695_i2 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 7), (0, 8), (0, 9), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 5), (3, 7), (3, 8), (3, 9), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 4), (5, 6), (5, 8), (5, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_695_i2 : Fin 2 → Finset Cell := ![(placed21 0 (1, 5) required_5), required_695_i3]
def childrenD_695_i2 : Fin 2 → Finset Cell := ![(placed21 0 (1, 5) envelope_5), envelope_695_i3]
theorem common_sub_695_i2 : commonEnvelope childrenD_695_i2 ⊆ insert (1, 5) required_695_i2 := by decide +kernel
theorem child_required_sub_695_i2 : ∀ j, childrenC_695_i2 j ⊆ insert (1, 5) required_695_i2 := by decide +kernel
theorem child_envelope_sub_695_i2 : ∀ j, childrenD_695_i2 j ⊆ envelope_695_i2 := by decide +kernel
theorem pivot_mem_695_i2 : (1, 5) ∈ envelope_695_i2 := by decide +kernel
theorem children_work_695_i2 : ∀ j, Template HasSnaky 9 (childrenC_695_i2 j) (childrenD_695_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (1, 5)).mono (by decide +kernel)
  · exact row_works_695_i3.mono (by decide +kernel)
theorem row_works_695_i2 : Template HasSnaky 10 required_695_i2 envelope_695_i2 := by
  refine compose HasSnaky 9 childrenC_695_i2 childrenD_695_i2 children_work_695_i2 (1, 5)
    required_695_i2 envelope_695_i2 pivot_mem_695_i2 child_required_sub_695_i2 child_envelope_sub_695_i2 ?_
  intro b hb
  exact common_sub_695_i2 (mem_commonEnvelope childrenD_695_i2 b hb)
def required_695_i1 : Finset Cell := ⟨(([(2, 5), (3, 5), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_695_i1 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 7), (0, 8), (0, 9), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 5), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, 6), (6, 7), (6, 8), (7, 6), (7, 7), (7, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_695_i1 : Fin 6 → Finset Cell := ![(placed21 2 (5, 3) required_67), (placed21 6 (5, 9) required_175), (placed21 1 (1, 4) required_228), (placed21 5 (7, 4) required_435), (placed21 1 (0, 5) required_688), required_695_i2]
def childrenD_695_i1 : Fin 6 → Finset Cell := ![(placed21 2 (5, 3) envelope_67), (placed21 6 (5, 9) envelope_175), (placed21 1 (1, 4) envelope_228), (placed21 5 (7, 4) envelope_435), (placed21 1 (0, 5) envelope_688), envelope_695_i2]
theorem common_sub_695_i1 : commonEnvelope childrenD_695_i1 ⊆ insert (4, 7) required_695_i1 := by decide +kernel
theorem child_required_sub_695_i1 : ∀ j, childrenC_695_i1 j ⊆ insert (4, 7) required_695_i1 := by decide +kernel
theorem child_envelope_sub_695_i1 : ∀ j, childrenD_695_i1 j ⊆ envelope_695_i1 := by decide +kernel
theorem pivot_mem_695_i1 : (4, 7) ∈ envelope_695_i1 := by decide +kernel
theorem children_work_695_i1 : ∀ j, Template HasSnaky 10 (childrenC_695_i1 j) (childrenD_695_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_67 2 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_175 6 (5, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_228 1 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 5 (7, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_688 1 (0, 5)).mono (by decide +kernel)
  · exact row_works_695_i2.mono (by decide +kernel)
theorem row_works_695_i1 : Template HasSnaky 11 required_695_i1 envelope_695_i1 := by
  refine compose HasSnaky 10 childrenC_695_i1 childrenD_695_i1 children_work_695_i1 (4, 7)
    required_695_i1 envelope_695_i1 pivot_mem_695_i1 child_required_sub_695_i1 child_envelope_sub_695_i1 ?_
  intro b hb
  exact common_sub_695_i1 (mem_commonEnvelope childrenD_695_i1 b hb)
def required_695_i0 : Finset Cell := ⟨(([(2, 5), (3, 5), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_695_i0 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 7), (0, 8), (0, 9), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 1), (3, 2), (3, 3), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 1), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, 6), (6, 7), (6, 8), (7, 6), (7, 7), (7, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_695_i0 : Fin 4 → Finset Cell := ![(placed21 1 (1, 5) required_44), (placed21 2 (5, 1) required_324), (placed21 0 (0, 2) required_686), required_695_i1]
def childrenD_695_i0 : Fin 4 → Finset Cell := ![(placed21 1 (1, 5) envelope_44), (placed21 2 (5, 1) envelope_324), (placed21 0 (0, 2) envelope_686), envelope_695_i1]
theorem common_sub_695_i0 : commonEnvelope childrenD_695_i0 ⊆ insert (4, 6) required_695_i0 := by decide +kernel
theorem child_required_sub_695_i0 : ∀ j, childrenC_695_i0 j ⊆ insert (4, 6) required_695_i0 := by decide +kernel
theorem child_envelope_sub_695_i0 : ∀ j, childrenD_695_i0 j ⊆ envelope_695_i0 := by decide +kernel
theorem pivot_mem_695_i0 : (4, 6) ∈ envelope_695_i0 := by decide +kernel
theorem children_work_695_i0 : ∀ j, Template HasSnaky 11 (childrenC_695_i0 j) (childrenD_695_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 1 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_324 2 (5, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_686 0 (0, 2)).mono (by decide +kernel)
  · exact row_works_695_i1.mono (by decide +kernel)
theorem row_works_695_i0 : Template HasSnaky 12 required_695_i0 envelope_695_i0 := by
  refine compose HasSnaky 11 childrenC_695_i0 childrenD_695_i0 children_work_695_i0 (4, 6)
    required_695_i0 envelope_695_i0 pivot_mem_695_i0 child_required_sub_695_i0 child_envelope_sub_695_i0 ?_
  intro b hb
  exact common_sub_695_i0 (mem_commonEnvelope childrenD_695_i0 b hb)
def required_695 : Finset Cell := ⟨(([(2, 5), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_695 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 7), (0, 8), (0, 9), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 1), (3, 2), (3, 3), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 4), (7, 6), (7, 7), (7, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_695 : Fin 5 → Finset Cell := ![(placed21 1 (0, 4) required_12), (placed21 4 (1, 8) required_118), (placed21 1 (0, 3) required_135), (placed21 3 (0, 7) required_182), required_695_i0]
def childrenD_695 : Fin 5 → Finset Cell := ![(placed21 1 (0, 4) envelope_12), (placed21 4 (1, 8) envelope_118), (placed21 1 (0, 3) envelope_135), (placed21 3 (0, 7) envelope_182), envelope_695_i0]
theorem common_sub_695 : commonEnvelope childrenD_695 ⊆ insert (4, 5) required_695 := by decide +kernel
theorem child_required_sub_695 : ∀ j, childrenC_695 j ⊆ insert (4, 5) required_695 := by decide +kernel
theorem child_envelope_sub_695 : ∀ j, childrenD_695 j ⊆ envelope_695 := by decide +kernel
theorem pivot_mem_695 : (4, 5) ∈ envelope_695 := by decide +kernel
theorem children_work_695 : ∀ j, Template HasSnaky 12 (childrenC_695 j) (childrenD_695 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 1 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_118 4 (1, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_135 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_182 3 (0, 7)).mono (by decide +kernel)
  · exact row_works_695_i0.mono (by decide +kernel)
theorem row_works_695 : Template HasSnaky 13 required_695 envelope_695 := by
  refine compose HasSnaky 12 childrenC_695 childrenD_695 children_work_695 (4, 5)
    required_695 envelope_695 pivot_mem_695 child_required_sub_695 child_envelope_sub_695 ?_
  intro b hb
  exact common_sub_695 (mem_commonEnvelope childrenD_695 b hb)
def required_696_i1 : Finset Cell := ⟨(([(4, 4), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_696_i1 : Finset Cell := ⟨(([(4, 3), (4, 4), (4, 8), (4, 9), (4, 10), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_696_i1 : Fin 2 → Finset Cell := ![(placed21 7 (5, 7) required_5), (placed21 5 (6, 4) required_197)]
def childrenD_696_i1 : Fin 2 → Finset Cell := ![(placed21 7 (5, 7) envelope_5), (placed21 5 (6, 4) envelope_197)]
theorem common_sub_696_i1 : commonEnvelope childrenD_696_i1 ⊆ insert (5, 7) required_696_i1 := by decide +kernel
theorem child_required_sub_696_i1 : ∀ j, childrenC_696_i1 j ⊆ insert (5, 7) required_696_i1 := by decide +kernel
theorem child_envelope_sub_696_i1 : ∀ j, childrenD_696_i1 j ⊆ envelope_696_i1 := by decide +kernel
theorem pivot_mem_696_i1 : (5, 7) ∈ envelope_696_i1 := by decide +kernel
theorem children_work_696_i1 : ∀ j, Template HasSnaky 5 (childrenC_696_i1 j) (childrenD_696_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (5, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_197 5 (6, 4)).mono (by decide +kernel)
theorem row_works_696_i1 : Template HasSnaky 6 required_696_i1 envelope_696_i1 := by
  refine compose HasSnaky 5 childrenC_696_i1 childrenD_696_i1 children_work_696_i1 (5, 7)
    required_696_i1 envelope_696_i1 pivot_mem_696_i1 child_required_sub_696_i1 child_envelope_sub_696_i1 ?_
  intro b hb
  exact common_sub_696_i1 (mem_commonEnvelope childrenD_696_i1 b hb)
def required_696_i0 : Finset Cell := ⟨(([(5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_696_i0 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (1, 7), (1, 9), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 8), (4, 9), (4, 10), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 3), (7, 4), (7, 5), (8, 3), (8, 4), (8, 5), (9, 3), (9, 4), (9, 5), (10, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_696_i0 : Fin 4 → Finset Cell := ![(placed21 3 (1, 7) required_317), required_696_i1, (placed21 7 (8, 7) required_436), (placed21 6 (8, 9) required_685)]
def childrenD_696_i0 : Fin 4 → Finset Cell := ![(placed21 3 (1, 7) envelope_317), envelope_696_i1, (placed21 7 (8, 7) envelope_436), (placed21 6 (8, 9) envelope_685)]
theorem common_sub_696_i0 : commonEnvelope childrenD_696_i0 ⊆ insert (4, 4) required_696_i0 := by decide +kernel
theorem child_required_sub_696_i0 : ∀ j, childrenC_696_i0 j ⊆ insert (4, 4) required_696_i0 := by decide +kernel
theorem child_envelope_sub_696_i0 : ∀ j, childrenD_696_i0 j ⊆ envelope_696_i0 := by decide +kernel
theorem pivot_mem_696_i0 : (4, 4) ∈ envelope_696_i0 := by decide +kernel
theorem children_work_696_i0 : ∀ j, Template HasSnaky 11 (childrenC_696_i0 j) (childrenD_696_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_317 3 (1, 7)).mono (by decide +kernel)
  · exact row_works_696_i1.mono (by decide +kernel)
  · exact (placed21_template row_works_436 7 (8, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_685 6 (8, 9)).mono (by decide +kernel)
theorem row_works_696_i0 : Template HasSnaky 12 required_696_i0 envelope_696_i0 := by
  refine compose HasSnaky 11 childrenC_696_i0 childrenD_696_i0 children_work_696_i0 (4, 4)
    required_696_i0 envelope_696_i0 pivot_mem_696_i0 child_required_sub_696_i0 child_envelope_sub_696_i0 ?_
  intro b hb
  exact common_sub_696_i0 (mem_commonEnvelope childrenD_696_i0 b hb)
def required_696 : Finset Cell := ⟨(([(5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_696 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (1, 7), (1, 9), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 6), (4, 8), (4, 9), (4, 10), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (10, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_696 : Fin 6 → Finset Cell := ![(placed21 6 (6, 8) required_12), (placed21 7 (9, 7) required_322), (placed21 2 (6, 1) required_369), (placed21 7 (8, 7) required_435), (placed21 0 (2, 1) required_622), required_696_i0]
def childrenD_696 : Fin 6 → Finset Cell := ![(placed21 6 (6, 8) envelope_12), (placed21 7 (9, 7) envelope_322), (placed21 2 (6, 1) envelope_369), (placed21 7 (8, 7) envelope_435), (placed21 0 (2, 1) envelope_622), envelope_696_i0]
theorem common_sub_696 : commonEnvelope childrenD_696 ⊆ insert (5, 4) required_696 := by decide +kernel
theorem child_required_sub_696 : ∀ j, childrenC_696 j ⊆ insert (5, 4) required_696 := by decide +kernel
theorem child_envelope_sub_696 : ∀ j, childrenD_696 j ⊆ envelope_696 := by decide +kernel
theorem pivot_mem_696 : (5, 4) ∈ envelope_696 := by decide +kernel
theorem children_work_696 : ∀ j, Template HasSnaky 12 (childrenC_696 j) (childrenD_696 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 6 (6, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_322 7 (9, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_369 2 (6, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 7 (8, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_622 0 (2, 1)).mono (by decide +kernel)
  · exact row_works_696_i0.mono (by decide +kernel)
theorem row_works_696 : Template HasSnaky 13 required_696 envelope_696 := by
  refine compose HasSnaky 12 childrenC_696 childrenD_696 children_work_696 (5, 4)
    required_696 envelope_696 pivot_mem_696 child_required_sub_696 child_envelope_sub_696 ?_
  intro b hb
  exact common_sub_696 (mem_commonEnvelope childrenD_696 b hb)
def required_709_i2 : Finset Cell := ⟨(([(5, 4), (5, 5), (5, 6), (5, 7), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_709_i2 : Finset Cell := ⟨(([(2, 5), (3, 5), (4, 4), (4, 5), (5, 4), (5, 5), (5, 6), (5, 7), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 3), (7, 4), (7, 5), (7, 6), (8, 4), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_709_i2 : Fin 3 → Finset Cell := ![(placed21 1 (2, 5) required_53), (placed21 3 (2, 7) required_56), (placed21 0 (4, 3) required_392)]
def childrenD_709_i2 : Fin 3 → Finset Cell := ![(placed21 1 (2, 5) envelope_53), (placed21 3 (2, 7) envelope_56), (placed21 0 (4, 3) envelope_392)]
theorem common_sub_709_i2 : commonEnvelope childrenD_709_i2 ⊆ insert (4, 5) required_709_i2 := by decide +kernel
theorem child_required_sub_709_i2 : ∀ j, childrenC_709_i2 j ⊆ insert (4, 5) required_709_i2 := by decide +kernel
theorem child_envelope_sub_709_i2 : ∀ j, childrenD_709_i2 j ⊆ envelope_709_i2 := by decide +kernel
theorem pivot_mem_709_i2 : (4, 5) ∈ envelope_709_i2 := by decide +kernel
theorem children_work_709_i2 : ∀ j, Template HasSnaky 6 (childrenC_709_i2 j) (childrenD_709_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_53 1 (2, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_56 3 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_392 0 (4, 3)).mono (by decide +kernel)
theorem row_works_709_i2 : Template HasSnaky 7 required_709_i2 envelope_709_i2 := by
  refine compose HasSnaky 6 childrenC_709_i2 childrenD_709_i2 children_work_709_i2 (4, 5)
    required_709_i2 envelope_709_i2 pivot_mem_709_i2 child_required_sub_709_i2 child_envelope_sub_709_i2 ?_
  intro b hb
  exact common_sub_709_i2 (mem_commonEnvelope childrenD_709_i2 b hb)
def required_709_i1 : Finset Cell := ⟨(([(5, 5), (5, 6), (5, 7), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_709_i1 : Finset Cell := ⟨(([(2, 5), (3, 5), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 3), (7, 4), (7, 5), (7, 6), (8, 4), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_709_i1 : Fin 3 → Finset Cell := ![(placed21 4 (5, 8) required_11), (placed21 7 (8, 7) required_253), required_709_i2]
def childrenD_709_i1 : Fin 3 → Finset Cell := ![(placed21 4 (5, 8) envelope_11), (placed21 7 (8, 7) envelope_253), envelope_709_i2]
theorem common_sub_709_i1 : commonEnvelope childrenD_709_i1 ⊆ insert (5, 4) required_709_i1 := by decide +kernel
theorem child_required_sub_709_i1 : ∀ j, childrenC_709_i1 j ⊆ insert (5, 4) required_709_i1 := by decide +kernel
theorem child_envelope_sub_709_i1 : ∀ j, childrenD_709_i1 j ⊆ envelope_709_i1 := by decide +kernel
theorem pivot_mem_709_i1 : (5, 4) ∈ envelope_709_i1 := by decide +kernel
theorem children_work_709_i1 : ∀ j, Template HasSnaky 7 (childrenC_709_i1 j) (childrenD_709_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 4 (5, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_253 7 (8, 7)).mono (by decide +kernel)
  · exact row_works_709_i2.mono (by decide +kernel)
theorem row_works_709_i1 : Template HasSnaky 8 required_709_i1 envelope_709_i1 := by
  refine compose HasSnaky 7 childrenC_709_i1 childrenD_709_i1 children_work_709_i1 (5, 4)
    required_709_i1 envelope_709_i1 pivot_mem_709_i1 child_required_sub_709_i1 child_envelope_sub_709_i1 ?_
  intro b hb
  exact common_sub_709_i1 (mem_commonEnvelope childrenD_709_i1 b hb)
def required_709_i4 : Finset Cell := ⟨(([(5, 4), (5, 5), (5, 6), (5, 7), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_709_i4 : Finset Cell := ⟨(([(4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_709_i4 : Fin 2 → Finset Cell := ![(placed21 4 (5, 7) required_6), (placed21 6 (6, 6) required_89)]
def childrenD_709_i4 : Fin 2 → Finset Cell := ![(placed21 4 (5, 7) envelope_6), (placed21 6 (6, 6) envelope_89)]
theorem common_sub_709_i4 : commonEnvelope childrenD_709_i4 ⊆ insert (5, 3) required_709_i4 := by decide +kernel
theorem child_required_sub_709_i4 : ∀ j, childrenC_709_i4 j ⊆ insert (5, 3) required_709_i4 := by decide +kernel
theorem child_envelope_sub_709_i4 : ∀ j, childrenD_709_i4 j ⊆ envelope_709_i4 := by decide +kernel
theorem pivot_mem_709_i4 : (5, 3) ∈ envelope_709_i4 := by decide +kernel
theorem children_work_709_i4 : ∀ j, Template HasSnaky 4 (childrenC_709_i4 j) (childrenD_709_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 4 (5, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_89 6 (6, 6)).mono (by decide +kernel)
theorem row_works_709_i4 : Template HasSnaky 5 required_709_i4 envelope_709_i4 := by
  refine compose HasSnaky 4 childrenC_709_i4 childrenD_709_i4 children_work_709_i4 (5, 3)
    required_709_i4 envelope_709_i4 pivot_mem_709_i4 child_required_sub_709_i4 child_envelope_sub_709_i4 ?_
  intro b hb
  exact common_sub_709_i4 (mem_commonEnvelope childrenD_709_i4 b hb)
def required_709_i3 : Finset Cell := ⟨(([(5, 5), (5, 6), (5, 7), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_709_i3 : Finset Cell := ⟨(([(4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 3), (7, 4), (7, 7), (7, 8), (8, 4), (8, 7), (9, 4), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_709_i3 : Fin 3 → Finset Cell := ![(placed21 4 (5, 8) required_11), (placed21 4 (4, 8) required_521), required_709_i4]
def childrenD_709_i3 : Fin 3 → Finset Cell := ![(placed21 4 (5, 8) envelope_11), (placed21 4 (4, 8) envelope_521), envelope_709_i4]
theorem common_sub_709_i3 : commonEnvelope childrenD_709_i3 ⊆ insert (5, 4) required_709_i3 := by decide +kernel
theorem child_required_sub_709_i3 : ∀ j, childrenC_709_i3 j ⊆ insert (5, 4) required_709_i3 := by decide +kernel
theorem child_envelope_sub_709_i3 : ∀ j, childrenD_709_i3 j ⊆ envelope_709_i3 := by decide +kernel
theorem pivot_mem_709_i3 : (5, 4) ∈ envelope_709_i3 := by decide +kernel
theorem children_work_709_i3 : ∀ j, Template HasSnaky 6 (childrenC_709_i3 j) (childrenD_709_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 4 (5, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_521 4 (4, 8)).mono (by decide +kernel)
  · exact row_works_709_i4.mono (by decide +kernel)
theorem row_works_709_i3 : Template HasSnaky 7 required_709_i3 envelope_709_i3 := by
  refine compose HasSnaky 6 childrenC_709_i3 childrenD_709_i3 children_work_709_i3 (5, 4)
    required_709_i3 envelope_709_i3 pivot_mem_709_i3 child_required_sub_709_i3 child_envelope_sub_709_i3 ?_
  intro b hb
  exact common_sub_709_i3 (mem_commonEnvelope childrenD_709_i3 b hb)
def required_709_i0 : Finset Cell := ⟨(([(5, 5), (5, 6), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_709_i0 : Finset Cell := ⟨(([(0, 5), (1, 5), (1, 6), (1, 7), (2, 5), (2, 6), (2, 7), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (11, 7), (11, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_709_i0 : Fin 7 → Finset Cell := ![(placed21 5 (9, 3) required_524), (placed21 7 (9, 9) required_536), (placed21 7 (10, 7) required_545), (placed21 5 (10, 3) required_655), (placed21 4 (1, 11) required_664), required_709_i1, required_709_i3]
def childrenD_709_i0 : Fin 7 → Finset Cell := ![(placed21 5 (9, 3) envelope_524), (placed21 7 (9, 9) envelope_536), (placed21 7 (10, 7) envelope_545), (placed21 5 (10, 3) envelope_655), (placed21 4 (1, 11) envelope_664), envelope_709_i1, envelope_709_i3]
theorem common_sub_709_i0 : commonEnvelope childrenD_709_i0 ⊆ insert (6, 6) required_709_i0 := by decide +kernel
theorem child_required_sub_709_i0 : ∀ j, childrenC_709_i0 j ⊆ insert (6, 6) required_709_i0 := by decide +kernel
theorem child_envelope_sub_709_i0 : ∀ j, childrenD_709_i0 j ⊆ envelope_709_i0 := by decide +kernel
theorem pivot_mem_709_i0 : (6, 6) ∈ envelope_709_i0 := by decide +kernel
theorem children_work_709_i0 : ∀ j, Template HasSnaky 11 (childrenC_709_i0 j) (childrenD_709_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_524 5 (9, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_536 7 (9, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_545 7 (10, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_655 5 (10, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_664 4 (1, 11)).mono (by decide +kernel)
  · exact row_works_709_i1.mono (by decide +kernel)
  · exact row_works_709_i3.mono (by decide +kernel)
theorem row_works_709_i0 : Template HasSnaky 12 required_709_i0 envelope_709_i0 := by
  refine compose HasSnaky 11 childrenC_709_i0 childrenD_709_i0 children_work_709_i0 (6, 6)
    required_709_i0 envelope_709_i0 pivot_mem_709_i0 child_required_sub_709_i0 child_envelope_sub_709_i0 ?_
  intro b hb
  exact common_sub_709_i0 (mem_commonEnvelope childrenD_709_i0 b hb)
def required_709 : Finset Cell := ⟨(([(5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_709 : Finset Cell := ⟨(([(0, 5), (1, 4), (1, 5), (1, 6), (1, 7), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 8), (4, 9), (4, 10), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (11, 7), (11, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_709 : Fin 4 → Finset Cell := ![(placed21 2 (6, 3) required_14), (placed21 5 (8, 4) required_116), (placed21 5 (7, 4) required_181), required_709_i0]
def childrenD_709 : Fin 4 → Finset Cell := ![(placed21 2 (6, 3) envelope_14), (placed21 5 (8, 4) envelope_116), (placed21 5 (7, 4) envelope_181), envelope_709_i0]
theorem common_sub_709 : commonEnvelope childrenD_709 ⊆ insert (5, 7) required_709 := by decide +kernel
theorem child_required_sub_709 : ∀ j, childrenC_709 j ⊆ insert (5, 7) required_709 := by decide +kernel
theorem child_envelope_sub_709 : ∀ j, childrenD_709 j ⊆ envelope_709 := by decide +kernel
theorem pivot_mem_709 : (5, 7) ∈ envelope_709 := by decide +kernel
theorem children_work_709 : ∀ j, Template HasSnaky 12 (childrenC_709 j) (childrenD_709 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_14 2 (6, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_116 5 (8, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_181 5 (7, 4)).mono (by decide +kernel)
  · exact row_works_709_i0.mono (by decide +kernel)
theorem row_works_709 : Template HasSnaky 13 required_709 envelope_709 := by
  refine compose HasSnaky 12 childrenC_709 childrenD_709 children_work_709 (5, 7)
    required_709 envelope_709 pivot_mem_709 child_required_sub_709 child_envelope_sub_709 ?_
  intro b hb
  exact common_sub_709 (mem_commonEnvelope childrenD_709 b hb)
def height_695_i6 : ℕ := 5
def childrenH_695_i6 : Fin 3 → ℕ := ![height_11, height_75, height_103]
theorem height_exact_695_i6 : height_695_i6 = 1 + Finset.univ.sup childrenH_695_i6 := by decide +kernel
theorem required_origin_695_i6 : ∀ x ∈ required_695_i6,
    (∃ j, x ∈ childrenC_695_i6 j) ∨ ∀ j, x ∈ childrenD_695_i6 j := by decide +kernel
theorem required_exact_695_i6 : required_695_i6 =
    ((Finset.univ.biUnion childrenC_695_i6) ∪ commonEnvelope childrenD_695_i6).erase (1, 6) := by
  exact required_eq_combination childrenC_695_i6 childrenD_695_i6 (1, 6) required_695_i6
    (by decide +kernel) child_required_sub_695_i6 common_sub_695_i6 required_origin_695_i6
theorem envelope_origin_695_i6 : ∀ x ∈ envelope_695_i6,
    x = (1, 6) ∨ ∃ j, x ∈ childrenD_695_i6 j := by decide +kernel
theorem envelope_exact_695_i6 : envelope_695_i6 =
    insert (1, 6) (Finset.univ.biUnion childrenD_695_i6) := by
  exact envelope_eq_combination childrenD_695_i6 (1, 6) envelope_695_i6
    pivot_mem_695_i6 child_envelope_sub_695_i6 envelope_origin_695_i6
def checked_695_i6 : CheckedCard where
  required := required_695_i6
  envelope := envelope_695_i6
  height := height_695_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_695_i6
def height_695_i7 : ℕ := 5
def childrenH_695_i7 : Fin 3 → ℕ := ![height_11, height_17, height_90]
theorem height_exact_695_i7 : height_695_i7 = 1 + Finset.univ.sup childrenH_695_i7 := by decide +kernel
theorem required_origin_695_i7 : ∀ x ∈ required_695_i7,
    (∃ j, x ∈ childrenC_695_i7 j) ∨ ∀ j, x ∈ childrenD_695_i7 j := by decide +kernel
theorem required_exact_695_i7 : required_695_i7 =
    ((Finset.univ.biUnion childrenC_695_i7) ∪ commonEnvelope childrenD_695_i7).erase (1, 6) := by
  exact required_eq_combination childrenC_695_i7 childrenD_695_i7 (1, 6) required_695_i7
    (by decide +kernel) child_required_sub_695_i7 common_sub_695_i7 required_origin_695_i7
theorem envelope_origin_695_i7 : ∀ x ∈ envelope_695_i7,
    x = (1, 6) ∨ ∃ j, x ∈ childrenD_695_i7 j := by decide +kernel
theorem envelope_exact_695_i7 : envelope_695_i7 =
    insert (1, 6) (Finset.univ.biUnion childrenD_695_i7) := by
  exact envelope_eq_combination childrenD_695_i7 (1, 6) envelope_695_i7
    pivot_mem_695_i7 child_envelope_sub_695_i7 envelope_origin_695_i7
def checked_695_i7 : CheckedCard where
  required := required_695_i7
  envelope := envelope_695_i7
  height := height_695_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_695_i7
def height_695_i5 : ℕ := 7
def childrenH_695_i5 : Fin 4 → ℕ := ![height_308, height_348, height_695_i6, height_695_i7]
theorem height_exact_695_i5 : height_695_i5 = 1 + Finset.univ.sup childrenH_695_i5 := by decide +kernel
theorem required_origin_695_i5 : ∀ x ∈ required_695_i5,
    (∃ j, x ∈ childrenC_695_i5 j) ∨ ∀ j, x ∈ childrenD_695_i5 j := by decide +kernel
theorem required_exact_695_i5 : required_695_i5 =
    ((Finset.univ.biUnion childrenC_695_i5) ∪ commonEnvelope childrenD_695_i5).erase (1, 7) := by
  exact required_eq_combination childrenC_695_i5 childrenD_695_i5 (1, 7) required_695_i5
    (by decide +kernel) child_required_sub_695_i5 common_sub_695_i5 required_origin_695_i5
theorem envelope_origin_695_i5 : ∀ x ∈ envelope_695_i5,
    x = (1, 7) ∨ ∃ j, x ∈ childrenD_695_i5 j := by decide +kernel
theorem envelope_exact_695_i5 : envelope_695_i5 =
    insert (1, 7) (Finset.univ.biUnion childrenD_695_i5) := by
  exact envelope_eq_combination childrenD_695_i5 (1, 7) envelope_695_i5
    pivot_mem_695_i5 child_envelope_sub_695_i5 envelope_origin_695_i5
def checked_695_i5 : CheckedCard where
  required := required_695_i5
  envelope := envelope_695_i5
  height := height_695_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_695_i5
def height_695_i4 : ℕ := 8
def childrenH_695_i4 : Fin 2 → ℕ := ![height_5, height_695_i5]
theorem height_exact_695_i4 : height_695_i4 = 1 + Finset.univ.sup childrenH_695_i4 := by decide +kernel
theorem required_origin_695_i4 : ∀ x ∈ required_695_i4,
    (∃ j, x ∈ childrenC_695_i4 j) ∨ ∀ j, x ∈ childrenD_695_i4 j := by decide +kernel
theorem required_exact_695_i4 : required_695_i4 =
    ((Finset.univ.biUnion childrenC_695_i4) ∪ commonEnvelope childrenD_695_i4).erase (1, 4) := by
  exact required_eq_combination childrenC_695_i4 childrenD_695_i4 (1, 4) required_695_i4
    (by decide +kernel) child_required_sub_695_i4 common_sub_695_i4 required_origin_695_i4
theorem envelope_origin_695_i4 : ∀ x ∈ envelope_695_i4,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_695_i4 j := by decide +kernel
theorem envelope_exact_695_i4 : envelope_695_i4 =
    insert (1, 4) (Finset.univ.biUnion childrenD_695_i4) := by
  exact envelope_eq_combination childrenD_695_i4 (1, 4) envelope_695_i4
    pivot_mem_695_i4 child_envelope_sub_695_i4 envelope_origin_695_i4
def checked_695_i4 : CheckedCard where
  required := required_695_i4
  envelope := envelope_695_i4
  height := height_695_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_695_i4
def height_695_i3 : ℕ := 9
def childrenH_695_i3 : Fin 2 → ℕ := ![height_96, height_695_i4]
theorem height_exact_695_i3 : height_695_i3 = 1 + Finset.univ.sup childrenH_695_i3 := by decide +kernel
theorem required_origin_695_i3 : ∀ x ∈ required_695_i3,
    (∃ j, x ∈ childrenC_695_i3 j) ∨ ∀ j, x ∈ childrenD_695_i3 j := by decide +kernel
theorem required_exact_695_i3 : required_695_i3 =
    ((Finset.univ.biUnion childrenC_695_i3) ∪ commonEnvelope childrenD_695_i3).erase (3, 8) := by
  exact required_eq_combination childrenC_695_i3 childrenD_695_i3 (3, 8) required_695_i3
    (by decide +kernel) child_required_sub_695_i3 common_sub_695_i3 required_origin_695_i3
theorem envelope_origin_695_i3 : ∀ x ∈ envelope_695_i3,
    x = (3, 8) ∨ ∃ j, x ∈ childrenD_695_i3 j := by decide +kernel
theorem envelope_exact_695_i3 : envelope_695_i3 =
    insert (3, 8) (Finset.univ.biUnion childrenD_695_i3) := by
  exact envelope_eq_combination childrenD_695_i3 (3, 8) envelope_695_i3
    pivot_mem_695_i3 child_envelope_sub_695_i3 envelope_origin_695_i3
def checked_695_i3 : CheckedCard where
  required := required_695_i3
  envelope := envelope_695_i3
  height := height_695_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_695_i3
def height_695_i2 : ℕ := 10
def childrenH_695_i2 : Fin 2 → ℕ := ![height_5, height_695_i3]
theorem height_exact_695_i2 : height_695_i2 = 1 + Finset.univ.sup childrenH_695_i2 := by decide +kernel
theorem required_origin_695_i2 : ∀ x ∈ required_695_i2,
    (∃ j, x ∈ childrenC_695_i2 j) ∨ ∀ j, x ∈ childrenD_695_i2 j := by decide +kernel
theorem required_exact_695_i2 : required_695_i2 =
    ((Finset.univ.biUnion childrenC_695_i2) ∪ commonEnvelope childrenD_695_i2).erase (1, 5) := by
  exact required_eq_combination childrenC_695_i2 childrenD_695_i2 (1, 5) required_695_i2
    (by decide +kernel) child_required_sub_695_i2 common_sub_695_i2 required_origin_695_i2
theorem envelope_origin_695_i2 : ∀ x ∈ envelope_695_i2,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_695_i2 j := by decide +kernel
theorem envelope_exact_695_i2 : envelope_695_i2 =
    insert (1, 5) (Finset.univ.biUnion childrenD_695_i2) := by
  exact envelope_eq_combination childrenD_695_i2 (1, 5) envelope_695_i2
    pivot_mem_695_i2 child_envelope_sub_695_i2 envelope_origin_695_i2
def checked_695_i2 : CheckedCard where
  required := required_695_i2
  envelope := envelope_695_i2
  height := height_695_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_695_i2
def height_695_i1 : ℕ := 11
def childrenH_695_i1 : Fin 6 → ℕ := ![height_67, height_175, height_228, height_435, height_688, height_695_i2]
theorem height_exact_695_i1 : height_695_i1 = 1 + Finset.univ.sup childrenH_695_i1 := by decide +kernel
theorem required_origin_695_i1 : ∀ x ∈ required_695_i1,
    (∃ j, x ∈ childrenC_695_i1 j) ∨ ∀ j, x ∈ childrenD_695_i1 j := by decide +kernel
theorem required_exact_695_i1 : required_695_i1 =
    ((Finset.univ.biUnion childrenC_695_i1) ∪ commonEnvelope childrenD_695_i1).erase (4, 7) := by
  exact required_eq_combination childrenC_695_i1 childrenD_695_i1 (4, 7) required_695_i1
    (by decide +kernel) child_required_sub_695_i1 common_sub_695_i1 required_origin_695_i1
theorem envelope_origin_695_i1 : ∀ x ∈ envelope_695_i1,
    x = (4, 7) ∨ ∃ j, x ∈ childrenD_695_i1 j := by decide +kernel
theorem envelope_exact_695_i1 : envelope_695_i1 =
    insert (4, 7) (Finset.univ.biUnion childrenD_695_i1) := by
  exact envelope_eq_combination childrenD_695_i1 (4, 7) envelope_695_i1
    pivot_mem_695_i1 child_envelope_sub_695_i1 envelope_origin_695_i1
def checked_695_i1 : CheckedCard where
  required := required_695_i1
  envelope := envelope_695_i1
  height := height_695_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_695_i1
def height_695_i0 : ℕ := 12
def childrenH_695_i0 : Fin 4 → ℕ := ![height_44, height_324, height_686, height_695_i1]
theorem height_exact_695_i0 : height_695_i0 = 1 + Finset.univ.sup childrenH_695_i0 := by decide +kernel
theorem required_origin_695_i0 : ∀ x ∈ required_695_i0,
    (∃ j, x ∈ childrenC_695_i0 j) ∨ ∀ j, x ∈ childrenD_695_i0 j := by decide +kernel
theorem required_exact_695_i0 : required_695_i0 =
    ((Finset.univ.biUnion childrenC_695_i0) ∪ commonEnvelope childrenD_695_i0).erase (4, 6) := by
  exact required_eq_combination childrenC_695_i0 childrenD_695_i0 (4, 6) required_695_i0
    (by decide +kernel) child_required_sub_695_i0 common_sub_695_i0 required_origin_695_i0
theorem envelope_origin_695_i0 : ∀ x ∈ envelope_695_i0,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_695_i0 j := by decide +kernel
theorem envelope_exact_695_i0 : envelope_695_i0 =
    insert (4, 6) (Finset.univ.biUnion childrenD_695_i0) := by
  exact envelope_eq_combination childrenD_695_i0 (4, 6) envelope_695_i0
    pivot_mem_695_i0 child_envelope_sub_695_i0 envelope_origin_695_i0
def checked_695_i0 : CheckedCard where
  required := required_695_i0
  envelope := envelope_695_i0
  height := height_695_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_695_i0
def height_695 : ℕ := 13
def childrenH_695 : Fin 5 → ℕ := ![height_12, height_118, height_135, height_182, height_695_i0]
theorem height_exact_695 : height_695 = 1 + Finset.univ.sup childrenH_695 := by decide +kernel
theorem required_origin_695 : ∀ x ∈ required_695,
    (∃ j, x ∈ childrenC_695 j) ∨ ∀ j, x ∈ childrenD_695 j := by decide +kernel
theorem required_exact_695 : required_695 =
    ((Finset.univ.biUnion childrenC_695) ∪ commonEnvelope childrenD_695).erase (4, 5) := by
  exact required_eq_combination childrenC_695 childrenD_695 (4, 5) required_695
    (by decide +kernel) child_required_sub_695 common_sub_695 required_origin_695
theorem envelope_origin_695 : ∀ x ∈ envelope_695,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_695 j := by decide +kernel
theorem envelope_exact_695 : envelope_695 =
    insert (4, 5) (Finset.univ.biUnion childrenD_695) := by
  exact envelope_eq_combination childrenD_695 (4, 5) envelope_695
    pivot_mem_695 child_envelope_sub_695 envelope_origin_695
def checked_695 : CheckedCard where
  required := required_695
  envelope := envelope_695
  height := height_695
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_695
def height_696_i1 : ℕ := 6
def childrenH_696_i1 : Fin 2 → ℕ := ![height_5, height_197]
theorem height_exact_696_i1 : height_696_i1 = 1 + Finset.univ.sup childrenH_696_i1 := by decide +kernel
theorem required_origin_696_i1 : ∀ x ∈ required_696_i1,
    (∃ j, x ∈ childrenC_696_i1 j) ∨ ∀ j, x ∈ childrenD_696_i1 j := by decide +kernel
theorem required_exact_696_i1 : required_696_i1 =
    ((Finset.univ.biUnion childrenC_696_i1) ∪ commonEnvelope childrenD_696_i1).erase (5, 7) := by
  exact required_eq_combination childrenC_696_i1 childrenD_696_i1 (5, 7) required_696_i1
    (by decide +kernel) child_required_sub_696_i1 common_sub_696_i1 required_origin_696_i1
theorem envelope_origin_696_i1 : ∀ x ∈ envelope_696_i1,
    x = (5, 7) ∨ ∃ j, x ∈ childrenD_696_i1 j := by decide +kernel
theorem envelope_exact_696_i1 : envelope_696_i1 =
    insert (5, 7) (Finset.univ.biUnion childrenD_696_i1) := by
  exact envelope_eq_combination childrenD_696_i1 (5, 7) envelope_696_i1
    pivot_mem_696_i1 child_envelope_sub_696_i1 envelope_origin_696_i1
def checked_696_i1 : CheckedCard where
  required := required_696_i1
  envelope := envelope_696_i1
  height := height_696_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_696_i1
def height_696_i0 : ℕ := 12
def childrenH_696_i0 : Fin 4 → ℕ := ![height_317, height_696_i1, height_436, height_685]
theorem height_exact_696_i0 : height_696_i0 = 1 + Finset.univ.sup childrenH_696_i0 := by decide +kernel
theorem required_origin_696_i0 : ∀ x ∈ required_696_i0,
    (∃ j, x ∈ childrenC_696_i0 j) ∨ ∀ j, x ∈ childrenD_696_i0 j := by decide +kernel
theorem required_exact_696_i0 : required_696_i0 =
    ((Finset.univ.biUnion childrenC_696_i0) ∪ commonEnvelope childrenD_696_i0).erase (4, 4) := by
  exact required_eq_combination childrenC_696_i0 childrenD_696_i0 (4, 4) required_696_i0
    (by decide +kernel) child_required_sub_696_i0 common_sub_696_i0 required_origin_696_i0
theorem envelope_origin_696_i0 : ∀ x ∈ envelope_696_i0,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_696_i0 j := by decide +kernel
theorem envelope_exact_696_i0 : envelope_696_i0 =
    insert (4, 4) (Finset.univ.biUnion childrenD_696_i0) := by
  exact envelope_eq_combination childrenD_696_i0 (4, 4) envelope_696_i0
    pivot_mem_696_i0 child_envelope_sub_696_i0 envelope_origin_696_i0
def checked_696_i0 : CheckedCard where
  required := required_696_i0
  envelope := envelope_696_i0
  height := height_696_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_696_i0
def height_696 : ℕ := 13
def childrenH_696 : Fin 6 → ℕ := ![height_12, height_322, height_369, height_435, height_622, height_696_i0]
theorem height_exact_696 : height_696 = 1 + Finset.univ.sup childrenH_696 := by decide +kernel
theorem required_origin_696 : ∀ x ∈ required_696,
    (∃ j, x ∈ childrenC_696 j) ∨ ∀ j, x ∈ childrenD_696 j := by decide +kernel
theorem required_exact_696 : required_696 =
    ((Finset.univ.biUnion childrenC_696) ∪ commonEnvelope childrenD_696).erase (5, 4) := by
  exact required_eq_combination childrenC_696 childrenD_696 (5, 4) required_696
    (by decide +kernel) child_required_sub_696 common_sub_696 required_origin_696
theorem envelope_origin_696 : ∀ x ∈ envelope_696,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_696 j := by decide +kernel
theorem envelope_exact_696 : envelope_696 =
    insert (5, 4) (Finset.univ.biUnion childrenD_696) := by
  exact envelope_eq_combination childrenD_696 (5, 4) envelope_696
    pivot_mem_696 child_envelope_sub_696 envelope_origin_696
def checked_696 : CheckedCard where
  required := required_696
  envelope := envelope_696
  height := height_696
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_696
def height_709_i2 : ℕ := 7
def childrenH_709_i2 : Fin 3 → ℕ := ![height_53, height_56, height_392]
theorem height_exact_709_i2 : height_709_i2 = 1 + Finset.univ.sup childrenH_709_i2 := by decide +kernel
theorem required_origin_709_i2 : ∀ x ∈ required_709_i2,
    (∃ j, x ∈ childrenC_709_i2 j) ∨ ∀ j, x ∈ childrenD_709_i2 j := by decide +kernel
theorem required_exact_709_i2 : required_709_i2 =
    ((Finset.univ.biUnion childrenC_709_i2) ∪ commonEnvelope childrenD_709_i2).erase (4, 5) := by
  exact required_eq_combination childrenC_709_i2 childrenD_709_i2 (4, 5) required_709_i2
    (by decide +kernel) child_required_sub_709_i2 common_sub_709_i2 required_origin_709_i2
theorem envelope_origin_709_i2 : ∀ x ∈ envelope_709_i2,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_709_i2 j := by decide +kernel
theorem envelope_exact_709_i2 : envelope_709_i2 =
    insert (4, 5) (Finset.univ.biUnion childrenD_709_i2) := by
  exact envelope_eq_combination childrenD_709_i2 (4, 5) envelope_709_i2
    pivot_mem_709_i2 child_envelope_sub_709_i2 envelope_origin_709_i2
def checked_709_i2 : CheckedCard where
  required := required_709_i2
  envelope := envelope_709_i2
  height := height_709_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_709_i2
def height_709_i1 : ℕ := 8
def childrenH_709_i1 : Fin 3 → ℕ := ![height_11, height_253, height_709_i2]
theorem height_exact_709_i1 : height_709_i1 = 1 + Finset.univ.sup childrenH_709_i1 := by decide +kernel
theorem required_origin_709_i1 : ∀ x ∈ required_709_i1,
    (∃ j, x ∈ childrenC_709_i1 j) ∨ ∀ j, x ∈ childrenD_709_i1 j := by decide +kernel
theorem required_exact_709_i1 : required_709_i1 =
    ((Finset.univ.biUnion childrenC_709_i1) ∪ commonEnvelope childrenD_709_i1).erase (5, 4) := by
  exact required_eq_combination childrenC_709_i1 childrenD_709_i1 (5, 4) required_709_i1
    (by decide +kernel) child_required_sub_709_i1 common_sub_709_i1 required_origin_709_i1
theorem envelope_origin_709_i1 : ∀ x ∈ envelope_709_i1,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_709_i1 j := by decide +kernel
theorem envelope_exact_709_i1 : envelope_709_i1 =
    insert (5, 4) (Finset.univ.biUnion childrenD_709_i1) := by
  exact envelope_eq_combination childrenD_709_i1 (5, 4) envelope_709_i1
    pivot_mem_709_i1 child_envelope_sub_709_i1 envelope_origin_709_i1
def checked_709_i1 : CheckedCard where
  required := required_709_i1
  envelope := envelope_709_i1
  height := height_709_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_709_i1
def height_709_i4 : ℕ := 5
def childrenH_709_i4 : Fin 2 → ℕ := ![height_6, height_89]
theorem height_exact_709_i4 : height_709_i4 = 1 + Finset.univ.sup childrenH_709_i4 := by decide +kernel
theorem required_origin_709_i4 : ∀ x ∈ required_709_i4,
    (∃ j, x ∈ childrenC_709_i4 j) ∨ ∀ j, x ∈ childrenD_709_i4 j := by decide +kernel
theorem required_exact_709_i4 : required_709_i4 =
    ((Finset.univ.biUnion childrenC_709_i4) ∪ commonEnvelope childrenD_709_i4).erase (5, 3) := by
  exact required_eq_combination childrenC_709_i4 childrenD_709_i4 (5, 3) required_709_i4
    (by decide +kernel) child_required_sub_709_i4 common_sub_709_i4 required_origin_709_i4
theorem envelope_origin_709_i4 : ∀ x ∈ envelope_709_i4,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_709_i4 j := by decide +kernel
theorem envelope_exact_709_i4 : envelope_709_i4 =
    insert (5, 3) (Finset.univ.biUnion childrenD_709_i4) := by
  exact envelope_eq_combination childrenD_709_i4 (5, 3) envelope_709_i4
    pivot_mem_709_i4 child_envelope_sub_709_i4 envelope_origin_709_i4
def checked_709_i4 : CheckedCard where
  required := required_709_i4
  envelope := envelope_709_i4
  height := height_709_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_709_i4
def height_709_i3 : ℕ := 7
def childrenH_709_i3 : Fin 3 → ℕ := ![height_11, height_521, height_709_i4]
theorem height_exact_709_i3 : height_709_i3 = 1 + Finset.univ.sup childrenH_709_i3 := by decide +kernel
theorem required_origin_709_i3 : ∀ x ∈ required_709_i3,
    (∃ j, x ∈ childrenC_709_i3 j) ∨ ∀ j, x ∈ childrenD_709_i3 j := by decide +kernel
theorem required_exact_709_i3 : required_709_i3 =
    ((Finset.univ.biUnion childrenC_709_i3) ∪ commonEnvelope childrenD_709_i3).erase (5, 4) := by
  exact required_eq_combination childrenC_709_i3 childrenD_709_i3 (5, 4) required_709_i3
    (by decide +kernel) child_required_sub_709_i3 common_sub_709_i3 required_origin_709_i3
theorem envelope_origin_709_i3 : ∀ x ∈ envelope_709_i3,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_709_i3 j := by decide +kernel
theorem envelope_exact_709_i3 : envelope_709_i3 =
    insert (5, 4) (Finset.univ.biUnion childrenD_709_i3) := by
  exact envelope_eq_combination childrenD_709_i3 (5, 4) envelope_709_i3
    pivot_mem_709_i3 child_envelope_sub_709_i3 envelope_origin_709_i3
def checked_709_i3 : CheckedCard where
  required := required_709_i3
  envelope := envelope_709_i3
  height := height_709_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_709_i3
def height_709_i0 : ℕ := 12
def childrenH_709_i0 : Fin 7 → ℕ := ![height_524, height_536, height_545, height_655, height_664, height_709_i1, height_709_i3]
theorem height_exact_709_i0 : height_709_i0 = 1 + Finset.univ.sup childrenH_709_i0 := by decide +kernel
theorem required_origin_709_i0 : ∀ x ∈ required_709_i0,
    (∃ j, x ∈ childrenC_709_i0 j) ∨ ∀ j, x ∈ childrenD_709_i0 j := by decide +kernel
theorem required_exact_709_i0 : required_709_i0 =
    ((Finset.univ.biUnion childrenC_709_i0) ∪ commonEnvelope childrenD_709_i0).erase (6, 6) := by
  exact required_eq_combination childrenC_709_i0 childrenD_709_i0 (6, 6) required_709_i0
    (by decide +kernel) child_required_sub_709_i0 common_sub_709_i0 required_origin_709_i0
theorem envelope_origin_709_i0 : ∀ x ∈ envelope_709_i0,
    x = (6, 6) ∨ ∃ j, x ∈ childrenD_709_i0 j := by decide +kernel
theorem envelope_exact_709_i0 : envelope_709_i0 =
    insert (6, 6) (Finset.univ.biUnion childrenD_709_i0) := by
  exact envelope_eq_combination childrenD_709_i0 (6, 6) envelope_709_i0
    pivot_mem_709_i0 child_envelope_sub_709_i0 envelope_origin_709_i0
def checked_709_i0 : CheckedCard where
  required := required_709_i0
  envelope := envelope_709_i0
  height := height_709_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_709_i0
def height_709 : ℕ := 13
def childrenH_709 : Fin 4 → ℕ := ![height_14, height_116, height_181, height_709_i0]
theorem height_exact_709 : height_709 = 1 + Finset.univ.sup childrenH_709 := by decide +kernel
theorem required_origin_709 : ∀ x ∈ required_709,
    (∃ j, x ∈ childrenC_709 j) ∨ ∀ j, x ∈ childrenD_709 j := by decide +kernel
theorem required_exact_709 : required_709 =
    ((Finset.univ.biUnion childrenC_709) ∪ commonEnvelope childrenD_709).erase (5, 7) := by
  exact required_eq_combination childrenC_709 childrenD_709 (5, 7) required_709
    (by decide +kernel) child_required_sub_709 common_sub_709 required_origin_709
theorem envelope_origin_709 : ∀ x ∈ envelope_709,
    x = (5, 7) ∨ ∃ j, x ∈ childrenD_709 j := by decide +kernel
theorem envelope_exact_709 : envelope_709 =
    insert (5, 7) (Finset.univ.biUnion childrenD_709) := by
  exact envelope_eq_combination childrenD_709 (5, 7) envelope_709
    pivot_mem_709 child_envelope_sub_709 envelope_origin_709
def checked_709 : CheckedCard where
  required := required_709
  envelope := envelope_709
  height := height_709
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_709
end SnakyPrototype.Certificate21

end OAI
