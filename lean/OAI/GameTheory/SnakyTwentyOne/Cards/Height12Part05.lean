import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part07
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part07
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part06
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_715_i1 : Finset Cell := ⟨(([(3, 5), (4, 5), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_715_i1 : Finset Cell := ⟨(([(2, 6), (2, 7), (3, 5), (3, 6), (3, 7), (3, 8), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 5), (6, 6), (7, 4), (7, 5), (7, 6), (8, 4), (8, 5), (8, 6), (9, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_715_i1 : Fin 4 → Finset Cell := ![(placed21 6 (5, 8) required_53), (placed21 0 (4, 2) required_53), (placed21 0 (2, 2) required_111), (placed21 1 (2, 4) required_394)]
def childrenD_715_i1 : Fin 4 → Finset Cell := ![(placed21 6 (5, 8) envelope_53), (placed21 0 (4, 2) envelope_53), (placed21 0 (2, 2) envelope_111), (placed21 1 (2, 4) envelope_394)]
theorem common_sub_715_i1 : commonEnvelope childrenD_715_i1 ⊆ insert (4, 4) required_715_i1 := by decide +kernel
theorem child_required_sub_715_i1 : ∀ j, childrenC_715_i1 j ⊆ insert (4, 4) required_715_i1 := by decide +kernel
theorem child_envelope_sub_715_i1 : ∀ j, childrenD_715_i1 j ⊆ envelope_715_i1 := by decide +kernel
theorem pivot_mem_715_i1 : (4, 4) ∈ envelope_715_i1 := by decide +kernel
theorem children_work_715_i1 : ∀ j, Template HasSnaky 7 (childrenC_715_i1 j) (childrenD_715_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_53 6 (5, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_53 0 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_111 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_394 1 (2, 4)).mono (by decide +kernel)
theorem row_works_715_i1 : Template HasSnaky 8 required_715_i1 envelope_715_i1 := by
  refine compose HasSnaky 7 childrenC_715_i1 childrenD_715_i1 children_work_715_i1 (4, 4)
    required_715_i1 envelope_715_i1 pivot_mem_715_i1 child_required_sub_715_i1 child_envelope_sub_715_i1 ?_
  intro b hb
  exact common_sub_715_i1 (mem_commonEnvelope childrenD_715_i1 b hb)
def required_715_i0 : Finset Cell := ⟨(([(4, 5), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_715_i0 : Finset Cell := ⟨(([(0, 4), (0, 6), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 5), (3, 6), (3, 7), (3, 8), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 5), (6, 6), (7, 4), (7, 5), (7, 6), (8, 4), (8, 5), (8, 6), (9, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_715_i0 : Fin 4 → Finset Cell := ![(placed21 1 (2, 5) required_44), (placed21 1 (2, 5) required_52), (placed21 2 (6, 3) required_134), required_715_i1]
def childrenD_715_i0 : Fin 4 → Finset Cell := ![(placed21 1 (2, 5) envelope_44), (placed21 1 (2, 5) envelope_52), (placed21 2 (6, 3) envelope_134), envelope_715_i1]
theorem common_sub_715_i0 : commonEnvelope childrenD_715_i0 ⊆ insert (3, 5) required_715_i0 := by decide +kernel
theorem child_required_sub_715_i0 : ∀ j, childrenC_715_i0 j ⊆ insert (3, 5) required_715_i0 := by decide +kernel
theorem child_envelope_sub_715_i0 : ∀ j, childrenD_715_i0 j ⊆ envelope_715_i0 := by decide +kernel
theorem pivot_mem_715_i0 : (3, 5) ∈ envelope_715_i0 := by decide +kernel
theorem children_work_715_i0 : ∀ j, Template HasSnaky 8 (childrenC_715_i0 j) (childrenD_715_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 1 (2, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 1 (2, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_134 2 (6, 3)).mono (by decide +kernel)
  · exact row_works_715_i1.mono (by decide +kernel)
theorem row_works_715_i0 : Template HasSnaky 9 required_715_i0 envelope_715_i0 := by
  refine compose HasSnaky 8 childrenC_715_i0 childrenD_715_i0 children_work_715_i0 (3, 5)
    required_715_i0 envelope_715_i0 pivot_mem_715_i0 child_required_sub_715_i0 child_envelope_sub_715_i0 ?_
  intro b hb
  exact common_sub_715_i0 (mem_commonEnvelope childrenD_715_i0 b hb)
def required_715_i4 : Finset Cell := ⟨(([(4, 5), (4, 6), (5, 5), (5, 6), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_715_i4 : Finset Cell := ⟨(([(3, 6), (4, 3), (4, 4), (4, 5), (4, 6), (5, 5), (5, 6), (5, 7), (5, 8), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_715_i4 : Fin 4 → Finset Cell := ![(placed21 3 (4, 6) required_30), (placed21 0 (4, 3) required_110), (placed21 1 (3, 4) required_296), (placed21 0 (4, 3) required_511)]
def childrenD_715_i4 : Fin 4 → Finset Cell := ![(placed21 3 (4, 6) envelope_30), (placed21 0 (4, 3) envelope_110), (placed21 1 (3, 4) envelope_296), (placed21 0 (4, 3) envelope_511)]
theorem common_sub_715_i4 : commonEnvelope childrenD_715_i4 ⊆ insert (7, 6) required_715_i4 := by decide +kernel
theorem child_required_sub_715_i4 : ∀ j, childrenC_715_i4 j ⊆ insert (7, 6) required_715_i4 := by decide +kernel
theorem child_envelope_sub_715_i4 : ∀ j, childrenD_715_i4 j ⊆ envelope_715_i4 := by decide +kernel
theorem pivot_mem_715_i4 : (7, 6) ∈ envelope_715_i4 := by decide +kernel
theorem children_work_715_i4 : ∀ j, Template HasSnaky 7 (childrenC_715_i4 j) (childrenD_715_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_30 3 (4, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_110 0 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_296 1 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_511 0 (4, 3)).mono (by decide +kernel)
theorem row_works_715_i4 : Template HasSnaky 8 required_715_i4 envelope_715_i4 := by
  refine compose HasSnaky 7 childrenC_715_i4 childrenD_715_i4 children_work_715_i4 (7, 6)
    required_715_i4 envelope_715_i4 pivot_mem_715_i4 child_required_sub_715_i4 child_envelope_sub_715_i4 ?_
  intro b hb
  exact common_sub_715_i4 (mem_commonEnvelope childrenD_715_i4 b hb)
def required_715_i3 : Finset Cell := ⟨(([(4, 5), (4, 6), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_715_i3 : Finset Cell := ⟨(([(3, 6), (4, 3), (4, 4), (4, 5), (4, 6), (5, 5), (5, 6), (5, 7), (5, 8), (6, 1), (6, 2), (6, 3), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_715_i3 : Fin 4 → Finset Cell := ![(placed21 1 (3, 5) required_22), (placed21 1 (4, 5) required_74), (placed21 0 (3, 1) required_325), required_715_i4]
def childrenD_715_i3 : Fin 4 → Finset Cell := ![(placed21 1 (3, 5) envelope_22), (placed21 1 (4, 5) envelope_74), (placed21 0 (3, 1) envelope_325), envelope_715_i4]
theorem common_sub_715_i3 : commonEnvelope childrenD_715_i3 ⊆ insert (7, 5) required_715_i3 := by decide +kernel
theorem child_required_sub_715_i3 : ∀ j, childrenC_715_i3 j ⊆ insert (7, 5) required_715_i3 := by decide +kernel
theorem child_envelope_sub_715_i3 : ∀ j, childrenD_715_i3 j ⊆ envelope_715_i3 := by decide +kernel
theorem pivot_mem_715_i3 : (7, 5) ∈ envelope_715_i3 := by decide +kernel
theorem children_work_715_i3 : ∀ j, Template HasSnaky 9 (childrenC_715_i3 j) (childrenD_715_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_22 1 (3, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_74 1 (4, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_325 0 (3, 1)).mono (by decide +kernel)
  · exact row_works_715_i4.mono (by decide +kernel)
theorem row_works_715_i3 : Template HasSnaky 10 required_715_i3 envelope_715_i3 := by
  refine compose HasSnaky 9 childrenC_715_i3 childrenD_715_i3 children_work_715_i3 (7, 5)
    required_715_i3 envelope_715_i3 pivot_mem_715_i3 child_required_sub_715_i3 child_envelope_sub_715_i3 ?_
  intro b hb
  exact common_sub_715_i3 (mem_commonEnvelope childrenD_715_i3 b hb)
def required_715_i2 : Finset Cell := ⟨(([(4, 5), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_715_i2 : Finset Cell := ⟨(([(0, 7), (1, 6), (1, 7), (2, 6), (2, 7), (2, 8), (3, 6), (3, 7), (3, 8), (3, 9), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 7), (9, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_715_i2 : Fin 5 → Finset Cell := ![(placed21 2 (7, 3) required_361), (placed21 5 (8, 5) required_408), (placed21 7 (8, 9) required_621), (placed21 1 (0, 3) required_714), required_715_i3]
def childrenD_715_i2 : Fin 5 → Finset Cell := ![(placed21 2 (7, 3) envelope_361), (placed21 5 (8, 5) envelope_408), (placed21 7 (8, 9) envelope_621), (placed21 1 (0, 3) envelope_714), envelope_715_i3]
theorem common_sub_715_i2 : commonEnvelope childrenD_715_i2 ⊆ insert (4, 6) required_715_i2 := by decide +kernel
theorem child_required_sub_715_i2 : ∀ j, childrenC_715_i2 j ⊆ insert (4, 6) required_715_i2 := by decide +kernel
theorem child_envelope_sub_715_i2 : ∀ j, childrenD_715_i2 j ⊆ envelope_715_i2 := by decide +kernel
theorem pivot_mem_715_i2 : (4, 6) ∈ envelope_715_i2 := by decide +kernel
theorem children_work_715_i2 : ∀ j, Template HasSnaky 10 (childrenC_715_i2 j) (childrenD_715_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_361 2 (7, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_408 5 (8, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_621 7 (8, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_714 1 (0, 3)).mono (by decide +kernel)
  · exact row_works_715_i3.mono (by decide +kernel)
theorem row_works_715_i2 : Template HasSnaky 11 required_715_i2 envelope_715_i2 := by
  refine compose HasSnaky 10 childrenC_715_i2 childrenD_715_i2 children_work_715_i2 (4, 6)
    required_715_i2 envelope_715_i2 pivot_mem_715_i2 child_required_sub_715_i2 child_envelope_sub_715_i2 ?_
  intro b hb
  exact common_sub_715_i2 (mem_commonEnvelope childrenD_715_i2 b hb)
def required_715 : Finset Cell := ⟨(([(4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_715 : Finset Cell := ⟨(([(0, 4), (0, 6), (0, 7), (0, 8), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 1), (6, 2), (6, 3), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (10, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_715 : Fin 8 → Finset Cell := ![(placed21 4 (2, 9) required_523), (placed21 1 (0, 3) required_532), (placed21 6 (8, 9) required_536), (placed21 6 (6, 10) required_545), (placed21 4 (2, 10) required_655), (placed21 1 (0, 1) required_664), required_715_i0, required_715_i2]
def childrenD_715 : Fin 8 → Finset Cell := ![(placed21 4 (2, 9) envelope_523), (placed21 1 (0, 3) envelope_532), (placed21 6 (8, 9) envelope_536), (placed21 6 (6, 10) envelope_545), (placed21 4 (2, 10) envelope_655), (placed21 1 (0, 1) envelope_664), envelope_715_i0, envelope_715_i2]
theorem common_sub_715 : commonEnvelope childrenD_715 ⊆ insert (5, 6) required_715 := by decide +kernel
theorem child_required_sub_715 : ∀ j, childrenC_715 j ⊆ insert (5, 6) required_715 := by decide +kernel
theorem child_envelope_sub_715 : ∀ j, childrenD_715 j ⊆ envelope_715 := by decide +kernel
theorem pivot_mem_715 : (5, 6) ∈ envelope_715 := by decide +kernel
theorem children_work_715 : ∀ j, Template HasSnaky 11 (childrenC_715 j) (childrenD_715 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_523 4 (2, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_532 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_536 6 (8, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_545 6 (6, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_655 4 (2, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_664 1 (0, 1)).mono (by decide +kernel)
  · exact row_works_715_i0.mono (by decide +kernel)
  · exact row_works_715_i2.mono (by decide +kernel)
theorem row_works_715 : Template HasSnaky 12 required_715 envelope_715 := by
  refine compose HasSnaky 11 childrenC_715 childrenD_715 children_work_715 (5, 6)
    required_715 envelope_715 pivot_mem_715 child_required_sub_715 child_envelope_sub_715 ?_
  intro b hb
  exact common_sub_715 (mem_commonEnvelope childrenD_715 b hb)
def required_717 : Finset Cell := ⟨(([(4, 6), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_717 : Finset Cell := ⟨(([(0, 3), (0, 5), (0, 7), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 9), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 8), (3, 9), (3, 10), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 2), (7, 3), (7, 4), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 3), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (10, 5), (10, 7), (10, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_717 : Fin 10 → Finset Cell := ![(placed21 1 (2, 5) required_192), (placed21 7 (8, 7) required_192), (placed21 2 (10, 1) required_550), (placed21 4 (0, 11) required_550), (placed21 0 (3, 3) required_578), (placed21 6 (7, 9) required_578), (placed21 1 (1, 3) required_622), (placed21 7 (9, 9) required_622), (placed21 0 (0, 1) required_716), (placed21 6 (10, 11) required_716)]
def childrenD_717 : Fin 10 → Finset Cell := ![(placed21 1 (2, 5) envelope_192), (placed21 7 (8, 7) envelope_192), (placed21 2 (10, 1) envelope_550), (placed21 4 (0, 11) envelope_550), (placed21 0 (3, 3) envelope_578), (placed21 6 (7, 9) envelope_578), (placed21 1 (1, 3) envelope_622), (placed21 7 (9, 9) envelope_622), (placed21 0 (0, 1) envelope_716), (placed21 6 (10, 11) envelope_716)]
theorem common_sub_717 : commonEnvelope childrenD_717 ⊆ insert (6, 6) required_717 := by decide +kernel
theorem child_required_sub_717 : ∀ j, childrenC_717 j ⊆ insert (6, 6) required_717 := by decide +kernel
theorem child_envelope_sub_717 : ∀ j, childrenD_717 j ⊆ envelope_717 := by decide +kernel
theorem pivot_mem_717 : (6, 6) ∈ envelope_717 := by decide +kernel
theorem children_work_717 : ∀ j, Template HasSnaky 11 (childrenC_717 j) (childrenD_717 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_192 1 (2, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_192 7 (8, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_550 2 (10, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_550 4 (0, 11)).mono (by decide +kernel)
  · exact (placed21_template row_works_578 0 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_578 6 (7, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_622 1 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_622 7 (9, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_716 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_716 6 (10, 11)).mono (by decide +kernel)
theorem row_works_717 : Template HasSnaky 12 required_717 envelope_717 := by
  refine compose HasSnaky 11 childrenC_717 childrenD_717 children_work_717 (6, 6)
    required_717 envelope_717 pivot_mem_717 child_required_sub_717 child_envelope_sub_717 ?_
  intro b hb
  exact common_sub_717 (mem_commonEnvelope childrenD_717 b hb)
def required_723_i0 : Finset Cell := ⟨(([(2, 5), (3, 5), (3, 6), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_723_i0 : Finset Cell := ⟨(([(1, 4), (1, 6), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 4), (6, 6), (6, 7), (6, 8), (6, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_723_i0 : Fin 2 → Finset Cell := ![(placed21 6 (5, 7) required_46), (placed21 0 (2, 1) required_321)]
def childrenD_723_i0 : Fin 2 → Finset Cell := ![(placed21 6 (5, 7) envelope_46), (placed21 0 (2, 1) envelope_321)]
theorem common_sub_723_i0 : commonEnvelope childrenD_723_i0 ⊆ insert (4, 5) required_723_i0 := by decide +kernel
theorem child_required_sub_723_i0 : ∀ j, childrenC_723_i0 j ⊆ insert (4, 5) required_723_i0 := by decide +kernel
theorem child_envelope_sub_723_i0 : ∀ j, childrenD_723_i0 j ⊆ envelope_723_i0 := by decide +kernel
theorem pivot_mem_723_i0 : (4, 5) ∈ envelope_723_i0 := by decide +kernel
theorem children_work_723_i0 : ∀ j, Template HasSnaky 8 (childrenC_723_i0 j) (childrenD_723_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_46 6 (5, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_321 0 (2, 1)).mono (by decide +kernel)
theorem row_works_723_i0 : Template HasSnaky 9 required_723_i0 envelope_723_i0 := by
  refine compose HasSnaky 8 childrenC_723_i0 childrenD_723_i0 children_work_723_i0 (4, 5)
    required_723_i0 envelope_723_i0 pivot_mem_723_i0 child_required_sub_723_i0 child_envelope_sub_723_i0 ?_
  intro b hb
  exact common_sub_723_i0 (mem_commonEnvelope childrenD_723_i0 b hb)
def required_723_i1 : Finset Cell := ⟨(([(2, 5), (3, 5), (3, 6), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_723_i1 : Finset Cell := ⟨(([(1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 5), (5, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_723_i1 : Fin 3 → Finset Cell := ![(placed21 6 (3, 8) required_53), (placed21 0 (2, 2) required_53), (placed21 1 (1, 4) required_310)]
def childrenD_723_i1 : Fin 3 → Finset Cell := ![(placed21 6 (3, 8) envelope_53), (placed21 0 (2, 2) envelope_53), (placed21 1 (1, 4) envelope_310)]
theorem common_sub_723_i1 : commonEnvelope childrenD_723_i1 ⊆ insert (2, 4) required_723_i1 := by decide +kernel
theorem child_required_sub_723_i1 : ∀ j, childrenC_723_i1 j ⊆ insert (2, 4) required_723_i1 := by decide +kernel
theorem child_envelope_sub_723_i1 : ∀ j, childrenD_723_i1 j ⊆ envelope_723_i1 := by decide +kernel
theorem pivot_mem_723_i1 : (2, 4) ∈ envelope_723_i1 := by decide +kernel
theorem children_work_723_i1 : ∀ j, Template HasSnaky 3 (childrenC_723_i1 j) (childrenD_723_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_53 6 (3, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_53 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_310 1 (1, 4)).mono (by decide +kernel)
theorem row_works_723_i1 : Template HasSnaky 4 required_723_i1 envelope_723_i1 := by
  refine compose HasSnaky 3 childrenC_723_i1 childrenD_723_i1 children_work_723_i1 (2, 4)
    required_723_i1 envelope_723_i1 pivot_mem_723_i1 child_required_sub_723_i1 child_envelope_sub_723_i1 ?_
  intro b hb
  exact common_sub_723_i1 (mem_commonEnvelope childrenD_723_i1 b hb)
def required_723_i4 : Finset Cell := ⟨(([(2, 5), (3, 5), (3, 6), (3, 7), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_723_i4 : Finset Cell := ⟨(([(0, 6), (1, 6), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 6), (4, 7), (4, 8), (5, 7), (6, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_723_i4 : Fin 3 → Finset Cell := ![(placed21 6 (4, 8) required_9), (placed21 3 (2, 7) required_90), (placed21 5 (6, 4) required_99)]
def childrenD_723_i4 : Fin 3 → Finset Cell := ![(placed21 6 (4, 8) envelope_9), (placed21 3 (2, 7) envelope_90), (placed21 5 (6, 4) envelope_99)]
theorem common_sub_723_i4 : commonEnvelope childrenD_723_i4 ⊆ insert (3, 4) required_723_i4 := by decide +kernel
theorem child_required_sub_723_i4 : ∀ j, childrenC_723_i4 j ⊆ insert (3, 4) required_723_i4 := by decide +kernel
theorem child_envelope_sub_723_i4 : ∀ j, childrenD_723_i4 j ⊆ envelope_723_i4 := by decide +kernel
theorem pivot_mem_723_i4 : (3, 4) ∈ envelope_723_i4 := by decide +kernel
theorem children_work_723_i4 : ∀ j, Template HasSnaky 4 (childrenC_723_i4 j) (childrenD_723_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_9 6 (4, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_90 3 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_99 5 (6, 4)).mono (by decide +kernel)
theorem row_works_723_i4 : Template HasSnaky 5 required_723_i4 envelope_723_i4 := by
  refine compose HasSnaky 4 childrenC_723_i4 childrenD_723_i4 children_work_723_i4 (3, 4)
    required_723_i4 envelope_723_i4 pivot_mem_723_i4 child_required_sub_723_i4 child_envelope_sub_723_i4 ?_
  intro b hb
  exact common_sub_723_i4 (mem_commonEnvelope childrenD_723_i4 b hb)
def required_723_i3 : Finset Cell := ⟨(([(2, 5), (3, 5), (3, 6), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_723_i3 : Finset Cell := ⟨(([(0, 6), (0, 8), (1, 6), (1, 8), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 8), (2, 9), (2, 10), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 7), (6, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_723_i3 : Fin 4 → Finset Cell := ![(placed21 6 (3, 8) required_44), (placed21 6 (3, 8) required_52), (placed21 5 (5, 4) required_180), required_723_i4]
def childrenD_723_i3 : Fin 4 → Finset Cell := ![(placed21 6 (3, 8) envelope_44), (placed21 6 (3, 8) envelope_52), (placed21 5 (5, 4) envelope_180), envelope_723_i4]
theorem common_sub_723_i3 : commonEnvelope childrenD_723_i3 ⊆ insert (3, 7) required_723_i3 := by decide +kernel
theorem child_required_sub_723_i3 : ∀ j, childrenC_723_i3 j ⊆ insert (3, 7) required_723_i3 := by decide +kernel
theorem child_envelope_sub_723_i3 : ∀ j, childrenD_723_i3 j ⊆ envelope_723_i3 := by decide +kernel
theorem pivot_mem_723_i3 : (3, 7) ∈ envelope_723_i3 := by decide +kernel
theorem children_work_723_i3 : ∀ j, Template HasSnaky 6 (childrenC_723_i3 j) (childrenD_723_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 6 (3, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 6 (3, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_180 5 (5, 4)).mono (by decide +kernel)
  · exact row_works_723_i4.mono (by decide +kernel)
theorem row_works_723_i3 : Template HasSnaky 7 required_723_i3 envelope_723_i3 := by
  refine compose HasSnaky 6 childrenC_723_i3 childrenD_723_i3 children_work_723_i3 (3, 7)
    required_723_i3 envelope_723_i3 pivot_mem_723_i3 child_required_sub_723_i3 child_envelope_sub_723_i3 ?_
  intro b hb
  exact common_sub_723_i3 (mem_commonEnvelope childrenD_723_i3 b hb)
def required_723_i5 : Finset Cell := ⟨(([(2, 5), (3, 5), (3, 6), (5, 5), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_723_i5 : Finset Cell := ⟨(([(2, 5), (2, 6), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 7), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_723_i5 : Fin 4 → Finset Cell := ![(placed21 0 (2, 4) required_82), (placed21 4 (2, 8) required_176), (placed21 1 (2, 5) required_218), (placed21 6 (6, 10) required_369)]
def childrenD_723_i5 : Fin 4 → Finset Cell := ![(placed21 0 (2, 4) envelope_82), (placed21 4 (2, 8) envelope_176), (placed21 1 (2, 5) envelope_218), (placed21 6 (6, 10) envelope_369)]
theorem common_sub_723_i5 : commonEnvelope childrenD_723_i5 ⊆ insert (5, 6) required_723_i5 := by decide +kernel
theorem child_required_sub_723_i5 : ∀ j, childrenC_723_i5 j ⊆ insert (5, 6) required_723_i5 := by decide +kernel
theorem child_envelope_sub_723_i5 : ∀ j, childrenD_723_i5 j ⊆ envelope_723_i5 := by decide +kernel
theorem pivot_mem_723_i5 : (5, 6) ∈ envelope_723_i5 := by decide +kernel
theorem children_work_723_i5 : ∀ j, Template HasSnaky 6 (childrenC_723_i5 j) (childrenD_723_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_82 0 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_176 4 (2, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_218 1 (2, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_369 6 (6, 10)).mono (by decide +kernel)
theorem row_works_723_i5 : Template HasSnaky 7 required_723_i5 envelope_723_i5 := by
  refine compose HasSnaky 6 childrenC_723_i5 childrenD_723_i5 children_work_723_i5 (5, 6)
    required_723_i5 envelope_723_i5 pivot_mem_723_i5 child_required_sub_723_i5 child_envelope_sub_723_i5 ?_
  intro b hb
  exact common_sub_723_i5 (mem_commonEnvelope childrenD_723_i5 b hb)
def required_723_i7 : Finset Cell := ⟨(([(2, 5), (3, 5), (3, 6), (3, 7), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_723_i7 : Finset Cell := ⟨(([(2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 7), (4, 8), (5, 7), (6, 6), (6, 7), (6, 8), (7, 6), (7, 7), (7, 8), (8, 6), (8, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_723_i7 : Fin 2 → Finset Cell := ![(placed21 1 (2, 4) required_145), (placed21 3 (2, 7) required_314)]
def childrenD_723_i7 : Fin 2 → Finset Cell := ![(placed21 1 (2, 4) envelope_145), (placed21 3 (2, 7) envelope_314)]
theorem common_sub_723_i7 : commonEnvelope childrenD_723_i7 ⊆ insert (3, 4) required_723_i7 := by decide +kernel
theorem child_required_sub_723_i7 : ∀ j, childrenC_723_i7 j ⊆ insert (3, 4) required_723_i7 := by decide +kernel
theorem child_envelope_sub_723_i7 : ∀ j, childrenD_723_i7 j ⊆ envelope_723_i7 := by decide +kernel
theorem pivot_mem_723_i7 : (3, 4) ∈ envelope_723_i7 := by decide +kernel
theorem children_work_723_i7 : ∀ j, Template HasSnaky 5 (childrenC_723_i7 j) (childrenD_723_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_145 1 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_314 3 (2, 7)).mono (by decide +kernel)
theorem row_works_723_i7 : Template HasSnaky 6 required_723_i7 envelope_723_i7 := by
  refine compose HasSnaky 5 childrenC_723_i7 childrenD_723_i7 children_work_723_i7 (3, 4)
    required_723_i7 envelope_723_i7 pivot_mem_723_i7 child_required_sub_723_i7 child_envelope_sub_723_i7 ?_
  intro b hb
  exact common_sub_723_i7 (mem_commonEnvelope childrenD_723_i7 b hb)
def required_723_i6 : Finset Cell := ⟨(([(2, 5), (3, 5), (3, 6), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_723_i6 : Finset Cell := ⟨(([(0, 8), (1, 8), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 8), (2, 9), (2, 10), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 7), (4, 8), (4, 9), (4, 10), (5, 7), (6, 6), (6, 7), (6, 8), (7, 6), (7, 7), (7, 8), (8, 6), (8, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_723_i6 : Fin 4 → Finset Cell := ![(placed21 6 (3, 8) required_44), (placed21 6 (3, 8) required_52), (placed21 5 (5, 4) required_180), required_723_i7]
def childrenD_723_i6 : Fin 4 → Finset Cell := ![(placed21 6 (3, 8) envelope_44), (placed21 6 (3, 8) envelope_52), (placed21 5 (5, 4) envelope_180), envelope_723_i7]
theorem common_sub_723_i6 : commonEnvelope childrenD_723_i6 ⊆ insert (3, 7) required_723_i6 := by decide +kernel
theorem child_required_sub_723_i6 : ∀ j, childrenC_723_i6 j ⊆ insert (3, 7) required_723_i6 := by decide +kernel
theorem child_envelope_sub_723_i6 : ∀ j, childrenD_723_i6 j ⊆ envelope_723_i6 := by decide +kernel
theorem pivot_mem_723_i6 : (3, 7) ∈ envelope_723_i6 := by decide +kernel
theorem children_work_723_i6 : ∀ j, Template HasSnaky 6 (childrenC_723_i6 j) (childrenD_723_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 6 (3, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 6 (3, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_180 5 (5, 4)).mono (by decide +kernel)
  · exact row_works_723_i7.mono (by decide +kernel)
theorem row_works_723_i6 : Template HasSnaky 7 required_723_i6 envelope_723_i6 := by
  refine compose HasSnaky 6 childrenC_723_i6 childrenD_723_i6 children_work_723_i6 (3, 7)
    required_723_i6 envelope_723_i6 pivot_mem_723_i6 child_required_sub_723_i6 child_envelope_sub_723_i6 ?_
  intro b hb
  exact common_sub_723_i6 (mem_commonEnvelope childrenD_723_i6 b hb)
def required_723_i8 : Finset Cell := ⟨(([(5, 5), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_723_i8 : Finset Cell := ⟨(([(2, 8), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 6), (8, 7), (8, 8), (8, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_723_i8 : Fin 6 → Finset Cell := ![(placed21 2 (6, 3) required_13), (placed21 4 (4, 9) required_192), (placed21 6 (6, 10) required_369), (placed21 1 (2, 4) required_435), (placed21 1 (3, 4) required_474), (placed21 3 (3, 8) required_477)]
def childrenD_723_i8 : Fin 6 → Finset Cell := ![(placed21 2 (6, 3) envelope_13), (placed21 4 (4, 9) envelope_192), (placed21 6 (6, 10) envelope_369), (placed21 1 (2, 4) envelope_435), (placed21 1 (3, 4) envelope_474), (placed21 3 (3, 8) envelope_477)]
theorem common_sub_723_i8 : commonEnvelope childrenD_723_i8 ⊆ insert (5, 6) required_723_i8 := by decide +kernel
theorem child_required_sub_723_i8 : ∀ j, childrenC_723_i8 j ⊆ insert (5, 6) required_723_i8 := by decide +kernel
theorem child_envelope_sub_723_i8 : ∀ j, childrenD_723_i8 j ⊆ envelope_723_i8 := by decide +kernel
theorem pivot_mem_723_i8 : (5, 6) ∈ envelope_723_i8 := by decide +kernel
theorem children_work_723_i8 : ∀ j, Template HasSnaky 9 (childrenC_723_i8 j) (childrenD_723_i8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 2 (6, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_192 4 (4, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_369 6 (6, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 1 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_474 1 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_477 3 (3, 8)).mono (by decide +kernel)
theorem row_works_723_i8 : Template HasSnaky 10 required_723_i8 envelope_723_i8 := by
  refine compose HasSnaky 9 childrenC_723_i8 childrenD_723_i8 children_work_723_i8 (5, 6)
    required_723_i8 envelope_723_i8 pivot_mem_723_i8 child_required_sub_723_i8 child_envelope_sub_723_i8 ?_
  intro b hb
  exact common_sub_723_i8 (mem_commonEnvelope childrenD_723_i8 b hb)
def required_723_i2 : Finset Cell := ⟨(([(2, 5), (3, 5), (3, 6), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_723_i2 : Finset Cell := ⟨(([(0, 6), (0, 7), (0, 8), (0, 9), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 8), (2, 9), (2, 10), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 6), (8, 7), (8, 8), (8, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_723_i2 : Fin 6 → Finset Cell := ![required_723_i3, required_723_i5, required_723_i6, required_723_i8, (placed21 0 (0, 2) required_721), (placed21 0 (1, 2) required_722)]
def childrenD_723_i2 : Fin 6 → Finset Cell := ![envelope_723_i3, envelope_723_i5, envelope_723_i6, envelope_723_i8, (placed21 0 (0, 2) envelope_721), (placed21 0 (1, 2) envelope_722)]
theorem common_sub_723_i2 : commonEnvelope childrenD_723_i2 ⊆ insert (5, 7) required_723_i2 := by decide +kernel
theorem child_required_sub_723_i2 : ∀ j, childrenC_723_i2 j ⊆ insert (5, 7) required_723_i2 := by decide +kernel
theorem child_envelope_sub_723_i2 : ∀ j, childrenD_723_i2 j ⊆ envelope_723_i2 := by decide +kernel
theorem pivot_mem_723_i2 : (5, 7) ∈ envelope_723_i2 := by decide +kernel
theorem children_work_723_i2 : ∀ j, Template HasSnaky 10 (childrenC_723_i2 j) (childrenD_723_i2 j) := by
  intro j
  fin_cases j
  · exact row_works_723_i3.mono (by decide +kernel)
  · exact row_works_723_i5.mono (by decide +kernel)
  · exact row_works_723_i6.mono (by decide +kernel)
  · exact row_works_723_i8.mono (by decide +kernel)
  · exact (placed21_template row_works_721 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_722 0 (1, 2)).mono (by decide +kernel)
theorem row_works_723_i2 : Template HasSnaky 11 required_723_i2 envelope_723_i2 := by
  refine compose HasSnaky 10 childrenC_723_i2 childrenD_723_i2 children_work_723_i2 (5, 7)
    required_723_i2 envelope_723_i2 pivot_mem_723_i2 child_required_sub_723_i2 child_envelope_sub_723_i2 ?_
  intro b hb
  exact common_sub_723_i2 (mem_commonEnvelope childrenD_723_i2 b hb)
def required_723 : Finset Cell := ⟨(([(2, 5), (3, 5), (3, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_723 : Finset Cell := ⟨(([(0, 6), (0, 7), (0, 8), (0, 9), (1, 4), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 8), (2, 9), (2, 10), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 6), (8, 7), (8, 8), (8, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_723 : Fin 5 → Finset Cell := ![(placed21 0 (1, 1) required_328), (placed21 0 (1, 1) required_330), required_723_i0, required_723_i1, required_723_i2]
def childrenD_723 : Fin 5 → Finset Cell := ![(placed21 0 (1, 1) envelope_328), (placed21 0 (1, 1) envelope_330), envelope_723_i0, envelope_723_i1, envelope_723_i2]
theorem common_sub_723 : commonEnvelope childrenD_723 ⊆ insert (5, 5) required_723 := by decide +kernel
theorem child_required_sub_723 : ∀ j, childrenC_723 j ⊆ insert (5, 5) required_723 := by decide +kernel
theorem child_envelope_sub_723 : ∀ j, childrenD_723 j ⊆ envelope_723 := by decide +kernel
theorem pivot_mem_723 : (5, 5) ∈ envelope_723 := by decide +kernel
theorem children_work_723 : ∀ j, Template HasSnaky 11 (childrenC_723 j) (childrenD_723 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_328 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_330 0 (1, 1)).mono (by decide +kernel)
  · exact row_works_723_i0.mono (by decide +kernel)
  · exact row_works_723_i1.mono (by decide +kernel)
  · exact row_works_723_i2.mono (by decide +kernel)
theorem row_works_723 : Template HasSnaky 12 required_723 envelope_723 := by
  refine compose HasSnaky 11 childrenC_723 childrenD_723 children_work_723 (5, 5)
    required_723 envelope_723 pivot_mem_723 child_required_sub_723 child_envelope_sub_723 ?_
  intro b hb
  exact common_sub_723 (mem_commonEnvelope childrenD_723 b hb)
def height_715_i1 : ℕ := 8
def childrenH_715_i1 : Fin 4 → ℕ := ![height_53, height_53, height_111, height_394]
theorem height_exact_715_i1 : height_715_i1 = 1 + Finset.univ.sup childrenH_715_i1 := by decide +kernel
theorem required_origin_715_i1 : ∀ x ∈ required_715_i1,
    (∃ j, x ∈ childrenC_715_i1 j) ∨ ∀ j, x ∈ childrenD_715_i1 j := by decide +kernel
theorem required_exact_715_i1 : required_715_i1 =
    ((Finset.univ.biUnion childrenC_715_i1) ∪ commonEnvelope childrenD_715_i1).erase (4, 4) := by
  exact required_eq_combination childrenC_715_i1 childrenD_715_i1 (4, 4) required_715_i1
    (by decide +kernel) child_required_sub_715_i1 common_sub_715_i1 required_origin_715_i1
theorem envelope_origin_715_i1 : ∀ x ∈ envelope_715_i1,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_715_i1 j := by decide +kernel
theorem envelope_exact_715_i1 : envelope_715_i1 =
    insert (4, 4) (Finset.univ.biUnion childrenD_715_i1) := by
  exact envelope_eq_combination childrenD_715_i1 (4, 4) envelope_715_i1
    pivot_mem_715_i1 child_envelope_sub_715_i1 envelope_origin_715_i1
def checked_715_i1 : CheckedCard where
  required := required_715_i1
  envelope := envelope_715_i1
  height := height_715_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_715_i1
def height_715_i0 : ℕ := 9
def childrenH_715_i0 : Fin 4 → ℕ := ![height_44, height_52, height_134, height_715_i1]
theorem height_exact_715_i0 : height_715_i0 = 1 + Finset.univ.sup childrenH_715_i0 := by decide +kernel
theorem required_origin_715_i0 : ∀ x ∈ required_715_i0,
    (∃ j, x ∈ childrenC_715_i0 j) ∨ ∀ j, x ∈ childrenD_715_i0 j := by decide +kernel
theorem required_exact_715_i0 : required_715_i0 =
    ((Finset.univ.biUnion childrenC_715_i0) ∪ commonEnvelope childrenD_715_i0).erase (3, 5) := by
  exact required_eq_combination childrenC_715_i0 childrenD_715_i0 (3, 5) required_715_i0
    (by decide +kernel) child_required_sub_715_i0 common_sub_715_i0 required_origin_715_i0
theorem envelope_origin_715_i0 : ∀ x ∈ envelope_715_i0,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_715_i0 j := by decide +kernel
theorem envelope_exact_715_i0 : envelope_715_i0 =
    insert (3, 5) (Finset.univ.biUnion childrenD_715_i0) := by
  exact envelope_eq_combination childrenD_715_i0 (3, 5) envelope_715_i0
    pivot_mem_715_i0 child_envelope_sub_715_i0 envelope_origin_715_i0
def checked_715_i0 : CheckedCard where
  required := required_715_i0
  envelope := envelope_715_i0
  height := height_715_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_715_i0
def height_715_i4 : ℕ := 8
def childrenH_715_i4 : Fin 4 → ℕ := ![height_30, height_110, height_296, height_511]
theorem height_exact_715_i4 : height_715_i4 = 1 + Finset.univ.sup childrenH_715_i4 := by decide +kernel
theorem required_origin_715_i4 : ∀ x ∈ required_715_i4,
    (∃ j, x ∈ childrenC_715_i4 j) ∨ ∀ j, x ∈ childrenD_715_i4 j := by decide +kernel
theorem required_exact_715_i4 : required_715_i4 =
    ((Finset.univ.biUnion childrenC_715_i4) ∪ commonEnvelope childrenD_715_i4).erase (7, 6) := by
  exact required_eq_combination childrenC_715_i4 childrenD_715_i4 (7, 6) required_715_i4
    (by decide +kernel) child_required_sub_715_i4 common_sub_715_i4 required_origin_715_i4
theorem envelope_origin_715_i4 : ∀ x ∈ envelope_715_i4,
    x = (7, 6) ∨ ∃ j, x ∈ childrenD_715_i4 j := by decide +kernel
theorem envelope_exact_715_i4 : envelope_715_i4 =
    insert (7, 6) (Finset.univ.biUnion childrenD_715_i4) := by
  exact envelope_eq_combination childrenD_715_i4 (7, 6) envelope_715_i4
    pivot_mem_715_i4 child_envelope_sub_715_i4 envelope_origin_715_i4
def checked_715_i4 : CheckedCard where
  required := required_715_i4
  envelope := envelope_715_i4
  height := height_715_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_715_i4
def height_715_i3 : ℕ := 10
def childrenH_715_i3 : Fin 4 → ℕ := ![height_22, height_74, height_325, height_715_i4]
theorem height_exact_715_i3 : height_715_i3 = 1 + Finset.univ.sup childrenH_715_i3 := by decide +kernel
theorem required_origin_715_i3 : ∀ x ∈ required_715_i3,
    (∃ j, x ∈ childrenC_715_i3 j) ∨ ∀ j, x ∈ childrenD_715_i3 j := by decide +kernel
theorem required_exact_715_i3 : required_715_i3 =
    ((Finset.univ.biUnion childrenC_715_i3) ∪ commonEnvelope childrenD_715_i3).erase (7, 5) := by
  exact required_eq_combination childrenC_715_i3 childrenD_715_i3 (7, 5) required_715_i3
    (by decide +kernel) child_required_sub_715_i3 common_sub_715_i3 required_origin_715_i3
theorem envelope_origin_715_i3 : ∀ x ∈ envelope_715_i3,
    x = (7, 5) ∨ ∃ j, x ∈ childrenD_715_i3 j := by decide +kernel
theorem envelope_exact_715_i3 : envelope_715_i3 =
    insert (7, 5) (Finset.univ.biUnion childrenD_715_i3) := by
  exact envelope_eq_combination childrenD_715_i3 (7, 5) envelope_715_i3
    pivot_mem_715_i3 child_envelope_sub_715_i3 envelope_origin_715_i3
def checked_715_i3 : CheckedCard where
  required := required_715_i3
  envelope := envelope_715_i3
  height := height_715_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_715_i3
def height_715_i2 : ℕ := 11
def childrenH_715_i2 : Fin 5 → ℕ := ![height_361, height_408, height_621, height_714, height_715_i3]
theorem height_exact_715_i2 : height_715_i2 = 1 + Finset.univ.sup childrenH_715_i2 := by decide +kernel
theorem required_origin_715_i2 : ∀ x ∈ required_715_i2,
    (∃ j, x ∈ childrenC_715_i2 j) ∨ ∀ j, x ∈ childrenD_715_i2 j := by decide +kernel
theorem required_exact_715_i2 : required_715_i2 =
    ((Finset.univ.biUnion childrenC_715_i2) ∪ commonEnvelope childrenD_715_i2).erase (4, 6) := by
  exact required_eq_combination childrenC_715_i2 childrenD_715_i2 (4, 6) required_715_i2
    (by decide +kernel) child_required_sub_715_i2 common_sub_715_i2 required_origin_715_i2
theorem envelope_origin_715_i2 : ∀ x ∈ envelope_715_i2,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_715_i2 j := by decide +kernel
theorem envelope_exact_715_i2 : envelope_715_i2 =
    insert (4, 6) (Finset.univ.biUnion childrenD_715_i2) := by
  exact envelope_eq_combination childrenD_715_i2 (4, 6) envelope_715_i2
    pivot_mem_715_i2 child_envelope_sub_715_i2 envelope_origin_715_i2
def checked_715_i2 : CheckedCard where
  required := required_715_i2
  envelope := envelope_715_i2
  height := height_715_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_715_i2
def height_715 : ℕ := 12
def childrenH_715 : Fin 8 → ℕ := ![height_523, height_532, height_536, height_545, height_655, height_664, height_715_i0, height_715_i2]
theorem height_exact_715 : height_715 = 1 + Finset.univ.sup childrenH_715 := by decide +kernel
theorem required_origin_715 : ∀ x ∈ required_715,
    (∃ j, x ∈ childrenC_715 j) ∨ ∀ j, x ∈ childrenD_715 j := by decide +kernel
theorem required_exact_715 : required_715 =
    ((Finset.univ.biUnion childrenC_715) ∪ commonEnvelope childrenD_715).erase (5, 6) := by
  exact required_eq_combination childrenC_715 childrenD_715 (5, 6) required_715
    (by decide +kernel) child_required_sub_715 common_sub_715 required_origin_715
theorem envelope_origin_715 : ∀ x ∈ envelope_715,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_715 j := by decide +kernel
theorem envelope_exact_715 : envelope_715 =
    insert (5, 6) (Finset.univ.biUnion childrenD_715) := by
  exact envelope_eq_combination childrenD_715 (5, 6) envelope_715
    pivot_mem_715 child_envelope_sub_715 envelope_origin_715
def checked_715 : CheckedCard where
  required := required_715
  envelope := envelope_715
  height := height_715
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_715
def height_717 : ℕ := 12
def childrenH_717 : Fin 10 → ℕ := ![height_192, height_192, height_550, height_550, height_578, height_578, height_622, height_622, height_716, height_716]
theorem height_exact_717 : height_717 = 1 + Finset.univ.sup childrenH_717 := by decide +kernel
theorem required_origin_717 : ∀ x ∈ required_717,
    (∃ j, x ∈ childrenC_717 j) ∨ ∀ j, x ∈ childrenD_717 j := by decide +kernel
theorem required_exact_717 : required_717 =
    ((Finset.univ.biUnion childrenC_717) ∪ commonEnvelope childrenD_717).erase (6, 6) := by
  exact required_eq_combination childrenC_717 childrenD_717 (6, 6) required_717
    (by decide +kernel) child_required_sub_717 common_sub_717 required_origin_717
theorem envelope_origin_717 : ∀ x ∈ envelope_717,
    x = (6, 6) ∨ ∃ j, x ∈ childrenD_717 j := by decide +kernel
theorem envelope_exact_717 : envelope_717 =
    insert (6, 6) (Finset.univ.biUnion childrenD_717) := by
  exact envelope_eq_combination childrenD_717 (6, 6) envelope_717
    pivot_mem_717 child_envelope_sub_717 envelope_origin_717
def checked_717 : CheckedCard where
  required := required_717
  envelope := envelope_717
  height := height_717
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_717
def height_723_i0 : ℕ := 9
def childrenH_723_i0 : Fin 2 → ℕ := ![height_46, height_321]
theorem height_exact_723_i0 : height_723_i0 = 1 + Finset.univ.sup childrenH_723_i0 := by decide +kernel
theorem required_origin_723_i0 : ∀ x ∈ required_723_i0,
    (∃ j, x ∈ childrenC_723_i0 j) ∨ ∀ j, x ∈ childrenD_723_i0 j := by decide +kernel
theorem required_exact_723_i0 : required_723_i0 =
    ((Finset.univ.biUnion childrenC_723_i0) ∪ commonEnvelope childrenD_723_i0).erase (4, 5) := by
  exact required_eq_combination childrenC_723_i0 childrenD_723_i0 (4, 5) required_723_i0
    (by decide +kernel) child_required_sub_723_i0 common_sub_723_i0 required_origin_723_i0
theorem envelope_origin_723_i0 : ∀ x ∈ envelope_723_i0,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_723_i0 j := by decide +kernel
theorem envelope_exact_723_i0 : envelope_723_i0 =
    insert (4, 5) (Finset.univ.biUnion childrenD_723_i0) := by
  exact envelope_eq_combination childrenD_723_i0 (4, 5) envelope_723_i0
    pivot_mem_723_i0 child_envelope_sub_723_i0 envelope_origin_723_i0
def checked_723_i0 : CheckedCard where
  required := required_723_i0
  envelope := envelope_723_i0
  height := height_723_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_723_i0
def height_723_i1 : ℕ := 4
def childrenH_723_i1 : Fin 3 → ℕ := ![height_53, height_53, height_310]
theorem height_exact_723_i1 : height_723_i1 = 1 + Finset.univ.sup childrenH_723_i1 := by decide +kernel
theorem required_origin_723_i1 : ∀ x ∈ required_723_i1,
    (∃ j, x ∈ childrenC_723_i1 j) ∨ ∀ j, x ∈ childrenD_723_i1 j := by decide +kernel
theorem required_exact_723_i1 : required_723_i1 =
    ((Finset.univ.biUnion childrenC_723_i1) ∪ commonEnvelope childrenD_723_i1).erase (2, 4) := by
  exact required_eq_combination childrenC_723_i1 childrenD_723_i1 (2, 4) required_723_i1
    (by decide +kernel) child_required_sub_723_i1 common_sub_723_i1 required_origin_723_i1
theorem envelope_origin_723_i1 : ∀ x ∈ envelope_723_i1,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_723_i1 j := by decide +kernel
theorem envelope_exact_723_i1 : envelope_723_i1 =
    insert (2, 4) (Finset.univ.biUnion childrenD_723_i1) := by
  exact envelope_eq_combination childrenD_723_i1 (2, 4) envelope_723_i1
    pivot_mem_723_i1 child_envelope_sub_723_i1 envelope_origin_723_i1
def checked_723_i1 : CheckedCard where
  required := required_723_i1
  envelope := envelope_723_i1
  height := height_723_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_723_i1
def height_723_i4 : ℕ := 5
def childrenH_723_i4 : Fin 3 → ℕ := ![height_9, height_90, height_99]
theorem height_exact_723_i4 : height_723_i4 = 1 + Finset.univ.sup childrenH_723_i4 := by decide +kernel
theorem required_origin_723_i4 : ∀ x ∈ required_723_i4,
    (∃ j, x ∈ childrenC_723_i4 j) ∨ ∀ j, x ∈ childrenD_723_i4 j := by decide +kernel
theorem required_exact_723_i4 : required_723_i4 =
    ((Finset.univ.biUnion childrenC_723_i4) ∪ commonEnvelope childrenD_723_i4).erase (3, 4) := by
  exact required_eq_combination childrenC_723_i4 childrenD_723_i4 (3, 4) required_723_i4
    (by decide +kernel) child_required_sub_723_i4 common_sub_723_i4 required_origin_723_i4
theorem envelope_origin_723_i4 : ∀ x ∈ envelope_723_i4,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_723_i4 j := by decide +kernel
theorem envelope_exact_723_i4 : envelope_723_i4 =
    insert (3, 4) (Finset.univ.biUnion childrenD_723_i4) := by
  exact envelope_eq_combination childrenD_723_i4 (3, 4) envelope_723_i4
    pivot_mem_723_i4 child_envelope_sub_723_i4 envelope_origin_723_i4
def checked_723_i4 : CheckedCard where
  required := required_723_i4
  envelope := envelope_723_i4
  height := height_723_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_723_i4
def height_723_i3 : ℕ := 7
def childrenH_723_i3 : Fin 4 → ℕ := ![height_44, height_52, height_180, height_723_i4]
theorem height_exact_723_i3 : height_723_i3 = 1 + Finset.univ.sup childrenH_723_i3 := by decide +kernel
theorem required_origin_723_i3 : ∀ x ∈ required_723_i3,
    (∃ j, x ∈ childrenC_723_i3 j) ∨ ∀ j, x ∈ childrenD_723_i3 j := by decide +kernel
theorem required_exact_723_i3 : required_723_i3 =
    ((Finset.univ.biUnion childrenC_723_i3) ∪ commonEnvelope childrenD_723_i3).erase (3, 7) := by
  exact required_eq_combination childrenC_723_i3 childrenD_723_i3 (3, 7) required_723_i3
    (by decide +kernel) child_required_sub_723_i3 common_sub_723_i3 required_origin_723_i3
theorem envelope_origin_723_i3 : ∀ x ∈ envelope_723_i3,
    x = (3, 7) ∨ ∃ j, x ∈ childrenD_723_i3 j := by decide +kernel
theorem envelope_exact_723_i3 : envelope_723_i3 =
    insert (3, 7) (Finset.univ.biUnion childrenD_723_i3) := by
  exact envelope_eq_combination childrenD_723_i3 (3, 7) envelope_723_i3
    pivot_mem_723_i3 child_envelope_sub_723_i3 envelope_origin_723_i3
def checked_723_i3 : CheckedCard where
  required := required_723_i3
  envelope := envelope_723_i3
  height := height_723_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_723_i3
def height_723_i5 : ℕ := 7
def childrenH_723_i5 : Fin 4 → ℕ := ![height_82, height_176, height_218, height_369]
theorem height_exact_723_i5 : height_723_i5 = 1 + Finset.univ.sup childrenH_723_i5 := by decide +kernel
theorem required_origin_723_i5 : ∀ x ∈ required_723_i5,
    (∃ j, x ∈ childrenC_723_i5 j) ∨ ∀ j, x ∈ childrenD_723_i5 j := by decide +kernel
theorem required_exact_723_i5 : required_723_i5 =
    ((Finset.univ.biUnion childrenC_723_i5) ∪ commonEnvelope childrenD_723_i5).erase (5, 6) := by
  exact required_eq_combination childrenC_723_i5 childrenD_723_i5 (5, 6) required_723_i5
    (by decide +kernel) child_required_sub_723_i5 common_sub_723_i5 required_origin_723_i5
theorem envelope_origin_723_i5 : ∀ x ∈ envelope_723_i5,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_723_i5 j := by decide +kernel
theorem envelope_exact_723_i5 : envelope_723_i5 =
    insert (5, 6) (Finset.univ.biUnion childrenD_723_i5) := by
  exact envelope_eq_combination childrenD_723_i5 (5, 6) envelope_723_i5
    pivot_mem_723_i5 child_envelope_sub_723_i5 envelope_origin_723_i5
def checked_723_i5 : CheckedCard where
  required := required_723_i5
  envelope := envelope_723_i5
  height := height_723_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_723_i5
def height_723_i7 : ℕ := 6
def childrenH_723_i7 : Fin 2 → ℕ := ![height_145, height_314]
theorem height_exact_723_i7 : height_723_i7 = 1 + Finset.univ.sup childrenH_723_i7 := by decide +kernel
theorem required_origin_723_i7 : ∀ x ∈ required_723_i7,
    (∃ j, x ∈ childrenC_723_i7 j) ∨ ∀ j, x ∈ childrenD_723_i7 j := by decide +kernel
theorem required_exact_723_i7 : required_723_i7 =
    ((Finset.univ.biUnion childrenC_723_i7) ∪ commonEnvelope childrenD_723_i7).erase (3, 4) := by
  exact required_eq_combination childrenC_723_i7 childrenD_723_i7 (3, 4) required_723_i7
    (by decide +kernel) child_required_sub_723_i7 common_sub_723_i7 required_origin_723_i7
theorem envelope_origin_723_i7 : ∀ x ∈ envelope_723_i7,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_723_i7 j := by decide +kernel
theorem envelope_exact_723_i7 : envelope_723_i7 =
    insert (3, 4) (Finset.univ.biUnion childrenD_723_i7) := by
  exact envelope_eq_combination childrenD_723_i7 (3, 4) envelope_723_i7
    pivot_mem_723_i7 child_envelope_sub_723_i7 envelope_origin_723_i7
def checked_723_i7 : CheckedCard where
  required := required_723_i7
  envelope := envelope_723_i7
  height := height_723_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_723_i7
def height_723_i6 : ℕ := 7
def childrenH_723_i6 : Fin 4 → ℕ := ![height_44, height_52, height_180, height_723_i7]
theorem height_exact_723_i6 : height_723_i6 = 1 + Finset.univ.sup childrenH_723_i6 := by decide +kernel
theorem required_origin_723_i6 : ∀ x ∈ required_723_i6,
    (∃ j, x ∈ childrenC_723_i6 j) ∨ ∀ j, x ∈ childrenD_723_i6 j := by decide +kernel
theorem required_exact_723_i6 : required_723_i6 =
    ((Finset.univ.biUnion childrenC_723_i6) ∪ commonEnvelope childrenD_723_i6).erase (3, 7) := by
  exact required_eq_combination childrenC_723_i6 childrenD_723_i6 (3, 7) required_723_i6
    (by decide +kernel) child_required_sub_723_i6 common_sub_723_i6 required_origin_723_i6
theorem envelope_origin_723_i6 : ∀ x ∈ envelope_723_i6,
    x = (3, 7) ∨ ∃ j, x ∈ childrenD_723_i6 j := by decide +kernel
theorem envelope_exact_723_i6 : envelope_723_i6 =
    insert (3, 7) (Finset.univ.biUnion childrenD_723_i6) := by
  exact envelope_eq_combination childrenD_723_i6 (3, 7) envelope_723_i6
    pivot_mem_723_i6 child_envelope_sub_723_i6 envelope_origin_723_i6
def checked_723_i6 : CheckedCard where
  required := required_723_i6
  envelope := envelope_723_i6
  height := height_723_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_723_i6
def height_723_i8 : ℕ := 10
def childrenH_723_i8 : Fin 6 → ℕ := ![height_13, height_192, height_369, height_435, height_474, height_477]
theorem height_exact_723_i8 : height_723_i8 = 1 + Finset.univ.sup childrenH_723_i8 := by decide +kernel
theorem required_origin_723_i8 : ∀ x ∈ required_723_i8,
    (∃ j, x ∈ childrenC_723_i8 j) ∨ ∀ j, x ∈ childrenD_723_i8 j := by decide +kernel
theorem required_exact_723_i8 : required_723_i8 =
    ((Finset.univ.biUnion childrenC_723_i8) ∪ commonEnvelope childrenD_723_i8).erase (5, 6) := by
  exact required_eq_combination childrenC_723_i8 childrenD_723_i8 (5, 6) required_723_i8
    (by decide +kernel) child_required_sub_723_i8 common_sub_723_i8 required_origin_723_i8
theorem envelope_origin_723_i8 : ∀ x ∈ envelope_723_i8,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_723_i8 j := by decide +kernel
theorem envelope_exact_723_i8 : envelope_723_i8 =
    insert (5, 6) (Finset.univ.biUnion childrenD_723_i8) := by
  exact envelope_eq_combination childrenD_723_i8 (5, 6) envelope_723_i8
    pivot_mem_723_i8 child_envelope_sub_723_i8 envelope_origin_723_i8
def checked_723_i8 : CheckedCard where
  required := required_723_i8
  envelope := envelope_723_i8
  height := height_723_i8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_723_i8
def height_723_i2 : ℕ := 11
def childrenH_723_i2 : Fin 6 → ℕ := ![height_723_i3, height_723_i5, height_723_i6, height_723_i8, height_721, height_722]
theorem height_exact_723_i2 : height_723_i2 = 1 + Finset.univ.sup childrenH_723_i2 := by decide +kernel
theorem required_origin_723_i2 : ∀ x ∈ required_723_i2,
    (∃ j, x ∈ childrenC_723_i2 j) ∨ ∀ j, x ∈ childrenD_723_i2 j := by decide +kernel
theorem required_exact_723_i2 : required_723_i2 =
    ((Finset.univ.biUnion childrenC_723_i2) ∪ commonEnvelope childrenD_723_i2).erase (5, 7) := by
  exact required_eq_combination childrenC_723_i2 childrenD_723_i2 (5, 7) required_723_i2
    (by decide +kernel) child_required_sub_723_i2 common_sub_723_i2 required_origin_723_i2
theorem envelope_origin_723_i2 : ∀ x ∈ envelope_723_i2,
    x = (5, 7) ∨ ∃ j, x ∈ childrenD_723_i2 j := by decide +kernel
theorem envelope_exact_723_i2 : envelope_723_i2 =
    insert (5, 7) (Finset.univ.biUnion childrenD_723_i2) := by
  exact envelope_eq_combination childrenD_723_i2 (5, 7) envelope_723_i2
    pivot_mem_723_i2 child_envelope_sub_723_i2 envelope_origin_723_i2
def checked_723_i2 : CheckedCard where
  required := required_723_i2
  envelope := envelope_723_i2
  height := height_723_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_723_i2
def height_723 : ℕ := 12
def childrenH_723 : Fin 5 → ℕ := ![height_328, height_330, height_723_i0, height_723_i1, height_723_i2]
theorem height_exact_723 : height_723 = 1 + Finset.univ.sup childrenH_723 := by decide +kernel
theorem required_origin_723 : ∀ x ∈ required_723,
    (∃ j, x ∈ childrenC_723 j) ∨ ∀ j, x ∈ childrenD_723 j := by decide +kernel
theorem required_exact_723 : required_723 =
    ((Finset.univ.biUnion childrenC_723) ∪ commonEnvelope childrenD_723).erase (5, 5) := by
  exact required_eq_combination childrenC_723 childrenD_723 (5, 5) required_723
    (by decide +kernel) child_required_sub_723 common_sub_723 required_origin_723
theorem envelope_origin_723 : ∀ x ∈ envelope_723,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_723 j := by decide +kernel
theorem envelope_exact_723 : envelope_723 =
    insert (5, 5) (Finset.univ.biUnion childrenD_723) := by
  exact envelope_eq_combination childrenD_723 (5, 5) envelope_723
    pivot_mem_723 child_envelope_sub_723 envelope_origin_723
def checked_723 : CheckedCard where
  required := required_723
  envelope := envelope_723
  height := height_723
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_723
end SnakyPrototype.Certificate21

end OAI
