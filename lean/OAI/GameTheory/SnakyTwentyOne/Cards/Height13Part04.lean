import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part04
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_650_i0 : Finset Cell := ⟨(([(3, 5), (4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_650_i0 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 7), (6, 8), (6, 9), (7, 4), (8, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_650_i0 : Fin 2 → Finset Cell := ![(placed21 3 (2, 5) required_52), (placed21 2 (6, 0) required_545)]
def childrenD_650_i0 : Fin 2 → Finset Cell := ![(placed21 3 (2, 5) envelope_52), (placed21 2 (6, 0) envelope_545)]
theorem common_sub_650_i0 : commonEnvelope childrenD_650_i0 ⊆ insert (5, 4) required_650_i0 := by decide +kernel
theorem child_required_sub_650_i0 : ∀ j, childrenC_650_i0 j ⊆ insert (5, 4) required_650_i0 := by decide +kernel
theorem child_envelope_sub_650_i0 : ∀ j, childrenD_650_i0 j ⊆ envelope_650_i0 := by decide +kernel
theorem pivot_mem_650_i0 : (5, 4) ∈ envelope_650_i0 := by decide +kernel
theorem children_work_650_i0 : ∀ j, Template HasSnaky 10 (childrenC_650_i0 j) (childrenD_650_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 3 (2, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_545 2 (6, 0)).mono (by decide +kernel)
theorem row_works_650_i0 : Template HasSnaky 11 required_650_i0 envelope_650_i0 := by
  refine compose HasSnaky 10 childrenC_650_i0 childrenD_650_i0 children_work_650_i0 (5, 4)
    required_650_i0 envelope_650_i0 pivot_mem_650_i0 child_required_sub_650_i0 child_envelope_sub_650_i0 ?_
  intro b hb
  exact common_sub_650_i0 (mem_commonEnvelope childrenD_650_i0 b hb)
def required_650 : Finset Cell := ⟨(([(3, 5), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_650 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (1, 4), (1, 6), (1, 7), (1, 8), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 2), (3, 3), (3, 4), (3, 5), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, 4), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_650 : Fin 7 → Finset Cell := ![(placed21 1 (1, 4) required_13), (placed21 1 (1, 4) required_14), (placed21 4 (2, 8) required_257), (placed21 4 (2, 8) required_435), (placed21 0 (2, 2) required_507), (placed21 4 (1, 10) required_649), required_650_i0]
def childrenD_650 : Fin 7 → Finset Cell := ![(placed21 1 (1, 4) envelope_13), (placed21 1 (1, 4) envelope_14), (placed21 4 (2, 8) envelope_257), (placed21 4 (2, 8) envelope_435), (placed21 0 (2, 2) envelope_507), (placed21 4 (1, 10) envelope_649), envelope_650_i0]
theorem common_sub_650 : commonEnvelope childrenD_650 ⊆ insert (5, 5) required_650 := by decide +kernel
theorem child_required_sub_650 : ∀ j, childrenC_650 j ⊆ insert (5, 5) required_650 := by decide +kernel
theorem child_envelope_sub_650 : ∀ j, childrenD_650 j ⊆ envelope_650 := by decide +kernel
theorem pivot_mem_650 : (5, 5) ∈ envelope_650 := by decide +kernel
theorem children_work_650 : ∀ j, Template HasSnaky 12 (childrenC_650 j) (childrenD_650 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 1 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_14 1 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_257 4 (2, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 4 (2, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_507 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_649 4 (1, 10)).mono (by decide +kernel)
  · exact row_works_650_i0.mono (by decide +kernel)
theorem row_works_650 : Template HasSnaky 13 required_650 envelope_650 := by
  refine compose HasSnaky 12 childrenC_650 childrenD_650 children_work_650 (5, 5)
    required_650 envelope_650 pivot_mem_650 child_required_sub_650 child_envelope_sub_650 ?_
  intro b hb
  exact common_sub_650 (mem_commonEnvelope childrenD_650 b hb)
def required_657_i1 : Finset Cell := ⟨(([(2, 2), (2, 3), (4, 3), (4, 4), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_657_i1 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 4), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (5, 3), (5, 4), (6, 3), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_657_i1 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) required_54), (placed21 2 (5, 1) required_79)]
def childrenD_657_i1 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) envelope_54), (placed21 2 (5, 1) envelope_79)]
theorem common_sub_657_i1 : commonEnvelope childrenD_657_i1 ⊆ insert (2, 4) required_657_i1 := by decide +kernel
theorem child_required_sub_657_i1 : ∀ j, childrenC_657_i1 j ⊆ insert (2, 4) required_657_i1 := by decide +kernel
theorem child_envelope_sub_657_i1 : ∀ j, childrenD_657_i1 j ⊆ envelope_657_i1 := by decide +kernel
theorem pivot_mem_657_i1 : (2, 4) ∈ envelope_657_i1 := by decide +kernel
theorem children_work_657_i1 : ∀ j, Template HasSnaky 4 (childrenC_657_i1 j) (childrenD_657_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_54 3 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_79 2 (5, 1)).mono (by decide +kernel)
theorem row_works_657_i1 : Template HasSnaky 5 required_657_i1 envelope_657_i1 := by
  refine compose HasSnaky 4 childrenC_657_i1 childrenD_657_i1 children_work_657_i1 (2, 4)
    required_657_i1 envelope_657_i1 pivot_mem_657_i1 child_required_sub_657_i1 child_envelope_sub_657_i1 ?_
  intro b hb
  exact common_sub_657_i1 (mem_commonEnvelope childrenD_657_i1 b hb)
def required_657_i2 : Finset Cell := ⟨(([(2, 2), (4, 3), (4, 4), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_657_i2 : Finset Cell := ⟨(([(1, 2), (2, 2), (2, 4), (3, 1), (3, 2), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (6, 3), (6, 4), (6, 5), (6, 6), (7, 3), (7, 4), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_657_i2 : Fin 3 → Finset Cell := ![(placed21 1 (1, 2) required_54), (placed21 2 (5, 1) required_71), (placed21 1 (2, 1) required_345)]
def childrenD_657_i2 : Fin 3 → Finset Cell := ![(placed21 1 (1, 2) envelope_54), (placed21 2 (5, 1) envelope_71), (placed21 1 (2, 1) envelope_345)]
theorem common_sub_657_i2 : commonEnvelope childrenD_657_i2 ⊆ insert (4, 2) required_657_i2 := by decide +kernel
theorem child_required_sub_657_i2 : ∀ j, childrenC_657_i2 j ⊆ insert (4, 2) required_657_i2 := by decide +kernel
theorem child_envelope_sub_657_i2 : ∀ j, childrenD_657_i2 j ⊆ envelope_657_i2 := by decide +kernel
theorem pivot_mem_657_i2 : (4, 2) ∈ envelope_657_i2 := by decide +kernel
theorem children_work_657_i2 : ∀ j, Template HasSnaky 8 (childrenC_657_i2 j) (childrenD_657_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_54 1 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_71 2 (5, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_345 1 (2, 1)).mono (by decide +kernel)
theorem row_works_657_i2 : Template HasSnaky 9 required_657_i2 envelope_657_i2 := by
  refine compose HasSnaky 8 childrenC_657_i2 childrenD_657_i2 children_work_657_i2 (4, 2)
    required_657_i2 envelope_657_i2 pivot_mem_657_i2 child_required_sub_657_i2 child_envelope_sub_657_i2 ?_
  intro b hb
  exact common_sub_657_i2 (mem_commonEnvelope childrenD_657_i2 b hb)
def required_657_i6 : Finset Cell := ⟨(([(3, 4), (4, 3), (4, 4), (5, 3), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_657_i6 : Finset Cell := ⟨(([(3, 4), (4, 3), (4, 4), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 0), (7, 1), (7, 2), (7, 3), (7, 5), (8, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_657_i6 : Fin 2 → Finset Cell := ![(placed21 4 (3, 4) required_5), (placed21 4 (3, 5) required_445)]
def childrenD_657_i6 : Fin 2 → Finset Cell := ![(placed21 4 (3, 4) envelope_5), (placed21 4 (3, 5) envelope_445)]
theorem common_sub_657_i6 : commonEnvelope childrenD_657_i6 ⊆ insert (6, 3) required_657_i6 := by decide +kernel
theorem child_required_sub_657_i6 : ∀ j, childrenC_657_i6 j ⊆ insert (6, 3) required_657_i6 := by decide +kernel
theorem child_envelope_sub_657_i6 : ∀ j, childrenD_657_i6 j ⊆ envelope_657_i6 := by decide +kernel
theorem pivot_mem_657_i6 : (6, 3) ∈ envelope_657_i6 := by decide +kernel
theorem children_work_657_i6 : ∀ j, Template HasSnaky 5 (childrenC_657_i6 j) (childrenD_657_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_445 4 (3, 5)).mono (by decide +kernel)
theorem row_works_657_i6 : Template HasSnaky 6 required_657_i6 envelope_657_i6 := by
  refine compose HasSnaky 5 childrenC_657_i6 childrenD_657_i6 children_work_657_i6 (6, 3)
    required_657_i6 envelope_657_i6 pivot_mem_657_i6 child_required_sub_657_i6 child_envelope_sub_657_i6 ?_
  intro b hb
  exact common_sub_657_i6 (mem_commonEnvelope childrenD_657_i6 b hb)
def required_657_i5 : Finset Cell := ⟨(([(3, 4), (4, 3), (4, 4), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_657_i5 : Finset Cell := ⟨(([(3, 4), (4, 3), (4, 4), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (8, 2), (8, 3), (8, 4), (8, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_657_i5 : Fin 3 → Finset Cell := ![(placed21 1 (3, 3) required_20), (placed21 3 (3, 4) required_29), required_657_i6]
def childrenD_657_i5 : Fin 3 → Finset Cell := ![(placed21 1 (3, 3) envelope_20), (placed21 3 (3, 4) envelope_29), envelope_657_i6]
theorem common_sub_657_i5 : commonEnvelope childrenD_657_i5 ⊆ insert (6, 4) required_657_i5 := by decide +kernel
theorem child_required_sub_657_i5 : ∀ j, childrenC_657_i5 j ⊆ insert (6, 4) required_657_i5 := by decide +kernel
theorem child_envelope_sub_657_i5 : ∀ j, childrenD_657_i5 j ⊆ envelope_657_i5 := by decide +kernel
theorem pivot_mem_657_i5 : (6, 4) ∈ envelope_657_i5 := by decide +kernel
theorem children_work_657_i5 : ∀ j, Template HasSnaky 6 (childrenC_657_i5 j) (childrenD_657_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_20 1 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_29 3 (3, 4)).mono (by decide +kernel)
  · exact row_works_657_i6.mono (by decide +kernel)
theorem row_works_657_i5 : Template HasSnaky 7 required_657_i5 envelope_657_i5 := by
  refine compose HasSnaky 6 childrenC_657_i5 childrenD_657_i5 children_work_657_i5 (6, 4)
    required_657_i5 envelope_657_i5 pivot_mem_657_i5 child_required_sub_657_i5 child_envelope_sub_657_i5 ?_
  intro b hb
  exact common_sub_657_i5 (mem_commonEnvelope childrenD_657_i5 b hb)
def required_657_i4 : Finset Cell := ⟨(([(4, 3), (4, 4), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_657_i4 : Finset Cell := ⟨(([(1, 4), (1, 5), (2, 4), (2, 5), (3, 4), (3, 5), (4, 3), (4, 4), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (8, 2), (8, 3), (8, 4), (8, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_657_i4 : Fin 3 → Finset Cell := ![(placed21 3 (2, 4) required_15), (placed21 1 (1, 3) required_65), required_657_i5]
def childrenD_657_i4 : Fin 3 → Finset Cell := ![(placed21 3 (2, 4) envelope_15), (placed21 1 (1, 3) envelope_65), envelope_657_i5]
theorem common_sub_657_i4 : commonEnvelope childrenD_657_i4 ⊆ insert (3, 4) required_657_i4 := by decide +kernel
theorem child_required_sub_657_i4 : ∀ j, childrenC_657_i4 j ⊆ insert (3, 4) required_657_i4 := by decide +kernel
theorem child_envelope_sub_657_i4 : ∀ j, childrenD_657_i4 j ⊆ envelope_657_i4 := by decide +kernel
theorem pivot_mem_657_i4 : (3, 4) ∈ envelope_657_i4 := by decide +kernel
theorem children_work_657_i4 : ∀ j, Template HasSnaky 7 (childrenC_657_i4 j) (childrenD_657_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_15 3 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_65 1 (1, 3)).mono (by decide +kernel)
  · exact row_works_657_i5.mono (by decide +kernel)
theorem row_works_657_i4 : Template HasSnaky 8 required_657_i4 envelope_657_i4 := by
  refine compose HasSnaky 7 childrenC_657_i4 childrenD_657_i4 children_work_657_i4 (3, 4)
    required_657_i4 envelope_657_i4 pivot_mem_657_i4 child_required_sub_657_i4 child_envelope_sub_657_i4 ?_
  intro b hb
  exact common_sub_657_i4 (mem_commonEnvelope childrenD_657_i4 b hb)
def required_657_i3 : Finset Cell := ⟨(([(4, 3), (4, 4), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_657_i3 : Finset Cell := ⟨(([(0, 5), (0, 7), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6), (3, 7), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_657_i3 : Fin 5 → Finset Cell := ![(placed21 5 (8, 2) required_85), (placed21 4 (3, 7) required_85), (placed21 4 (4, 7) required_411), (placed21 5 (8, 2) required_537), required_657_i4]
def childrenD_657_i3 : Fin 5 → Finset Cell := ![(placed21 5 (8, 2) envelope_85), (placed21 4 (3, 7) envelope_85), (placed21 4 (4, 7) envelope_411), (placed21 5 (8, 2) envelope_537), envelope_657_i4]
theorem common_sub_657_i3 : commonEnvelope childrenD_657_i3 ⊆ insert (5, 4) required_657_i3 := by decide +kernel
theorem child_required_sub_657_i3 : ∀ j, childrenC_657_i3 j ⊆ insert (5, 4) required_657_i3 := by decide +kernel
theorem child_envelope_sub_657_i3 : ∀ j, childrenD_657_i3 j ⊆ envelope_657_i3 := by decide +kernel
theorem pivot_mem_657_i3 : (5, 4) ∈ envelope_657_i3 := by decide +kernel
theorem children_work_657_i3 : ∀ j, Template HasSnaky 10 (childrenC_657_i3 j) (childrenD_657_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_85 5 (8, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_85 4 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_411 4 (4, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_537 5 (8, 2)).mono (by decide +kernel)
  · exact row_works_657_i4.mono (by decide +kernel)
theorem row_works_657_i3 : Template HasSnaky 11 required_657_i3 envelope_657_i3 := by
  refine compose HasSnaky 10 childrenC_657_i3 childrenD_657_i3 children_work_657_i3 (5, 4)
    required_657_i3 envelope_657_i3 pivot_mem_657_i3 child_required_sub_657_i3 child_envelope_sub_657_i3 ?_
  intro b hb
  exact common_sub_657_i3 (mem_commonEnvelope childrenD_657_i3 b hb)
def required_657_i0 : Finset Cell := ⟨(([(2, 2), (2, 3), (4, 3), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_657_i0 : Finset Cell := ⟨(([(0, 5), (0, 7), (1, 1), (1, 2), (1, 4), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (9, 2), (9, 4), (9, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_657_i0 : Fin 6 → Finset Cell := ![(placed21 1 (1, 1) required_510), (placed21 0 (1, 0) required_631), (placed21 1 (1, 0) required_653), required_657_i1, required_657_i2, required_657_i3]
def childrenD_657_i0 : Fin 6 → Finset Cell := ![(placed21 1 (1, 1) envelope_510), (placed21 0 (1, 0) envelope_631), (placed21 1 (1, 0) envelope_653), envelope_657_i1, envelope_657_i2, envelope_657_i3]
theorem common_sub_657_i0 : commonEnvelope childrenD_657_i0 ⊆ insert (4, 4) required_657_i0 := by decide +kernel
theorem child_required_sub_657_i0 : ∀ j, childrenC_657_i0 j ⊆ insert (4, 4) required_657_i0 := by decide +kernel
theorem child_envelope_sub_657_i0 : ∀ j, childrenD_657_i0 j ⊆ envelope_657_i0 := by decide +kernel
theorem pivot_mem_657_i0 : (4, 4) ∈ envelope_657_i0 := by decide +kernel
theorem children_work_657_i0 : ∀ j, Template HasSnaky 11 (childrenC_657_i0 j) (childrenD_657_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_510 1 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_631 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_653 1 (1, 0)).mono (by decide +kernel)
  · exact row_works_657_i1.mono (by decide +kernel)
  · exact row_works_657_i2.mono (by decide +kernel)
  · exact row_works_657_i3.mono (by decide +kernel)
theorem row_works_657_i0 : Template HasSnaky 12 required_657_i0 envelope_657_i0 := by
  refine compose HasSnaky 11 childrenC_657_i0 childrenD_657_i0 children_work_657_i0 (4, 4)
    required_657_i0 envelope_657_i0 pivot_mem_657_i0 child_required_sub_657_i0 child_envelope_sub_657_i0 ?_
  intro b hb
  exact common_sub_657_i0 (mem_commonEnvelope childrenD_657_i0 b hb)
def required_657 : Finset Cell := ⟨(([(2, 2), (2, 3), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_657 : Finset Cell := ⟨(([(0, 5), (0, 7), (1, 1), (1, 2), (1, 4), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (9, 2), (9, 4), (9, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_657 : Fin 5 → Finset Cell := ![(placed21 1 (1, 2) required_50), (placed21 1 (1, 2) required_125), (placed21 0 (1, 1) required_478), (placed21 0 (1, 1) required_482), required_657_i0]
def childrenD_657 : Fin 5 → Finset Cell := ![(placed21 1 (1, 2) envelope_50), (placed21 1 (1, 2) envelope_125), (placed21 0 (1, 1) envelope_478), (placed21 0 (1, 1) envelope_482), envelope_657_i0]
theorem common_sub_657 : commonEnvelope childrenD_657 ⊆ insert (4, 3) required_657 := by decide +kernel
theorem child_required_sub_657 : ∀ j, childrenC_657 j ⊆ insert (4, 3) required_657 := by decide +kernel
theorem child_envelope_sub_657 : ∀ j, childrenD_657 j ⊆ envelope_657 := by decide +kernel
theorem pivot_mem_657 : (4, 3) ∈ envelope_657 := by decide +kernel
theorem children_work_657 : ∀ j, Template HasSnaky 12 (childrenC_657 j) (childrenD_657 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_50 1 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_125 1 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_478 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_482 0 (1, 1)).mono (by decide +kernel)
  · exact row_works_657_i0.mono (by decide +kernel)
theorem row_works_657 : Template HasSnaky 13 required_657 envelope_657 := by
  refine compose HasSnaky 12 childrenC_657 childrenD_657 children_work_657 (4, 3)
    required_657 envelope_657 pivot_mem_657 child_required_sub_657 child_envelope_sub_657 ?_
  intro b hb
  exact common_sub_657 (mem_commonEnvelope childrenD_657 b hb)
def required_665_i0 : Finset Cell := ⟨(([(3, 3), (3, 6), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_665_i0 : Finset Cell := ⟨(([(0, 7), (0, 9), (1, 7), (1, 8), (1, 9), (2, 7), (2, 8), (2, 9), (3, 3), (3, 4), (3, 5), (3, 6), (3, 8), (3, 9), (3, 10), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 3), (5, 4), (5, 5), (5, 7), (5, 8), (5, 9), (5, 10), (6, 7), (6, 8), (6, 9), (7, 7), (7, 8), (7, 9), (8, 7), (8, 8), (8, 9), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_665_i0 : Fin 4 → Finset Cell := ![(placed21 6 (4, 7) required_70), (placed21 0 (3, 3) required_106), (placed21 0 (3, 3) required_269), (placed21 1 (0, 4) required_322)]
def childrenD_665_i0 : Fin 4 → Finset Cell := ![(placed21 6 (4, 7) envelope_70), (placed21 0 (3, 3) envelope_106), (placed21 0 (3, 3) envelope_269), (placed21 1 (0, 4) envelope_322)]
theorem common_sub_665_i0 : commonEnvelope childrenD_665_i0 ⊆ insert (4, 7) required_665_i0 := by decide +kernel
theorem child_required_sub_665_i0 : ∀ j, childrenC_665_i0 j ⊆ insert (4, 7) required_665_i0 := by decide +kernel
theorem child_envelope_sub_665_i0 : ∀ j, childrenD_665_i0 j ⊆ envelope_665_i0 := by decide +kernel
theorem pivot_mem_665_i0 : (4, 7) ∈ envelope_665_i0 := by decide +kernel
theorem children_work_665_i0 : ∀ j, Template HasSnaky 9 (childrenC_665_i0 j) (childrenD_665_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_70 6 (4, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_106 0 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_269 0 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_322 1 (0, 4)).mono (by decide +kernel)
theorem row_works_665_i0 : Template HasSnaky 10 required_665_i0 envelope_665_i0 := by
  refine compose HasSnaky 9 childrenC_665_i0 childrenD_665_i0 children_work_665_i0 (4, 7)
    required_665_i0 envelope_665_i0 pivot_mem_665_i0 child_required_sub_665_i0 child_envelope_sub_665_i0 ?_
  intro b hb
  exact common_sub_665_i0 (mem_commonEnvelope childrenD_665_i0 b hb)
def required_665_i1 : Finset Cell := ⟨(([(3, 3), (3, 6), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_665_i1 : Finset Cell := ⟨(([(0, 8), (0, 9), (1, 7), (1, 8), (1, 9), (2, 7), (2, 8), (2, 9), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 6), (6, 7), (6, 8), (7, 7), (7, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_665_i1 : Fin 3 → Finset Cell := ![(placed21 6 (4, 7) required_70), (placed21 5 (7, 4) required_257), (placed21 5 (7, 4) required_435)]
def childrenD_665_i1 : Fin 3 → Finset Cell := ![(placed21 6 (4, 7) envelope_70), (placed21 5 (7, 4) envelope_257), (placed21 5 (7, 4) envelope_435)]
theorem common_sub_665_i1 : commonEnvelope childrenD_665_i1 ⊆ insert (4, 7) required_665_i1 := by decide +kernel
theorem child_required_sub_665_i1 : ∀ j, childrenC_665_i1 j ⊆ insert (4, 7) required_665_i1 := by decide +kernel
theorem child_envelope_sub_665_i1 : ∀ j, childrenD_665_i1 j ⊆ envelope_665_i1 := by decide +kernel
theorem pivot_mem_665_i1 : (4, 7) ∈ envelope_665_i1 := by decide +kernel
theorem children_work_665_i1 : ∀ j, Template HasSnaky 8 (childrenC_665_i1 j) (childrenD_665_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_70 6 (4, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_257 5 (7, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 5 (7, 4)).mono (by decide +kernel)
theorem row_works_665_i1 : Template HasSnaky 9 required_665_i1 envelope_665_i1 := by
  refine compose HasSnaky 8 childrenC_665_i1 childrenD_665_i1 children_work_665_i1 (4, 7)
    required_665_i1 envelope_665_i1 pivot_mem_665_i1 child_required_sub_665_i1 child_envelope_sub_665_i1 ?_
  intro b hb
  exact common_sub_665_i1 (mem_commonEnvelope childrenD_665_i1 b hb)
def required_665_i4 : Finset Cell := ⟨(([(2, 3), (3, 4), (3, 5), (3, 6), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_665_i4 : Finset Cell := ⟨(([(2, 3), (2, 4), (2, 7), (2, 8), (2, 9), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 5), (4, 6), (4, 8), (4, 9), (4, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_665_i4 : Fin 2 → Finset Cell := ![(placed21 7 (3, 7) required_4), (placed21 5 (4, 4) required_93)]
def childrenD_665_i4 : Fin 2 → Finset Cell := ![(placed21 7 (3, 7) envelope_4), (placed21 5 (4, 4) envelope_93)]
theorem common_sub_665_i4 : commonEnvelope childrenD_665_i4 ⊆ insert (3, 7) required_665_i4 := by decide +kernel
theorem child_required_sub_665_i4 : ∀ j, childrenC_665_i4 j ⊆ insert (3, 7) required_665_i4 := by decide +kernel
theorem child_envelope_sub_665_i4 : ∀ j, childrenD_665_i4 j ⊆ envelope_665_i4 := by decide +kernel
theorem pivot_mem_665_i4 : (3, 7) ∈ envelope_665_i4 := by decide +kernel
theorem children_work_665_i4 : ∀ j, Template HasSnaky 4 (childrenC_665_i4 j) (childrenD_665_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 7 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_93 5 (4, 4)).mono (by decide +kernel)
theorem row_works_665_i4 : Template HasSnaky 5 required_665_i4 envelope_665_i4 := by
  refine compose HasSnaky 4 childrenC_665_i4 childrenD_665_i4 children_work_665_i4 (3, 7)
    required_665_i4 envelope_665_i4 pivot_mem_665_i4 child_required_sub_665_i4 child_envelope_sub_665_i4 ?_
  intro b hb
  exact common_sub_665_i4 (mem_commonEnvelope childrenD_665_i4 b hb)
def required_665_i3 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 5), (3, 6), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_665_i3 : Finset Cell := ⟨(([(2, 2), (2, 3), (2, 4), (2, 7), (2, 8), (2, 9), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 5), (4, 6), (4, 8), (4, 9), (4, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_665_i3 : Fin 2 → Finset Cell := ![(placed21 7 (3, 6) required_5), required_665_i4]
def childrenD_665_i3 : Fin 2 → Finset Cell := ![(placed21 7 (3, 6) envelope_5), envelope_665_i4]
theorem common_sub_665_i3 : commonEnvelope childrenD_665_i3 ⊆ insert (3, 4) required_665_i3 := by decide +kernel
theorem child_required_sub_665_i3 : ∀ j, childrenC_665_i3 j ⊆ insert (3, 4) required_665_i3 := by decide +kernel
theorem child_envelope_sub_665_i3 : ∀ j, childrenD_665_i3 j ⊆ envelope_665_i3 := by decide +kernel
theorem pivot_mem_665_i3 : (3, 4) ∈ envelope_665_i3 := by decide +kernel
theorem children_work_665_i3 : ∀ j, Template HasSnaky 5 (childrenC_665_i3 j) (childrenD_665_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (3, 6)).mono (by decide +kernel)
  · exact row_works_665_i4.mono (by decide +kernel)
theorem row_works_665_i3 : Template HasSnaky 6 required_665_i3 envelope_665_i3 := by
  refine compose HasSnaky 5 childrenC_665_i3 childrenD_665_i3 children_work_665_i3 (3, 4)
    required_665_i3 envelope_665_i3 pivot_mem_665_i3 child_required_sub_665_i3 child_envelope_sub_665_i3 ?_
  intro b hb
  exact common_sub_665_i3 (mem_commonEnvelope childrenD_665_i3 b hb)
def required_665_i2 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 6), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_665_i2 : Finset Cell := ⟨(([(0, 7), (0, 8), (0, 9), (1, 7), (1, 8), (1, 9), (2, 2), (2, 3), (2, 4), (2, 7), (2, 8), (2, 9), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 7), (8, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_665_i2 : Fin 3 → Finset Cell := ![(placed21 6 (4, 7) required_40), (placed21 1 (0, 4) required_517), required_665_i3]
def childrenD_665_i2 : Fin 3 → Finset Cell := ![(placed21 6 (4, 7) envelope_40), (placed21 1 (0, 4) envelope_517), envelope_665_i3]
theorem common_sub_665_i2 : commonEnvelope childrenD_665_i2 ⊆ insert (3, 5) required_665_i2 := by decide +kernel
theorem child_required_sub_665_i2 : ∀ j, childrenC_665_i2 j ⊆ insert (3, 5) required_665_i2 := by decide +kernel
theorem child_envelope_sub_665_i2 : ∀ j, childrenD_665_i2 j ⊆ envelope_665_i2 := by decide +kernel
theorem pivot_mem_665_i2 : (3, 5) ∈ envelope_665_i2 := by decide +kernel
theorem children_work_665_i2 : ∀ j, Template HasSnaky 11 (childrenC_665_i2 j) (childrenD_665_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_40 6 (4, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_517 1 (0, 4)).mono (by decide +kernel)
  · exact row_works_665_i3.mono (by decide +kernel)
theorem row_works_665_i2 : Template HasSnaky 12 required_665_i2 envelope_665_i2 := by
  refine compose HasSnaky 11 childrenC_665_i2 childrenD_665_i2 children_work_665_i2 (3, 5)
    required_665_i2 envelope_665_i2 pivot_mem_665_i2 child_required_sub_665_i2 child_envelope_sub_665_i2 ?_
  intro b hb
  exact common_sub_665_i2 (mem_commonEnvelope childrenD_665_i2 b hb)
def required_665 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 6), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_665 : Finset Cell := ⟨(([(0, 7), (0, 8), (0, 9), (1, 0), (1, 1), (1, 2), (1, 4), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 7), (2, 8), (2, 9), (3, 0), (3, 1), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 2), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 6), (8, 7), (8, 8), (8, 9), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_665 : Fin 5 → Finset Cell := ![(placed21 0 (3, 1) required_459), (placed21 3 (1, 7) required_588), required_665_i0, required_665_i1, required_665_i2]
def childrenD_665 : Fin 5 → Finset Cell := ![(placed21 0 (3, 1) envelope_459), (placed21 3 (1, 7) envelope_588), envelope_665_i0, envelope_665_i1, envelope_665_i2]
theorem common_sub_665 : commonEnvelope childrenD_665 ⊆ insert (4, 5) required_665 := by decide +kernel
theorem child_required_sub_665 : ∀ j, childrenC_665 j ⊆ insert (4, 5) required_665 := by decide +kernel
theorem child_envelope_sub_665 : ∀ j, childrenD_665 j ⊆ envelope_665 := by decide +kernel
theorem pivot_mem_665 : (4, 5) ∈ envelope_665 := by decide +kernel
theorem children_work_665 : ∀ j, Template HasSnaky 12 (childrenC_665 j) (childrenD_665 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_459 0 (3, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_588 3 (1, 7)).mono (by decide +kernel)
  · exact row_works_665_i0.mono (by decide +kernel)
  · exact row_works_665_i1.mono (by decide +kernel)
  · exact row_works_665_i2.mono (by decide +kernel)
theorem row_works_665 : Template HasSnaky 13 required_665 envelope_665 := by
  refine compose HasSnaky 12 childrenC_665 childrenD_665 children_work_665 (4, 5)
    required_665 envelope_665 pivot_mem_665 child_required_sub_665 child_envelope_sub_665 ?_
  intro b hb
  exact common_sub_665 (mem_commonEnvelope childrenD_665 b hb)
def height_650_i0 : ℕ := 11
def childrenH_650_i0 : Fin 2 → ℕ := ![height_52, height_545]
theorem height_exact_650_i0 : height_650_i0 = 1 + Finset.univ.sup childrenH_650_i0 := by decide +kernel
theorem required_origin_650_i0 : ∀ x ∈ required_650_i0,
    (∃ j, x ∈ childrenC_650_i0 j) ∨ ∀ j, x ∈ childrenD_650_i0 j := by decide +kernel
theorem required_exact_650_i0 : required_650_i0 =
    ((Finset.univ.biUnion childrenC_650_i0) ∪ commonEnvelope childrenD_650_i0).erase (5, 4) := by
  exact required_eq_combination childrenC_650_i0 childrenD_650_i0 (5, 4) required_650_i0
    (by decide +kernel) child_required_sub_650_i0 common_sub_650_i0 required_origin_650_i0
theorem envelope_origin_650_i0 : ∀ x ∈ envelope_650_i0,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_650_i0 j := by decide +kernel
theorem envelope_exact_650_i0 : envelope_650_i0 =
    insert (5, 4) (Finset.univ.biUnion childrenD_650_i0) := by
  exact envelope_eq_combination childrenD_650_i0 (5, 4) envelope_650_i0
    pivot_mem_650_i0 child_envelope_sub_650_i0 envelope_origin_650_i0
def checked_650_i0 : CheckedCard where
  required := required_650_i0
  envelope := envelope_650_i0
  height := height_650_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_650_i0
def height_650 : ℕ := 13
def childrenH_650 : Fin 7 → ℕ := ![height_13, height_14, height_257, height_435, height_507, height_649, height_650_i0]
theorem height_exact_650 : height_650 = 1 + Finset.univ.sup childrenH_650 := by decide +kernel
theorem required_origin_650 : ∀ x ∈ required_650,
    (∃ j, x ∈ childrenC_650 j) ∨ ∀ j, x ∈ childrenD_650 j := by decide +kernel
theorem required_exact_650 : required_650 =
    ((Finset.univ.biUnion childrenC_650) ∪ commonEnvelope childrenD_650).erase (5, 5) := by
  exact required_eq_combination childrenC_650 childrenD_650 (5, 5) required_650
    (by decide +kernel) child_required_sub_650 common_sub_650 required_origin_650
theorem envelope_origin_650 : ∀ x ∈ envelope_650,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_650 j := by decide +kernel
theorem envelope_exact_650 : envelope_650 =
    insert (5, 5) (Finset.univ.biUnion childrenD_650) := by
  exact envelope_eq_combination childrenD_650 (5, 5) envelope_650
    pivot_mem_650 child_envelope_sub_650 envelope_origin_650
def checked_650 : CheckedCard where
  required := required_650
  envelope := envelope_650
  height := height_650
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_650
def height_657_i1 : ℕ := 5
def childrenH_657_i1 : Fin 2 → ℕ := ![height_54, height_79]
theorem height_exact_657_i1 : height_657_i1 = 1 + Finset.univ.sup childrenH_657_i1 := by decide +kernel
theorem required_origin_657_i1 : ∀ x ∈ required_657_i1,
    (∃ j, x ∈ childrenC_657_i1 j) ∨ ∀ j, x ∈ childrenD_657_i1 j := by decide +kernel
theorem required_exact_657_i1 : required_657_i1 =
    ((Finset.univ.biUnion childrenC_657_i1) ∪ commonEnvelope childrenD_657_i1).erase (2, 4) := by
  exact required_eq_combination childrenC_657_i1 childrenD_657_i1 (2, 4) required_657_i1
    (by decide +kernel) child_required_sub_657_i1 common_sub_657_i1 required_origin_657_i1
theorem envelope_origin_657_i1 : ∀ x ∈ envelope_657_i1,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_657_i1 j := by decide +kernel
theorem envelope_exact_657_i1 : envelope_657_i1 =
    insert (2, 4) (Finset.univ.biUnion childrenD_657_i1) := by
  exact envelope_eq_combination childrenD_657_i1 (2, 4) envelope_657_i1
    pivot_mem_657_i1 child_envelope_sub_657_i1 envelope_origin_657_i1
def checked_657_i1 : CheckedCard where
  required := required_657_i1
  envelope := envelope_657_i1
  height := height_657_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_657_i1
def height_657_i2 : ℕ := 9
def childrenH_657_i2 : Fin 3 → ℕ := ![height_54, height_71, height_345]
theorem height_exact_657_i2 : height_657_i2 = 1 + Finset.univ.sup childrenH_657_i2 := by decide +kernel
theorem required_origin_657_i2 : ∀ x ∈ required_657_i2,
    (∃ j, x ∈ childrenC_657_i2 j) ∨ ∀ j, x ∈ childrenD_657_i2 j := by decide +kernel
theorem required_exact_657_i2 : required_657_i2 =
    ((Finset.univ.biUnion childrenC_657_i2) ∪ commonEnvelope childrenD_657_i2).erase (4, 2) := by
  exact required_eq_combination childrenC_657_i2 childrenD_657_i2 (4, 2) required_657_i2
    (by decide +kernel) child_required_sub_657_i2 common_sub_657_i2 required_origin_657_i2
theorem envelope_origin_657_i2 : ∀ x ∈ envelope_657_i2,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_657_i2 j := by decide +kernel
theorem envelope_exact_657_i2 : envelope_657_i2 =
    insert (4, 2) (Finset.univ.biUnion childrenD_657_i2) := by
  exact envelope_eq_combination childrenD_657_i2 (4, 2) envelope_657_i2
    pivot_mem_657_i2 child_envelope_sub_657_i2 envelope_origin_657_i2
def checked_657_i2 : CheckedCard where
  required := required_657_i2
  envelope := envelope_657_i2
  height := height_657_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_657_i2
def height_657_i6 : ℕ := 6
def childrenH_657_i6 : Fin 2 → ℕ := ![height_5, height_445]
theorem height_exact_657_i6 : height_657_i6 = 1 + Finset.univ.sup childrenH_657_i6 := by decide +kernel
theorem required_origin_657_i6 : ∀ x ∈ required_657_i6,
    (∃ j, x ∈ childrenC_657_i6 j) ∨ ∀ j, x ∈ childrenD_657_i6 j := by decide +kernel
theorem required_exact_657_i6 : required_657_i6 =
    ((Finset.univ.biUnion childrenC_657_i6) ∪ commonEnvelope childrenD_657_i6).erase (6, 3) := by
  exact required_eq_combination childrenC_657_i6 childrenD_657_i6 (6, 3) required_657_i6
    (by decide +kernel) child_required_sub_657_i6 common_sub_657_i6 required_origin_657_i6
theorem envelope_origin_657_i6 : ∀ x ∈ envelope_657_i6,
    x = (6, 3) ∨ ∃ j, x ∈ childrenD_657_i6 j := by decide +kernel
theorem envelope_exact_657_i6 : envelope_657_i6 =
    insert (6, 3) (Finset.univ.biUnion childrenD_657_i6) := by
  exact envelope_eq_combination childrenD_657_i6 (6, 3) envelope_657_i6
    pivot_mem_657_i6 child_envelope_sub_657_i6 envelope_origin_657_i6
def checked_657_i6 : CheckedCard where
  required := required_657_i6
  envelope := envelope_657_i6
  height := height_657_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_657_i6
def height_657_i5 : ℕ := 7
def childrenH_657_i5 : Fin 3 → ℕ := ![height_20, height_29, height_657_i6]
theorem height_exact_657_i5 : height_657_i5 = 1 + Finset.univ.sup childrenH_657_i5 := by decide +kernel
theorem required_origin_657_i5 : ∀ x ∈ required_657_i5,
    (∃ j, x ∈ childrenC_657_i5 j) ∨ ∀ j, x ∈ childrenD_657_i5 j := by decide +kernel
theorem required_exact_657_i5 : required_657_i5 =
    ((Finset.univ.biUnion childrenC_657_i5) ∪ commonEnvelope childrenD_657_i5).erase (6, 4) := by
  exact required_eq_combination childrenC_657_i5 childrenD_657_i5 (6, 4) required_657_i5
    (by decide +kernel) child_required_sub_657_i5 common_sub_657_i5 required_origin_657_i5
theorem envelope_origin_657_i5 : ∀ x ∈ envelope_657_i5,
    x = (6, 4) ∨ ∃ j, x ∈ childrenD_657_i5 j := by decide +kernel
theorem envelope_exact_657_i5 : envelope_657_i5 =
    insert (6, 4) (Finset.univ.biUnion childrenD_657_i5) := by
  exact envelope_eq_combination childrenD_657_i5 (6, 4) envelope_657_i5
    pivot_mem_657_i5 child_envelope_sub_657_i5 envelope_origin_657_i5
def checked_657_i5 : CheckedCard where
  required := required_657_i5
  envelope := envelope_657_i5
  height := height_657_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_657_i5
def height_657_i4 : ℕ := 8
def childrenH_657_i4 : Fin 3 → ℕ := ![height_15, height_65, height_657_i5]
theorem height_exact_657_i4 : height_657_i4 = 1 + Finset.univ.sup childrenH_657_i4 := by decide +kernel
theorem required_origin_657_i4 : ∀ x ∈ required_657_i4,
    (∃ j, x ∈ childrenC_657_i4 j) ∨ ∀ j, x ∈ childrenD_657_i4 j := by decide +kernel
theorem required_exact_657_i4 : required_657_i4 =
    ((Finset.univ.biUnion childrenC_657_i4) ∪ commonEnvelope childrenD_657_i4).erase (3, 4) := by
  exact required_eq_combination childrenC_657_i4 childrenD_657_i4 (3, 4) required_657_i4
    (by decide +kernel) child_required_sub_657_i4 common_sub_657_i4 required_origin_657_i4
theorem envelope_origin_657_i4 : ∀ x ∈ envelope_657_i4,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_657_i4 j := by decide +kernel
theorem envelope_exact_657_i4 : envelope_657_i4 =
    insert (3, 4) (Finset.univ.biUnion childrenD_657_i4) := by
  exact envelope_eq_combination childrenD_657_i4 (3, 4) envelope_657_i4
    pivot_mem_657_i4 child_envelope_sub_657_i4 envelope_origin_657_i4
def checked_657_i4 : CheckedCard where
  required := required_657_i4
  envelope := envelope_657_i4
  height := height_657_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_657_i4
def height_657_i3 : ℕ := 11
def childrenH_657_i3 : Fin 5 → ℕ := ![height_85, height_85, height_411, height_537, height_657_i4]
theorem height_exact_657_i3 : height_657_i3 = 1 + Finset.univ.sup childrenH_657_i3 := by decide +kernel
theorem required_origin_657_i3 : ∀ x ∈ required_657_i3,
    (∃ j, x ∈ childrenC_657_i3 j) ∨ ∀ j, x ∈ childrenD_657_i3 j := by decide +kernel
theorem required_exact_657_i3 : required_657_i3 =
    ((Finset.univ.biUnion childrenC_657_i3) ∪ commonEnvelope childrenD_657_i3).erase (5, 4) := by
  exact required_eq_combination childrenC_657_i3 childrenD_657_i3 (5, 4) required_657_i3
    (by decide +kernel) child_required_sub_657_i3 common_sub_657_i3 required_origin_657_i3
theorem envelope_origin_657_i3 : ∀ x ∈ envelope_657_i3,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_657_i3 j := by decide +kernel
theorem envelope_exact_657_i3 : envelope_657_i3 =
    insert (5, 4) (Finset.univ.biUnion childrenD_657_i3) := by
  exact envelope_eq_combination childrenD_657_i3 (5, 4) envelope_657_i3
    pivot_mem_657_i3 child_envelope_sub_657_i3 envelope_origin_657_i3
def checked_657_i3 : CheckedCard where
  required := required_657_i3
  envelope := envelope_657_i3
  height := height_657_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_657_i3
def height_657_i0 : ℕ := 12
def childrenH_657_i0 : Fin 6 → ℕ := ![height_510, height_631, height_653, height_657_i1, height_657_i2, height_657_i3]
theorem height_exact_657_i0 : height_657_i0 = 1 + Finset.univ.sup childrenH_657_i0 := by decide +kernel
theorem required_origin_657_i0 : ∀ x ∈ required_657_i0,
    (∃ j, x ∈ childrenC_657_i0 j) ∨ ∀ j, x ∈ childrenD_657_i0 j := by decide +kernel
theorem required_exact_657_i0 : required_657_i0 =
    ((Finset.univ.biUnion childrenC_657_i0) ∪ commonEnvelope childrenD_657_i0).erase (4, 4) := by
  exact required_eq_combination childrenC_657_i0 childrenD_657_i0 (4, 4) required_657_i0
    (by decide +kernel) child_required_sub_657_i0 common_sub_657_i0 required_origin_657_i0
theorem envelope_origin_657_i0 : ∀ x ∈ envelope_657_i0,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_657_i0 j := by decide +kernel
theorem envelope_exact_657_i0 : envelope_657_i0 =
    insert (4, 4) (Finset.univ.biUnion childrenD_657_i0) := by
  exact envelope_eq_combination childrenD_657_i0 (4, 4) envelope_657_i0
    pivot_mem_657_i0 child_envelope_sub_657_i0 envelope_origin_657_i0
def checked_657_i0 : CheckedCard where
  required := required_657_i0
  envelope := envelope_657_i0
  height := height_657_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_657_i0
def height_657 : ℕ := 13
def childrenH_657 : Fin 5 → ℕ := ![height_50, height_125, height_478, height_482, height_657_i0]
theorem height_exact_657 : height_657 = 1 + Finset.univ.sup childrenH_657 := by decide +kernel
theorem required_origin_657 : ∀ x ∈ required_657,
    (∃ j, x ∈ childrenC_657 j) ∨ ∀ j, x ∈ childrenD_657 j := by decide +kernel
theorem required_exact_657 : required_657 =
    ((Finset.univ.biUnion childrenC_657) ∪ commonEnvelope childrenD_657).erase (4, 3) := by
  exact required_eq_combination childrenC_657 childrenD_657 (4, 3) required_657
    (by decide +kernel) child_required_sub_657 common_sub_657 required_origin_657
theorem envelope_origin_657 : ∀ x ∈ envelope_657,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_657 j := by decide +kernel
theorem envelope_exact_657 : envelope_657 =
    insert (4, 3) (Finset.univ.biUnion childrenD_657) := by
  exact envelope_eq_combination childrenD_657 (4, 3) envelope_657
    pivot_mem_657 child_envelope_sub_657 envelope_origin_657
def checked_657 : CheckedCard where
  required := required_657
  envelope := envelope_657
  height := height_657
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_657
def height_665_i0 : ℕ := 10
def childrenH_665_i0 : Fin 4 → ℕ := ![height_70, height_106, height_269, height_322]
theorem height_exact_665_i0 : height_665_i0 = 1 + Finset.univ.sup childrenH_665_i0 := by decide +kernel
theorem required_origin_665_i0 : ∀ x ∈ required_665_i0,
    (∃ j, x ∈ childrenC_665_i0 j) ∨ ∀ j, x ∈ childrenD_665_i0 j := by decide +kernel
theorem required_exact_665_i0 : required_665_i0 =
    ((Finset.univ.biUnion childrenC_665_i0) ∪ commonEnvelope childrenD_665_i0).erase (4, 7) := by
  exact required_eq_combination childrenC_665_i0 childrenD_665_i0 (4, 7) required_665_i0
    (by decide +kernel) child_required_sub_665_i0 common_sub_665_i0 required_origin_665_i0
theorem envelope_origin_665_i0 : ∀ x ∈ envelope_665_i0,
    x = (4, 7) ∨ ∃ j, x ∈ childrenD_665_i0 j := by decide +kernel
theorem envelope_exact_665_i0 : envelope_665_i0 =
    insert (4, 7) (Finset.univ.biUnion childrenD_665_i0) := by
  exact envelope_eq_combination childrenD_665_i0 (4, 7) envelope_665_i0
    pivot_mem_665_i0 child_envelope_sub_665_i0 envelope_origin_665_i0
def checked_665_i0 : CheckedCard where
  required := required_665_i0
  envelope := envelope_665_i0
  height := height_665_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_665_i0
def height_665_i1 : ℕ := 9
def childrenH_665_i1 : Fin 3 → ℕ := ![height_70, height_257, height_435]
theorem height_exact_665_i1 : height_665_i1 = 1 + Finset.univ.sup childrenH_665_i1 := by decide +kernel
theorem required_origin_665_i1 : ∀ x ∈ required_665_i1,
    (∃ j, x ∈ childrenC_665_i1 j) ∨ ∀ j, x ∈ childrenD_665_i1 j := by decide +kernel
theorem required_exact_665_i1 : required_665_i1 =
    ((Finset.univ.biUnion childrenC_665_i1) ∪ commonEnvelope childrenD_665_i1).erase (4, 7) := by
  exact required_eq_combination childrenC_665_i1 childrenD_665_i1 (4, 7) required_665_i1
    (by decide +kernel) child_required_sub_665_i1 common_sub_665_i1 required_origin_665_i1
theorem envelope_origin_665_i1 : ∀ x ∈ envelope_665_i1,
    x = (4, 7) ∨ ∃ j, x ∈ childrenD_665_i1 j := by decide +kernel
theorem envelope_exact_665_i1 : envelope_665_i1 =
    insert (4, 7) (Finset.univ.biUnion childrenD_665_i1) := by
  exact envelope_eq_combination childrenD_665_i1 (4, 7) envelope_665_i1
    pivot_mem_665_i1 child_envelope_sub_665_i1 envelope_origin_665_i1
def checked_665_i1 : CheckedCard where
  required := required_665_i1
  envelope := envelope_665_i1
  height := height_665_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_665_i1
def height_665_i4 : ℕ := 5
def childrenH_665_i4 : Fin 2 → ℕ := ![height_4, height_93]
theorem height_exact_665_i4 : height_665_i4 = 1 + Finset.univ.sup childrenH_665_i4 := by decide +kernel
theorem required_origin_665_i4 : ∀ x ∈ required_665_i4,
    (∃ j, x ∈ childrenC_665_i4 j) ∨ ∀ j, x ∈ childrenD_665_i4 j := by decide +kernel
theorem required_exact_665_i4 : required_665_i4 =
    ((Finset.univ.biUnion childrenC_665_i4) ∪ commonEnvelope childrenD_665_i4).erase (3, 7) := by
  exact required_eq_combination childrenC_665_i4 childrenD_665_i4 (3, 7) required_665_i4
    (by decide +kernel) child_required_sub_665_i4 common_sub_665_i4 required_origin_665_i4
theorem envelope_origin_665_i4 : ∀ x ∈ envelope_665_i4,
    x = (3, 7) ∨ ∃ j, x ∈ childrenD_665_i4 j := by decide +kernel
theorem envelope_exact_665_i4 : envelope_665_i4 =
    insert (3, 7) (Finset.univ.biUnion childrenD_665_i4) := by
  exact envelope_eq_combination childrenD_665_i4 (3, 7) envelope_665_i4
    pivot_mem_665_i4 child_envelope_sub_665_i4 envelope_origin_665_i4
def checked_665_i4 : CheckedCard where
  required := required_665_i4
  envelope := envelope_665_i4
  height := height_665_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_665_i4
def height_665_i3 : ℕ := 6
def childrenH_665_i3 : Fin 2 → ℕ := ![height_5, height_665_i4]
theorem height_exact_665_i3 : height_665_i3 = 1 + Finset.univ.sup childrenH_665_i3 := by decide +kernel
theorem required_origin_665_i3 : ∀ x ∈ required_665_i3,
    (∃ j, x ∈ childrenC_665_i3 j) ∨ ∀ j, x ∈ childrenD_665_i3 j := by decide +kernel
theorem required_exact_665_i3 : required_665_i3 =
    ((Finset.univ.biUnion childrenC_665_i3) ∪ commonEnvelope childrenD_665_i3).erase (3, 4) := by
  exact required_eq_combination childrenC_665_i3 childrenD_665_i3 (3, 4) required_665_i3
    (by decide +kernel) child_required_sub_665_i3 common_sub_665_i3 required_origin_665_i3
theorem envelope_origin_665_i3 : ∀ x ∈ envelope_665_i3,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_665_i3 j := by decide +kernel
theorem envelope_exact_665_i3 : envelope_665_i3 =
    insert (3, 4) (Finset.univ.biUnion childrenD_665_i3) := by
  exact envelope_eq_combination childrenD_665_i3 (3, 4) envelope_665_i3
    pivot_mem_665_i3 child_envelope_sub_665_i3 envelope_origin_665_i3
def checked_665_i3 : CheckedCard where
  required := required_665_i3
  envelope := envelope_665_i3
  height := height_665_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_665_i3
def height_665_i2 : ℕ := 12
def childrenH_665_i2 : Fin 3 → ℕ := ![height_40, height_517, height_665_i3]
theorem height_exact_665_i2 : height_665_i2 = 1 + Finset.univ.sup childrenH_665_i2 := by decide +kernel
theorem required_origin_665_i2 : ∀ x ∈ required_665_i2,
    (∃ j, x ∈ childrenC_665_i2 j) ∨ ∀ j, x ∈ childrenD_665_i2 j := by decide +kernel
theorem required_exact_665_i2 : required_665_i2 =
    ((Finset.univ.biUnion childrenC_665_i2) ∪ commonEnvelope childrenD_665_i2).erase (3, 5) := by
  exact required_eq_combination childrenC_665_i2 childrenD_665_i2 (3, 5) required_665_i2
    (by decide +kernel) child_required_sub_665_i2 common_sub_665_i2 required_origin_665_i2
theorem envelope_origin_665_i2 : ∀ x ∈ envelope_665_i2,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_665_i2 j := by decide +kernel
theorem envelope_exact_665_i2 : envelope_665_i2 =
    insert (3, 5) (Finset.univ.biUnion childrenD_665_i2) := by
  exact envelope_eq_combination childrenD_665_i2 (3, 5) envelope_665_i2
    pivot_mem_665_i2 child_envelope_sub_665_i2 envelope_origin_665_i2
def checked_665_i2 : CheckedCard where
  required := required_665_i2
  envelope := envelope_665_i2
  height := height_665_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_665_i2
def height_665 : ℕ := 13
def childrenH_665 : Fin 5 → ℕ := ![height_459, height_588, height_665_i0, height_665_i1, height_665_i2]
theorem height_exact_665 : height_665 = 1 + Finset.univ.sup childrenH_665 := by decide +kernel
theorem required_origin_665 : ∀ x ∈ required_665,
    (∃ j, x ∈ childrenC_665 j) ∨ ∀ j, x ∈ childrenD_665 j := by decide +kernel
theorem required_exact_665 : required_665 =
    ((Finset.univ.biUnion childrenC_665) ∪ commonEnvelope childrenD_665).erase (4, 5) := by
  exact required_eq_combination childrenC_665 childrenD_665 (4, 5) required_665
    (by decide +kernel) child_required_sub_665 common_sub_665 required_origin_665
theorem envelope_origin_665 : ∀ x ∈ envelope_665,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_665 j := by decide +kernel
theorem envelope_exact_665 : envelope_665 =
    insert (4, 5) (Finset.univ.biUnion childrenD_665) := by
  exact envelope_eq_combination childrenD_665 (4, 5) envelope_665
    pivot_mem_665 child_envelope_sub_665 envelope_origin_665
def checked_665 : CheckedCard where
  required := required_665
  envelope := envelope_665
  height := height_665
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_665
end SnakyPrototype.Certificate21

end OAI
