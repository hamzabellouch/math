import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
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
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part07
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part05
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_645_i0 : Finset Cell := ⟨(([(4, 4), (4, 5), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_645_i0 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 3), (4, 4), (4, 5), (4, 6), (5, 3), (5, 4), (5, 5), (6, 4), (6, 5), (7, 4), (7, 5), (8, 4), (8, 5), (9, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_645_i0 : Fin 4 → Finset Cell := ![(placed21 5 (7, 4) required_44), (placed21 5 (7, 4) required_52), (placed21 3 (2, 5) required_128), (placed21 6 (6, 6) required_144)]
def childrenD_645_i0 : Fin 4 → Finset Cell := ![(placed21 5 (7, 4) envelope_44), (placed21 5 (7, 4) envelope_52), (placed21 3 (2, 5) envelope_128), (placed21 6 (6, 6) envelope_144)]
theorem common_sub_645_i0 : commonEnvelope childrenD_645_i0 ⊆ insert (5, 4) required_645_i0 := by decide +kernel
theorem child_required_sub_645_i0 : ∀ j, childrenC_645_i0 j ⊆ insert (5, 4) required_645_i0 := by decide +kernel
theorem child_envelope_sub_645_i0 : ∀ j, childrenD_645_i0 j ⊆ envelope_645_i0 := by decide +kernel
theorem pivot_mem_645_i0 : (5, 4) ∈ envelope_645_i0 := by decide +kernel
theorem children_work_645_i0 : ∀ j, Template HasSnaky 5 (childrenC_645_i0 j) (childrenD_645_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 5 (7, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 5 (7, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_128 3 (2, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_144 6 (6, 6)).mono (by decide +kernel)
theorem row_works_645_i0 : Template HasSnaky 6 required_645_i0 envelope_645_i0 := by
  refine compose HasSnaky 5 childrenC_645_i0 childrenD_645_i0 children_work_645_i0 (5, 4)
    required_645_i0 envelope_645_i0 pivot_mem_645_i0 child_required_sub_645_i0 child_envelope_sub_645_i0 ?_
  intro b hb
  exact common_sub_645_i0 (mem_commonEnvelope childrenD_645_i0 b hb)
def required_645_i1 : Finset Cell := ⟨(([(4, 4), (4, 5), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_645_i1 : Finset Cell := ⟨(([(1, 4), (1, 6), (2, 4), (2, 5), (2, 6), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 2), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, 2), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_645_i1 : Fin 6 → Finset Cell := ![(placed21 1 (1, 4) required_104), (placed21 1 (1, 4) required_359), (placed21 4 (1, 8) required_438), (placed21 0 (1, 1) required_452), (placed21 4 (3, 8) required_476), (placed21 0 (3, 1) required_479)]
def childrenD_645_i1 : Fin 6 → Finset Cell := ![(placed21 1 (1, 4) envelope_104), (placed21 1 (1, 4) envelope_359), (placed21 4 (1, 8) envelope_438), (placed21 0 (1, 1) envelope_452), (placed21 4 (3, 8) envelope_476), (placed21 0 (3, 1) envelope_479)]
theorem common_sub_645_i1 : commonEnvelope childrenD_645_i1 ⊆ insert (6, 5) required_645_i1 := by decide +kernel
theorem child_required_sub_645_i1 : ∀ j, childrenC_645_i1 j ⊆ insert (6, 5) required_645_i1 := by decide +kernel
theorem child_envelope_sub_645_i1 : ∀ j, childrenD_645_i1 j ⊆ envelope_645_i1 := by decide +kernel
theorem pivot_mem_645_i1 : (6, 5) ∈ envelope_645_i1 := by decide +kernel
theorem children_work_645_i1 : ∀ j, Template HasSnaky 10 (childrenC_645_i1 j) (childrenD_645_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_104 1 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_359 1 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_438 4 (1, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_452 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_476 4 (3, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_479 0 (3, 1)).mono (by decide +kernel)
theorem row_works_645_i1 : Template HasSnaky 11 required_645_i1 envelope_645_i1 := by
  refine compose HasSnaky 10 childrenC_645_i1 childrenD_645_i1 children_work_645_i1 (6, 5)
    required_645_i1 envelope_645_i1 pivot_mem_645_i1 child_required_sub_645_i1 child_envelope_sub_645_i1 ?_
  intro b hb
  exact common_sub_645_i1 (mem_commonEnvelope childrenD_645_i1 b hb)
def required_645 : Finset Cell := ⟨(([(4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_645 : Finset Cell := ⟨(([(0, 5), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (10, 3), (10, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_645 : Fin 10 → Finset Cell := ![(placed21 6 (7, 7) required_120), (placed21 3 (1, 6) required_276), (placed21 3 (1, 6) required_338), (placed21 3 (1, 7) required_437), (placed21 3 (0, 6) required_611), (placed21 0 (1, 0) required_634), (placed21 0 (3, 0) required_642), (placed21 0 (3, 0) required_643), required_645_i0, required_645_i1]
def childrenD_645 : Fin 10 → Finset Cell := ![(placed21 6 (7, 7) envelope_120), (placed21 3 (1, 6) envelope_276), (placed21 3 (1, 6) envelope_338), (placed21 3 (1, 7) envelope_437), (placed21 3 (0, 6) envelope_611), (placed21 0 (1, 0) envelope_634), (placed21 0 (3, 0) envelope_642), (placed21 0 (3, 0) envelope_643), envelope_645_i0, envelope_645_i1]
theorem common_sub_645 : commonEnvelope childrenD_645 ⊆ insert (6, 4) required_645 := by decide +kernel
theorem child_required_sub_645 : ∀ j, childrenC_645 j ⊆ insert (6, 4) required_645 := by decide +kernel
theorem child_envelope_sub_645 : ∀ j, childrenD_645 j ⊆ envelope_645 := by decide +kernel
theorem pivot_mem_645 : (6, 4) ∈ envelope_645 := by decide +kernel
theorem children_work_645 : ∀ j, Template HasSnaky 13 (childrenC_645 j) (childrenD_645 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_120 6 (7, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_276 3 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_338 3 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_437 3 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_611 3 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_634 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_642 0 (3, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_643 0 (3, 0)).mono (by decide +kernel)
  · exact row_works_645_i0.mono (by decide +kernel)
  · exact row_works_645_i1.mono (by decide +kernel)
theorem row_works_645 : Template HasSnaky 14 required_645 envelope_645 := by
  refine compose HasSnaky 13 childrenC_645 childrenD_645 children_work_645 (6, 4)
    required_645 envelope_645 pivot_mem_645 child_required_sub_645 child_envelope_sub_645 ?_
  intro b hb
  exact common_sub_645 (mem_commonEnvelope childrenD_645 b hb)
def required_669_i5 : Finset Cell := ⟨(([(3, 5), (4, 5), (4, 6), (5, 7), (6, 5), (6, 6), (6, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_669_i5 : Finset Cell := ⟨(([(2, 6), (3, 5), (3, 6), (4, 5), (4, 6), (5, 6), (5, 7), (6, 5), (6, 6), (6, 7), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_669_i5 : Fin 2 → Finset Cell := ![(placed21 6 (7, 6) required_0), (placed21 7 (7, 7) required_66)]
def childrenD_669_i5 : Fin 2 → Finset Cell := ![(placed21 6 (7, 6) envelope_0), (placed21 7 (7, 7) envelope_66)]
theorem common_sub_669_i5 : commonEnvelope childrenD_669_i5 ⊆ insert (5, 6) required_669_i5 := by decide +kernel
theorem child_required_sub_669_i5 : ∀ j, childrenC_669_i5 j ⊆ insert (5, 6) required_669_i5 := by decide +kernel
theorem child_envelope_sub_669_i5 : ∀ j, childrenD_669_i5 j ⊆ envelope_669_i5 := by decide +kernel
theorem pivot_mem_669_i5 : (5, 6) ∈ envelope_669_i5 := by decide +kernel
theorem children_work_669_i5 : ∀ j, Template HasSnaky 2 (childrenC_669_i5 j) (childrenD_669_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (7, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_66 7 (7, 7)).mono (by decide +kernel)
theorem row_works_669_i5 : Template HasSnaky 3 required_669_i5 envelope_669_i5 := by
  refine compose HasSnaky 2 childrenC_669_i5 childrenD_669_i5 children_work_669_i5 (5, 6)
    required_669_i5 envelope_669_i5 pivot_mem_669_i5 child_required_sub_669_i5 child_envelope_sub_669_i5 ?_
  intro b hb
  exact common_sub_669_i5 (mem_commonEnvelope childrenD_669_i5 b hb)
def required_669_i4 : Finset Cell := ⟨(([(3, 4), (3, 5), (4, 5), (4, 7), (5, 7), (6, 5), (6, 6), (6, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_669_i4 : Finset Cell := ⟨(([(2, 6), (3, 4), (3, 5), (3, 6), (4, 5), (4, 6), (4, 7), (4, 8), (5, 6), (5, 7), (6, 5), (6, 6), (6, 7), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_669_i4 : Fin 2 → Finset Cell := ![(placed21 7 (4, 8) required_0), required_669_i5]
def childrenD_669_i4 : Fin 2 → Finset Cell := ![(placed21 7 (4, 8) envelope_0), envelope_669_i5]
theorem common_sub_669_i4 : commonEnvelope childrenD_669_i4 ⊆ insert (4, 6) required_669_i4 := by decide +kernel
theorem child_required_sub_669_i4 : ∀ j, childrenC_669_i4 j ⊆ insert (4, 6) required_669_i4 := by decide +kernel
theorem child_envelope_sub_669_i4 : ∀ j, childrenD_669_i4 j ⊆ envelope_669_i4 := by decide +kernel
theorem pivot_mem_669_i4 : (4, 6) ∈ envelope_669_i4 := by decide +kernel
theorem children_work_669_i4 : ∀ j, Template HasSnaky 3 (childrenC_669_i4 j) (childrenD_669_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (4, 8)).mono (by decide +kernel)
  · exact row_works_669_i5.mono (by decide +kernel)
theorem row_works_669_i4 : Template HasSnaky 4 required_669_i4 envelope_669_i4 := by
  refine compose HasSnaky 3 childrenC_669_i4 childrenD_669_i4 children_work_669_i4 (4, 6)
    required_669_i4 envelope_669_i4 pivot_mem_669_i4 child_required_sub_669_i4 child_envelope_sub_669_i4 ?_
  intro b hb
  exact common_sub_669_i4 (mem_commonEnvelope childrenD_669_i4 b hb)
def required_669_i6 : Finset Cell := ⟨(([(3, 4), (3, 5), (4, 5), (4, 7), (5, 7), (6, 6), (6, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_669_i6 : Finset Cell := ⟨(([(3, 4), (3, 5), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (4, 8), (5, 7), (6, 6), (6, 7), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_669_i6 : Fin 2 → Finset Cell := ![(placed21 4 (3, 7) required_5), (placed21 0 (3, 4) required_36)]
def childrenD_669_i6 : Fin 2 → Finset Cell := ![(placed21 4 (3, 7) envelope_5), (placed21 0 (3, 4) envelope_36)]
theorem common_sub_669_i6 : commonEnvelope childrenD_669_i6 ⊆ insert (3, 7) required_669_i6 := by decide +kernel
theorem child_required_sub_669_i6 : ∀ j, childrenC_669_i6 j ⊆ insert (3, 7) required_669_i6 := by decide +kernel
theorem child_envelope_sub_669_i6 : ∀ j, childrenD_669_i6 j ⊆ envelope_669_i6 := by decide +kernel
theorem pivot_mem_669_i6 : (3, 7) ∈ envelope_669_i6 := by decide +kernel
theorem children_work_669_i6 : ∀ j, Template HasSnaky 2 (childrenC_669_i6 j) (childrenD_669_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_36 0 (3, 4)).mono (by decide +kernel)
theorem row_works_669_i6 : Template HasSnaky 3 required_669_i6 envelope_669_i6 := by
  refine compose HasSnaky 2 childrenC_669_i6 childrenD_669_i6 children_work_669_i6 (3, 7)
    required_669_i6 envelope_669_i6 pivot_mem_669_i6 child_required_sub_669_i6 child_envelope_sub_669_i6 ?_
  intro b hb
  exact common_sub_669_i6 (mem_commonEnvelope childrenD_669_i6 b hb)
def required_669_i7 : Finset Cell := ⟨(([(3, 4), (3, 5), (4, 5), (4, 7), (5, 7), (6, 6), (6, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_669_i7 : Finset Cell := ⟨(([(1, 8), (2, 7), (2, 8), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 5), (4, 6), (4, 7), (4, 8), (5, 6), (5, 7), (6, 6), (6, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_669_i7 : Fin 2 → Finset Cell := ![(placed21 2 (6, 6) required_24), (placed21 0 (3, 4) required_36)]
def childrenD_669_i7 : Fin 2 → Finset Cell := ![(placed21 2 (6, 6) envelope_24), (placed21 0 (3, 4) envelope_36)]
theorem common_sub_669_i7 : commonEnvelope childrenD_669_i7 ⊆ insert (3, 7) required_669_i7 := by decide +kernel
theorem child_required_sub_669_i7 : ∀ j, childrenC_669_i7 j ⊆ insert (3, 7) required_669_i7 := by decide +kernel
theorem child_envelope_sub_669_i7 : ∀ j, childrenD_669_i7 j ⊆ envelope_669_i7 := by decide +kernel
theorem pivot_mem_669_i7 : (3, 7) ∈ envelope_669_i7 := by decide +kernel
theorem children_work_669_i7 : ∀ j, Template HasSnaky 3 (childrenC_669_i7 j) (childrenD_669_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_24 2 (6, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_36 0 (3, 4)).mono (by decide +kernel)
theorem row_works_669_i7 : Template HasSnaky 4 required_669_i7 envelope_669_i7 := by
  refine compose HasSnaky 3 childrenC_669_i7 childrenD_669_i7 children_work_669_i7 (3, 7)
    required_669_i7 envelope_669_i7 pivot_mem_669_i7 child_required_sub_669_i7 child_envelope_sub_669_i7 ?_
  intro b hb
  exact common_sub_669_i7 (mem_commonEnvelope childrenD_669_i7 b hb)
def required_669_i3 : Finset Cell := ⟨(([(3, 4), (3, 5), (4, 5), (5, 7), (6, 5), (6, 6), (6, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_669_i3 : Finset Cell := ⟨(([(1, 8), (2, 6), (2, 7), (2, 8), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 5), (4, 6), (4, 7), (4, 8), (5, 6), (5, 7), (6, 5), (6, 6), (6, 7), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_669_i3 : Fin 4 → Finset Cell := ![(placed21 5 (7, 6) required_48), required_669_i4, required_669_i6, required_669_i7]
def childrenD_669_i3 : Fin 4 → Finset Cell := ![(placed21 5 (7, 6) envelope_48), envelope_669_i4, envelope_669_i6, envelope_669_i7]
theorem common_sub_669_i3 : commonEnvelope childrenD_669_i3 ⊆ insert (4, 7) required_669_i3 := by decide +kernel
theorem child_required_sub_669_i3 : ∀ j, childrenC_669_i3 j ⊆ insert (4, 7) required_669_i3 := by decide +kernel
theorem child_envelope_sub_669_i3 : ∀ j, childrenD_669_i3 j ⊆ envelope_669_i3 := by decide +kernel
theorem pivot_mem_669_i3 : (4, 7) ∈ envelope_669_i3 := by decide +kernel
theorem children_work_669_i3 : ∀ j, Template HasSnaky 4 (childrenC_669_i3 j) (childrenD_669_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_48 5 (7, 6)).mono (by decide +kernel)
  · exact row_works_669_i4.mono (by decide +kernel)
  · exact row_works_669_i6.mono (by decide +kernel)
  · exact row_works_669_i7.mono (by decide +kernel)
theorem row_works_669_i3 : Template HasSnaky 5 required_669_i3 envelope_669_i3 := by
  refine compose HasSnaky 4 childrenC_669_i3 childrenD_669_i3 children_work_669_i3 (4, 7)
    required_669_i3 envelope_669_i3 pivot_mem_669_i3 child_required_sub_669_i3 child_envelope_sub_669_i3 ?_
  intro b hb
  exact common_sub_669_i3 (mem_commonEnvelope childrenD_669_i3 b hb)
def required_669_i2 : Finset Cell := ⟨(([(3, 4), (3, 5), (4, 5), (6, 4), (6, 5), (6, 6), (6, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_669_i2 : Finset Cell := ⟨(([(1, 8), (2, 6), (2, 7), (2, 8), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 5), (4, 6), (4, 7), (4, 8), (5, 6), (5, 7), (5, 8), (6, 4), (6, 5), (6, 6), (6, 7), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_669_i2 : Fin 2 → Finset Cell := ![(placed21 5 (6, 4) required_5), required_669_i3]
def childrenD_669_i2 : Fin 2 → Finset Cell := ![(placed21 5 (6, 4) envelope_5), envelope_669_i3]
theorem common_sub_669_i2 : commonEnvelope childrenD_669_i2 ⊆ insert (5, 7) required_669_i2 := by decide +kernel
theorem child_required_sub_669_i2 : ∀ j, childrenC_669_i2 j ⊆ insert (5, 7) required_669_i2 := by decide +kernel
theorem child_envelope_sub_669_i2 : ∀ j, childrenD_669_i2 j ⊆ envelope_669_i2 := by decide +kernel
theorem pivot_mem_669_i2 : (5, 7) ∈ envelope_669_i2 := by decide +kernel
theorem children_work_669_i2 : ∀ j, Template HasSnaky 5 (childrenC_669_i2 j) (childrenD_669_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (6, 4)).mono (by decide +kernel)
  · exact row_works_669_i3.mono (by decide +kernel)
theorem row_works_669_i2 : Template HasSnaky 6 required_669_i2 envelope_669_i2 := by
  refine compose HasSnaky 5 childrenC_669_i2 childrenD_669_i2 children_work_669_i2 (5, 7)
    required_669_i2 envelope_669_i2 pivot_mem_669_i2 child_required_sub_669_i2 child_envelope_sub_669_i2 ?_
  intro b hb
  exact common_sub_669_i2 (mem_commonEnvelope childrenD_669_i2 b hb)
def required_669_i1 : Finset Cell := ⟨(([(3, 4), (3, 5), (6, 4), (6, 5), (6, 6), (6, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_669_i1 : Finset Cell := ⟨(([(1, 8), (2, 6), (2, 7), (2, 8), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 5), (4, 6), (4, 7), (4, 8), (5, 5), (5, 6), (5, 7), (5, 8), (6, 4), (6, 5), (6, 6), (6, 7), (7, 3), (7, 4), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_669_i1 : Fin 2 → Finset Cell := ![(placed21 7 (7, 7) required_25), required_669_i2]
def childrenD_669_i1 : Fin 2 → Finset Cell := ![(placed21 7 (7, 7) envelope_25), envelope_669_i2]
theorem common_sub_669_i1 : commonEnvelope childrenD_669_i1 ⊆ insert (4, 5) required_669_i1 := by decide +kernel
theorem child_required_sub_669_i1 : ∀ j, childrenC_669_i1 j ⊆ insert (4, 5) required_669_i1 := by decide +kernel
theorem child_envelope_sub_669_i1 : ∀ j, childrenD_669_i1 j ⊆ envelope_669_i1 := by decide +kernel
theorem pivot_mem_669_i1 : (4, 5) ∈ envelope_669_i1 := by decide +kernel
theorem children_work_669_i1 : ∀ j, Template HasSnaky 6 (childrenC_669_i1 j) (childrenD_669_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_25 7 (7, 7)).mono (by decide +kernel)
  · exact row_works_669_i2.mono (by decide +kernel)
theorem row_works_669_i1 : Template HasSnaky 7 required_669_i1 envelope_669_i1 := by
  refine compose HasSnaky 6 childrenC_669_i1 childrenD_669_i1 children_work_669_i1 (4, 5)
    required_669_i1 envelope_669_i1 pivot_mem_669_i1 child_required_sub_669_i1 child_envelope_sub_669_i1 ?_
  intro b hb
  exact common_sub_669_i1 (mem_commonEnvelope childrenD_669_i1 b hb)
def required_669_i0 : Finset Cell := ⟨(([(3, 4), (3, 5), (6, 4), (6, 5), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_669_i0 : Finset Cell := ⟨(([(1, 8), (2, 6), (2, 7), (2, 8), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 5), (4, 6), (4, 7), (4, 8), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 3), (7, 4), (7, 5), (7, 6), (7, 8), (7, 9), (7, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_669_i0 : Fin 4 → Finset Cell := ![(placed21 2 (7, 3) required_19), (placed21 1 (5, 4) required_197), (placed21 2 (7, 3) required_225), required_669_i1]
def childrenD_669_i0 : Fin 4 → Finset Cell := ![(placed21 2 (7, 3) envelope_19), (placed21 1 (5, 4) envelope_197), (placed21 2 (7, 3) envelope_225), envelope_669_i1]
theorem common_sub_669_i0 : commonEnvelope childrenD_669_i0 ⊆ insert (6, 7) required_669_i0 := by decide +kernel
theorem child_required_sub_669_i0 : ∀ j, childrenC_669_i0 j ⊆ insert (6, 7) required_669_i0 := by decide +kernel
theorem child_envelope_sub_669_i0 : ∀ j, childrenD_669_i0 j ⊆ envelope_669_i0 := by decide +kernel
theorem pivot_mem_669_i0 : (6, 7) ∈ envelope_669_i0 := by decide +kernel
theorem children_work_669_i0 : ∀ j, Template HasSnaky 7 (childrenC_669_i0 j) (childrenD_669_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_19 2 (7, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_197 1 (5, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_225 2 (7, 3)).mono (by decide +kernel)
  · exact row_works_669_i1.mono (by decide +kernel)
theorem row_works_669_i0 : Template HasSnaky 8 required_669_i0 envelope_669_i0 := by
  refine compose HasSnaky 7 childrenC_669_i0 childrenD_669_i0 children_work_669_i0 (6, 7)
    required_669_i0 envelope_669_i0 pivot_mem_669_i0 child_required_sub_669_i0 child_envelope_sub_669_i0 ?_
  intro b hb
  exact common_sub_669_i0 (mem_commonEnvelope childrenD_669_i0 b hb)
def required_669 : Finset Cell := ⟨(([(3, 4), (3, 5), (6, 5), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_669 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 3), (2, 4), (2, 6), (2, 7), (2, 8), (2, 9), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 8), (7, 9), (7, 10), (8, 2), (8, 3), (8, 4), (9, 2), (9, 3), (9, 4), (10, 2), (10, 3), (10, 4), (11, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_669 : Fin 4 → Finset Cell := ![(placed21 4 (4, 8) required_188), (placed21 2 (7, 3) required_590), (placed21 4 (3, 7) required_668), required_669_i0]
def childrenD_669 : Fin 4 → Finset Cell := ![(placed21 4 (4, 8) envelope_188), (placed21 2 (7, 3) envelope_590), (placed21 4 (3, 7) envelope_668), envelope_669_i0]
theorem common_sub_669 : commonEnvelope childrenD_669 ⊆ insert (6, 4) required_669 := by decide +kernel
theorem child_required_sub_669 : ∀ j, childrenC_669 j ⊆ insert (6, 4) required_669 := by decide +kernel
theorem child_envelope_sub_669 : ∀ j, childrenD_669 j ⊆ envelope_669 := by decide +kernel
theorem pivot_mem_669 : (6, 4) ∈ envelope_669 := by decide +kernel
theorem children_work_669 : ∀ j, Template HasSnaky 13 (childrenC_669 j) (childrenD_669 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_188 4 (4, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_590 2 (7, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_668 4 (3, 7)).mono (by decide +kernel)
  · exact row_works_669_i0.mono (by decide +kernel)
theorem row_works_669 : Template HasSnaky 14 required_669 envelope_669 := by
  refine compose HasSnaky 13 childrenC_669 childrenD_669 children_work_669 (6, 4)
    required_669 envelope_669 pivot_mem_669 child_required_sub_669 child_envelope_sub_669 ?_
  intro b hb
  exact common_sub_669 (mem_commonEnvelope childrenD_669 b hb)
def required_693_i1 : Finset Cell := ⟨(([(4, 5), (5, 5), (5, 7), (6, 5), (7, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_693_i1 : Finset Cell := ⟨(([(2, 7), (2, 9), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 4), (4, 5), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 4), (6, 5), (6, 7), (6, 8), (6, 9), (6, 10), (7, 8), (7, 9), (8, 8), (8, 9), (9, 8), (9, 9), (10, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_693_i1 : Fin 2 → Finset Cell := ![(placed21 0 (4, 4) required_28), (placed21 1 (2, 7) required_409)]
def childrenD_693_i1 : Fin 2 → Finset Cell := ![(placed21 0 (4, 4) envelope_28), (placed21 1 (2, 7) envelope_409)]
theorem common_sub_693_i1 : commonEnvelope childrenD_693_i1 ⊆ insert (5, 8) required_693_i1 := by decide +kernel
theorem child_required_sub_693_i1 : ∀ j, childrenC_693_i1 j ⊆ insert (5, 8) required_693_i1 := by decide +kernel
theorem child_envelope_sub_693_i1 : ∀ j, childrenD_693_i1 j ⊆ envelope_693_i1 := by decide +kernel
theorem pivot_mem_693_i1 : (5, 8) ∈ envelope_693_i1 := by decide +kernel
theorem children_work_693_i1 : ∀ j, Template HasSnaky 10 (childrenC_693_i1 j) (childrenD_693_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_28 0 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_409 1 (2, 7)).mono (by decide +kernel)
theorem row_works_693_i1 : Template HasSnaky 11 required_693_i1 envelope_693_i1 := by
  refine compose HasSnaky 10 childrenC_693_i1 childrenD_693_i1 children_work_693_i1 (5, 8)
    required_693_i1 envelope_693_i1 pivot_mem_693_i1 child_required_sub_693_i1 child_envelope_sub_693_i1 ?_
  intro b hb
  exact common_sub_693_i1 (mem_commonEnvelope childrenD_693_i1 b hb)
def required_693_i2 : Finset Cell := ⟨(([(4, 5), (5, 5), (5, 7), (6, 5), (7, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_693_i2 : Finset Cell := ⟨(([(1, 7), (2, 6), (2, 7), (2, 8), (2, 9), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 4), (6, 5), (6, 7), (6, 8), (6, 9), (6, 10), (7, 5), (7, 8), (7, 9), (8, 7), (8, 8), (8, 9), (9, 7), (9, 8), (9, 9), (10, 7), (10, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_693_i2 : Fin 3 → Finset Cell := ![(placed21 5 (7, 4) required_168), (placed21 1 (2, 7) required_409), (placed21 1 (1, 6) required_611)]
def childrenD_693_i2 : Fin 3 → Finset Cell := ![(placed21 5 (7, 4) envelope_168), (placed21 1 (2, 7) envelope_409), (placed21 1 (1, 6) envelope_611)]
theorem common_sub_693_i2 : commonEnvelope childrenD_693_i2 ⊆ insert (5, 8) required_693_i2 := by decide +kernel
theorem child_required_sub_693_i2 : ∀ j, childrenC_693_i2 j ⊆ insert (5, 8) required_693_i2 := by decide +kernel
theorem child_envelope_sub_693_i2 : ∀ j, childrenD_693_i2 j ⊆ envelope_693_i2 := by decide +kernel
theorem pivot_mem_693_i2 : (5, 8) ∈ envelope_693_i2 := by decide +kernel
theorem children_work_693_i2 : ∀ j, Template HasSnaky 10 (childrenC_693_i2 j) (childrenD_693_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_168 5 (7, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_409 1 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_611 1 (1, 6)).mono (by decide +kernel)
theorem row_works_693_i2 : Template HasSnaky 11 required_693_i2 envelope_693_i2 := by
  refine compose HasSnaky 10 childrenC_693_i2 childrenD_693_i2 children_work_693_i2 (5, 8)
    required_693_i2 envelope_693_i2 pivot_mem_693_i2 child_required_sub_693_i2 child_envelope_sub_693_i2 ?_
  intro b hb
  exact common_sub_693_i2 (mem_commonEnvelope childrenD_693_i2 b hb)
def required_693_i4 : Finset Cell := ⟨(([(3, 5), (4, 5), (5, 5), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_693_i4 : Finset Cell := ⟨(([(0, 4), (0, 6), (1, 4), (1, 5), (1, 6), (2, 4), (2, 5), (2, 6), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_693_i4 : Fin 2 → Finset Cell := ![(placed21 5 (6, 4) required_10), (placed21 4 (4, 8) required_308)]
def childrenD_693_i4 : Fin 2 → Finset Cell := ![(placed21 5 (6, 4) envelope_10), (placed21 4 (4, 8) envelope_308)]
theorem common_sub_693_i4 : commonEnvelope childrenD_693_i4 ⊆ insert (5, 4) required_693_i4 := by decide +kernel
theorem child_required_sub_693_i4 : ∀ j, childrenC_693_i4 j ⊆ insert (5, 4) required_693_i4 := by decide +kernel
theorem child_envelope_sub_693_i4 : ∀ j, childrenD_693_i4 j ⊆ envelope_693_i4 := by decide +kernel
theorem pivot_mem_693_i4 : (5, 4) ∈ envelope_693_i4 := by decide +kernel
theorem children_work_693_i4 : ∀ j, Template HasSnaky 5 (childrenC_693_i4 j) (childrenD_693_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 5 (6, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_308 4 (4, 8)).mono (by decide +kernel)
theorem row_works_693_i4 : Template HasSnaky 6 required_693_i4 envelope_693_i4 := by
  refine compose HasSnaky 5 childrenC_693_i4 childrenD_693_i4 children_work_693_i4 (5, 4)
    required_693_i4 envelope_693_i4 pivot_mem_693_i4 child_required_sub_693_i4 child_envelope_sub_693_i4 ?_
  intro b hb
  exact common_sub_693_i4 (mem_commonEnvelope childrenD_693_i4 b hb)
def required_693_i3 : Finset Cell := ⟨(([(4, 5), (5, 5), (5, 7), (6, 5), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_693_i3 : Finset Cell := ⟨(([(0, 4), (0, 6), (1, 4), (1, 5), (1, 6), (2, 4), (2, 5), (2, 6), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_693_i3 : Fin 4 → Finset Cell := ![(placed21 5 (7, 5) required_6), (placed21 2 (6, 4) required_26), (placed21 2 (7, 2) required_214), required_693_i4]
def childrenD_693_i3 : Fin 4 → Finset Cell := ![(placed21 5 (7, 5) envelope_6), (placed21 2 (6, 4) envelope_26), (placed21 2 (7, 2) envelope_214), envelope_693_i4]
theorem common_sub_693_i3 : commonEnvelope childrenD_693_i3 ⊆ insert (3, 5) required_693_i3 := by decide +kernel
theorem child_required_sub_693_i3 : ∀ j, childrenC_693_i3 j ⊆ insert (3, 5) required_693_i3 := by decide +kernel
theorem child_envelope_sub_693_i3 : ∀ j, childrenD_693_i3 j ⊆ envelope_693_i3 := by decide +kernel
theorem pivot_mem_693_i3 : (3, 5) ∈ envelope_693_i3 := by decide +kernel
theorem children_work_693_i3 : ∀ j, Template HasSnaky 6 (childrenC_693_i3 j) (childrenD_693_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 5 (7, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_26 2 (6, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_214 2 (7, 2)).mono (by decide +kernel)
  · exact row_works_693_i4.mono (by decide +kernel)
theorem row_works_693_i3 : Template HasSnaky 7 required_693_i3 envelope_693_i3 := by
  refine compose HasSnaky 6 childrenC_693_i3 childrenD_693_i3 children_work_693_i3 (3, 5)
    required_693_i3 envelope_693_i3 pivot_mem_693_i3 child_required_sub_693_i3 child_envelope_sub_693_i3 ?_
  intro b hb
  exact common_sub_693_i3 (mem_commonEnvelope childrenD_693_i3 b hb)
def required_693_i6 : Finset Cell := ⟨(([(4, 5), (5, 5), (5, 6), (5, 7), (6, 5), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_693_i6 : Finset Cell := ⟨(([(0, 4), (1, 4), (1, 5), (2, 4), (2, 5), (2, 6), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_693_i6 : Fin 3 → Finset Cell := ![(placed21 2 (7, 4) required_233), (placed21 7 (6, 7) required_314), (placed21 3 (4, 7) required_314)]
def childrenD_693_i6 : Fin 3 → Finset Cell := ![(placed21 2 (7, 4) envelope_233), (placed21 7 (6, 7) envelope_314), (placed21 3 (4, 7) envelope_314)]
theorem common_sub_693_i6 : commonEnvelope childrenD_693_i6 ⊆ insert (5, 4) required_693_i6 := by decide +kernel
theorem child_required_sub_693_i6 : ∀ j, childrenC_693_i6 j ⊆ insert (5, 4) required_693_i6 := by decide +kernel
theorem child_envelope_sub_693_i6 : ∀ j, childrenD_693_i6 j ⊆ envelope_693_i6 := by decide +kernel
theorem pivot_mem_693_i6 : (5, 4) ∈ envelope_693_i6 := by decide +kernel
theorem children_work_693_i6 : ∀ j, Template HasSnaky 5 (childrenC_693_i6 j) (childrenD_693_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_233 2 (7, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_314 7 (6, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_314 3 (4, 7)).mono (by decide +kernel)
theorem row_works_693_i6 : Template HasSnaky 6 required_693_i6 envelope_693_i6 := by
  refine compose HasSnaky 5 childrenC_693_i6 childrenD_693_i6 children_work_693_i6 (5, 4)
    required_693_i6 envelope_693_i6 pivot_mem_693_i6 child_required_sub_693_i6 child_envelope_sub_693_i6 ?_
  intro b hb
  exact common_sub_693_i6 (mem_commonEnvelope childrenD_693_i6 b hb)
def required_693_i5 : Finset Cell := ⟨(([(4, 5), (5, 5), (5, 7), (6, 5), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_693_i5 : Finset Cell := ⟨(([(0, 4), (1, 4), (1, 5), (2, 4), (2, 5), (2, 6), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_693_i5 : Fin 3 → Finset Cell := ![(placed21 6 (5, 8) required_44), (placed21 4 (5, 8) required_52), required_693_i6]
def childrenD_693_i5 : Fin 3 → Finset Cell := ![(placed21 6 (5, 8) envelope_44), (placed21 4 (5, 8) envelope_52), envelope_693_i6]
theorem common_sub_693_i5 : commonEnvelope childrenD_693_i5 ⊆ insert (5, 6) required_693_i5 := by decide +kernel
theorem child_required_sub_693_i5 : ∀ j, childrenC_693_i5 j ⊆ insert (5, 6) required_693_i5 := by decide +kernel
theorem child_envelope_sub_693_i5 : ∀ j, childrenD_693_i5 j ⊆ envelope_693_i5 := by decide +kernel
theorem pivot_mem_693_i5 : (5, 6) ∈ envelope_693_i5 := by decide +kernel
theorem children_work_693_i5 : ∀ j, Template HasSnaky 6 (childrenC_693_i5 j) (childrenD_693_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 6 (5, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 4 (5, 8)).mono (by decide +kernel)
  · exact row_works_693_i6.mono (by decide +kernel)
theorem row_works_693_i5 : Template HasSnaky 7 required_693_i5 envelope_693_i5 := by
  refine compose HasSnaky 6 childrenC_693_i5 childrenD_693_i5 children_work_693_i5 (5, 6)
    required_693_i5 envelope_693_i5 pivot_mem_693_i5 child_required_sub_693_i5 child_envelope_sub_693_i5 ?_
  intro b hb
  exact common_sub_693_i5 (mem_commonEnvelope childrenD_693_i5 b hb)
def required_693_i0 : Finset Cell := ⟨(([(4, 5), (5, 5), (6, 5), (7, 5), (7, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_693_i0 : Finset Cell := ⟨(([(0, 4), (0, 6), (1, 4), (1, 5), (1, 6), (1, 7), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 1), (3, 2), (3, 3), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 7), (6, 8), (6, 9), (6, 10), (7, 5), (7, 8), (7, 9), (8, 7), (8, 8), (8, 9), (9, 7), (9, 8), (9, 9), (10, 7), (10, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_693_i0 : Fin 5 → Finset Cell := ![(placed21 6 (7, 10) required_319), required_693_i1, required_693_i2, required_693_i3, required_693_i5]
def childrenD_693_i0 : Fin 5 → Finset Cell := ![(placed21 6 (7, 10) envelope_319), envelope_693_i1, envelope_693_i2, envelope_693_i3, envelope_693_i5]
theorem common_sub_693_i0 : commonEnvelope childrenD_693_i0 ⊆ insert (5, 7) required_693_i0 := by decide +kernel
theorem child_required_sub_693_i0 : ∀ j, childrenC_693_i0 j ⊆ insert (5, 7) required_693_i0 := by decide +kernel
theorem child_envelope_sub_693_i0 : ∀ j, childrenD_693_i0 j ⊆ envelope_693_i0 := by decide +kernel
theorem pivot_mem_693_i0 : (5, 7) ∈ envelope_693_i0 := by decide +kernel
theorem children_work_693_i0 : ∀ j, Template HasSnaky 11 (childrenC_693_i0 j) (childrenD_693_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_319 6 (7, 10)).mono (by decide +kernel)
  · exact row_works_693_i1.mono (by decide +kernel)
  · exact row_works_693_i2.mono (by decide +kernel)
  · exact row_works_693_i3.mono (by decide +kernel)
  · exact row_works_693_i5.mono (by decide +kernel)
theorem row_works_693_i0 : Template HasSnaky 12 required_693_i0 envelope_693_i0 := by
  refine compose HasSnaky 11 childrenC_693_i0 childrenD_693_i0 children_work_693_i0 (5, 7)
    required_693_i0 envelope_693_i0 pivot_mem_693_i0 child_required_sub_693_i0 child_envelope_sub_693_i0 ?_
  intro b hb
  exact common_sub_693_i0 (mem_commonEnvelope childrenD_693_i0 b hb)
def required_693 : Finset Cell := ⟨(([(4, 5), (5, 5), (6, 5), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_693 : Finset Cell := ⟨(([(0, 4), (0, 6), (1, 4), (1, 5), (1, 6), (1, 7), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 1), (3, 2), (3, 3), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (11, 7), (11, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_693 : Fin 4 → Finset Cell := ![(placed21 0 (4, 4) required_147), (placed21 7 (8, 8) required_339), (placed21 1 (2, 5) required_692), required_693_i0]
def childrenD_693 : Fin 4 → Finset Cell := ![(placed21 0 (4, 4) envelope_147), (placed21 7 (8, 8) envelope_339), (placed21 1 (2, 5) envelope_692), envelope_693_i0]
theorem common_sub_693 : commonEnvelope childrenD_693 ⊆ insert (7, 8) required_693 := by decide +kernel
theorem child_required_sub_693 : ∀ j, childrenC_693 j ⊆ insert (7, 8) required_693 := by decide +kernel
theorem child_envelope_sub_693 : ∀ j, childrenD_693 j ⊆ envelope_693 := by decide +kernel
theorem pivot_mem_693 : (7, 8) ∈ envelope_693 := by decide +kernel
theorem children_work_693 : ∀ j, Template HasSnaky 13 (childrenC_693 j) (childrenD_693 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_147 0 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_339 7 (8, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_692 1 (2, 5)).mono (by decide +kernel)
  · exact row_works_693_i0.mono (by decide +kernel)
theorem row_works_693 : Template HasSnaky 14 required_693 envelope_693 := by
  refine compose HasSnaky 13 childrenC_693 childrenD_693 children_work_693 (7, 8)
    required_693 envelope_693 pivot_mem_693 child_required_sub_693 child_envelope_sub_693 ?_
  intro b hb
  exact common_sub_693 (mem_commonEnvelope childrenD_693 b hb)
def height_645_i0 : ℕ := 6
def childrenH_645_i0 : Fin 4 → ℕ := ![height_44, height_52, height_128, height_144]
theorem height_exact_645_i0 : height_645_i0 = 1 + Finset.univ.sup childrenH_645_i0 := by decide +kernel
theorem required_origin_645_i0 : ∀ x ∈ required_645_i0,
    (∃ j, x ∈ childrenC_645_i0 j) ∨ ∀ j, x ∈ childrenD_645_i0 j := by decide +kernel
theorem required_exact_645_i0 : required_645_i0 =
    ((Finset.univ.biUnion childrenC_645_i0) ∪ commonEnvelope childrenD_645_i0).erase (5, 4) := by
  exact required_eq_combination childrenC_645_i0 childrenD_645_i0 (5, 4) required_645_i0
    (by decide +kernel) child_required_sub_645_i0 common_sub_645_i0 required_origin_645_i0
theorem envelope_origin_645_i0 : ∀ x ∈ envelope_645_i0,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_645_i0 j := by decide +kernel
theorem envelope_exact_645_i0 : envelope_645_i0 =
    insert (5, 4) (Finset.univ.biUnion childrenD_645_i0) := by
  exact envelope_eq_combination childrenD_645_i0 (5, 4) envelope_645_i0
    pivot_mem_645_i0 child_envelope_sub_645_i0 envelope_origin_645_i0
def checked_645_i0 : CheckedCard where
  required := required_645_i0
  envelope := envelope_645_i0
  height := height_645_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_645_i0
def height_645_i1 : ℕ := 11
def childrenH_645_i1 : Fin 6 → ℕ := ![height_104, height_359, height_438, height_452, height_476, height_479]
theorem height_exact_645_i1 : height_645_i1 = 1 + Finset.univ.sup childrenH_645_i1 := by decide +kernel
theorem required_origin_645_i1 : ∀ x ∈ required_645_i1,
    (∃ j, x ∈ childrenC_645_i1 j) ∨ ∀ j, x ∈ childrenD_645_i1 j := by decide +kernel
theorem required_exact_645_i1 : required_645_i1 =
    ((Finset.univ.biUnion childrenC_645_i1) ∪ commonEnvelope childrenD_645_i1).erase (6, 5) := by
  exact required_eq_combination childrenC_645_i1 childrenD_645_i1 (6, 5) required_645_i1
    (by decide +kernel) child_required_sub_645_i1 common_sub_645_i1 required_origin_645_i1
theorem envelope_origin_645_i1 : ∀ x ∈ envelope_645_i1,
    x = (6, 5) ∨ ∃ j, x ∈ childrenD_645_i1 j := by decide +kernel
theorem envelope_exact_645_i1 : envelope_645_i1 =
    insert (6, 5) (Finset.univ.biUnion childrenD_645_i1) := by
  exact envelope_eq_combination childrenD_645_i1 (6, 5) envelope_645_i1
    pivot_mem_645_i1 child_envelope_sub_645_i1 envelope_origin_645_i1
def checked_645_i1 : CheckedCard where
  required := required_645_i1
  envelope := envelope_645_i1
  height := height_645_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_645_i1
def height_645 : ℕ := 14
def childrenH_645 : Fin 10 → ℕ := ![height_120, height_276, height_338, height_437, height_611, height_634, height_642, height_643, height_645_i0, height_645_i1]
theorem height_exact_645 : height_645 = 1 + Finset.univ.sup childrenH_645 := by decide +kernel
theorem required_origin_645 : ∀ x ∈ required_645,
    (∃ j, x ∈ childrenC_645 j) ∨ ∀ j, x ∈ childrenD_645 j := by decide +kernel
theorem required_exact_645 : required_645 =
    ((Finset.univ.biUnion childrenC_645) ∪ commonEnvelope childrenD_645).erase (6, 4) := by
  exact required_eq_combination childrenC_645 childrenD_645 (6, 4) required_645
    (by decide +kernel) child_required_sub_645 common_sub_645 required_origin_645
theorem envelope_origin_645 : ∀ x ∈ envelope_645,
    x = (6, 4) ∨ ∃ j, x ∈ childrenD_645 j := by decide +kernel
theorem envelope_exact_645 : envelope_645 =
    insert (6, 4) (Finset.univ.biUnion childrenD_645) := by
  exact envelope_eq_combination childrenD_645 (6, 4) envelope_645
    pivot_mem_645 child_envelope_sub_645 envelope_origin_645
def checked_645 : CheckedCard where
  required := required_645
  envelope := envelope_645
  height := height_645
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_645
def height_669_i5 : ℕ := 3
def childrenH_669_i5 : Fin 2 → ℕ := ![height_0, height_66]
theorem height_exact_669_i5 : height_669_i5 = 1 + Finset.univ.sup childrenH_669_i5 := by decide +kernel
theorem required_origin_669_i5 : ∀ x ∈ required_669_i5,
    (∃ j, x ∈ childrenC_669_i5 j) ∨ ∀ j, x ∈ childrenD_669_i5 j := by decide +kernel
theorem required_exact_669_i5 : required_669_i5 =
    ((Finset.univ.biUnion childrenC_669_i5) ∪ commonEnvelope childrenD_669_i5).erase (5, 6) := by
  exact required_eq_combination childrenC_669_i5 childrenD_669_i5 (5, 6) required_669_i5
    (by decide +kernel) child_required_sub_669_i5 common_sub_669_i5 required_origin_669_i5
theorem envelope_origin_669_i5 : ∀ x ∈ envelope_669_i5,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_669_i5 j := by decide +kernel
theorem envelope_exact_669_i5 : envelope_669_i5 =
    insert (5, 6) (Finset.univ.biUnion childrenD_669_i5) := by
  exact envelope_eq_combination childrenD_669_i5 (5, 6) envelope_669_i5
    pivot_mem_669_i5 child_envelope_sub_669_i5 envelope_origin_669_i5
def checked_669_i5 : CheckedCard where
  required := required_669_i5
  envelope := envelope_669_i5
  height := height_669_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_669_i5
def height_669_i4 : ℕ := 4
def childrenH_669_i4 : Fin 2 → ℕ := ![height_0, height_669_i5]
theorem height_exact_669_i4 : height_669_i4 = 1 + Finset.univ.sup childrenH_669_i4 := by decide +kernel
theorem required_origin_669_i4 : ∀ x ∈ required_669_i4,
    (∃ j, x ∈ childrenC_669_i4 j) ∨ ∀ j, x ∈ childrenD_669_i4 j := by decide +kernel
theorem required_exact_669_i4 : required_669_i4 =
    ((Finset.univ.biUnion childrenC_669_i4) ∪ commonEnvelope childrenD_669_i4).erase (4, 6) := by
  exact required_eq_combination childrenC_669_i4 childrenD_669_i4 (4, 6) required_669_i4
    (by decide +kernel) child_required_sub_669_i4 common_sub_669_i4 required_origin_669_i4
theorem envelope_origin_669_i4 : ∀ x ∈ envelope_669_i4,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_669_i4 j := by decide +kernel
theorem envelope_exact_669_i4 : envelope_669_i4 =
    insert (4, 6) (Finset.univ.biUnion childrenD_669_i4) := by
  exact envelope_eq_combination childrenD_669_i4 (4, 6) envelope_669_i4
    pivot_mem_669_i4 child_envelope_sub_669_i4 envelope_origin_669_i4
def checked_669_i4 : CheckedCard where
  required := required_669_i4
  envelope := envelope_669_i4
  height := height_669_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_669_i4
def height_669_i6 : ℕ := 3
def childrenH_669_i6 : Fin 2 → ℕ := ![height_5, height_36]
theorem height_exact_669_i6 : height_669_i6 = 1 + Finset.univ.sup childrenH_669_i6 := by decide +kernel
theorem required_origin_669_i6 : ∀ x ∈ required_669_i6,
    (∃ j, x ∈ childrenC_669_i6 j) ∨ ∀ j, x ∈ childrenD_669_i6 j := by decide +kernel
theorem required_exact_669_i6 : required_669_i6 =
    ((Finset.univ.biUnion childrenC_669_i6) ∪ commonEnvelope childrenD_669_i6).erase (3, 7) := by
  exact required_eq_combination childrenC_669_i6 childrenD_669_i6 (3, 7) required_669_i6
    (by decide +kernel) child_required_sub_669_i6 common_sub_669_i6 required_origin_669_i6
theorem envelope_origin_669_i6 : ∀ x ∈ envelope_669_i6,
    x = (3, 7) ∨ ∃ j, x ∈ childrenD_669_i6 j := by decide +kernel
theorem envelope_exact_669_i6 : envelope_669_i6 =
    insert (3, 7) (Finset.univ.biUnion childrenD_669_i6) := by
  exact envelope_eq_combination childrenD_669_i6 (3, 7) envelope_669_i6
    pivot_mem_669_i6 child_envelope_sub_669_i6 envelope_origin_669_i6
def checked_669_i6 : CheckedCard where
  required := required_669_i6
  envelope := envelope_669_i6
  height := height_669_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_669_i6
def height_669_i7 : ℕ := 4
def childrenH_669_i7 : Fin 2 → ℕ := ![height_24, height_36]
theorem height_exact_669_i7 : height_669_i7 = 1 + Finset.univ.sup childrenH_669_i7 := by decide +kernel
theorem required_origin_669_i7 : ∀ x ∈ required_669_i7,
    (∃ j, x ∈ childrenC_669_i7 j) ∨ ∀ j, x ∈ childrenD_669_i7 j := by decide +kernel
theorem required_exact_669_i7 : required_669_i7 =
    ((Finset.univ.biUnion childrenC_669_i7) ∪ commonEnvelope childrenD_669_i7).erase (3, 7) := by
  exact required_eq_combination childrenC_669_i7 childrenD_669_i7 (3, 7) required_669_i7
    (by decide +kernel) child_required_sub_669_i7 common_sub_669_i7 required_origin_669_i7
theorem envelope_origin_669_i7 : ∀ x ∈ envelope_669_i7,
    x = (3, 7) ∨ ∃ j, x ∈ childrenD_669_i7 j := by decide +kernel
theorem envelope_exact_669_i7 : envelope_669_i7 =
    insert (3, 7) (Finset.univ.biUnion childrenD_669_i7) := by
  exact envelope_eq_combination childrenD_669_i7 (3, 7) envelope_669_i7
    pivot_mem_669_i7 child_envelope_sub_669_i7 envelope_origin_669_i7
def checked_669_i7 : CheckedCard where
  required := required_669_i7
  envelope := envelope_669_i7
  height := height_669_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_669_i7
def height_669_i3 : ℕ := 5
def childrenH_669_i3 : Fin 4 → ℕ := ![height_48, height_669_i4, height_669_i6, height_669_i7]
theorem height_exact_669_i3 : height_669_i3 = 1 + Finset.univ.sup childrenH_669_i3 := by decide +kernel
theorem required_origin_669_i3 : ∀ x ∈ required_669_i3,
    (∃ j, x ∈ childrenC_669_i3 j) ∨ ∀ j, x ∈ childrenD_669_i3 j := by decide +kernel
theorem required_exact_669_i3 : required_669_i3 =
    ((Finset.univ.biUnion childrenC_669_i3) ∪ commonEnvelope childrenD_669_i3).erase (4, 7) := by
  exact required_eq_combination childrenC_669_i3 childrenD_669_i3 (4, 7) required_669_i3
    (by decide +kernel) child_required_sub_669_i3 common_sub_669_i3 required_origin_669_i3
theorem envelope_origin_669_i3 : ∀ x ∈ envelope_669_i3,
    x = (4, 7) ∨ ∃ j, x ∈ childrenD_669_i3 j := by decide +kernel
theorem envelope_exact_669_i3 : envelope_669_i3 =
    insert (4, 7) (Finset.univ.biUnion childrenD_669_i3) := by
  exact envelope_eq_combination childrenD_669_i3 (4, 7) envelope_669_i3
    pivot_mem_669_i3 child_envelope_sub_669_i3 envelope_origin_669_i3
def checked_669_i3 : CheckedCard where
  required := required_669_i3
  envelope := envelope_669_i3
  height := height_669_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_669_i3
def height_669_i2 : ℕ := 6
def childrenH_669_i2 : Fin 2 → ℕ := ![height_5, height_669_i3]
theorem height_exact_669_i2 : height_669_i2 = 1 + Finset.univ.sup childrenH_669_i2 := by decide +kernel
theorem required_origin_669_i2 : ∀ x ∈ required_669_i2,
    (∃ j, x ∈ childrenC_669_i2 j) ∨ ∀ j, x ∈ childrenD_669_i2 j := by decide +kernel
theorem required_exact_669_i2 : required_669_i2 =
    ((Finset.univ.biUnion childrenC_669_i2) ∪ commonEnvelope childrenD_669_i2).erase (5, 7) := by
  exact required_eq_combination childrenC_669_i2 childrenD_669_i2 (5, 7) required_669_i2
    (by decide +kernel) child_required_sub_669_i2 common_sub_669_i2 required_origin_669_i2
theorem envelope_origin_669_i2 : ∀ x ∈ envelope_669_i2,
    x = (5, 7) ∨ ∃ j, x ∈ childrenD_669_i2 j := by decide +kernel
theorem envelope_exact_669_i2 : envelope_669_i2 =
    insert (5, 7) (Finset.univ.biUnion childrenD_669_i2) := by
  exact envelope_eq_combination childrenD_669_i2 (5, 7) envelope_669_i2
    pivot_mem_669_i2 child_envelope_sub_669_i2 envelope_origin_669_i2
def checked_669_i2 : CheckedCard where
  required := required_669_i2
  envelope := envelope_669_i2
  height := height_669_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_669_i2
def height_669_i1 : ℕ := 7
def childrenH_669_i1 : Fin 2 → ℕ := ![height_25, height_669_i2]
theorem height_exact_669_i1 : height_669_i1 = 1 + Finset.univ.sup childrenH_669_i1 := by decide +kernel
theorem required_origin_669_i1 : ∀ x ∈ required_669_i1,
    (∃ j, x ∈ childrenC_669_i1 j) ∨ ∀ j, x ∈ childrenD_669_i1 j := by decide +kernel
theorem required_exact_669_i1 : required_669_i1 =
    ((Finset.univ.biUnion childrenC_669_i1) ∪ commonEnvelope childrenD_669_i1).erase (4, 5) := by
  exact required_eq_combination childrenC_669_i1 childrenD_669_i1 (4, 5) required_669_i1
    (by decide +kernel) child_required_sub_669_i1 common_sub_669_i1 required_origin_669_i1
theorem envelope_origin_669_i1 : ∀ x ∈ envelope_669_i1,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_669_i1 j := by decide +kernel
theorem envelope_exact_669_i1 : envelope_669_i1 =
    insert (4, 5) (Finset.univ.biUnion childrenD_669_i1) := by
  exact envelope_eq_combination childrenD_669_i1 (4, 5) envelope_669_i1
    pivot_mem_669_i1 child_envelope_sub_669_i1 envelope_origin_669_i1
def checked_669_i1 : CheckedCard where
  required := required_669_i1
  envelope := envelope_669_i1
  height := height_669_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_669_i1
def height_669_i0 : ℕ := 8
def childrenH_669_i0 : Fin 4 → ℕ := ![height_19, height_197, height_225, height_669_i1]
theorem height_exact_669_i0 : height_669_i0 = 1 + Finset.univ.sup childrenH_669_i0 := by decide +kernel
theorem required_origin_669_i0 : ∀ x ∈ required_669_i0,
    (∃ j, x ∈ childrenC_669_i0 j) ∨ ∀ j, x ∈ childrenD_669_i0 j := by decide +kernel
theorem required_exact_669_i0 : required_669_i0 =
    ((Finset.univ.biUnion childrenC_669_i0) ∪ commonEnvelope childrenD_669_i0).erase (6, 7) := by
  exact required_eq_combination childrenC_669_i0 childrenD_669_i0 (6, 7) required_669_i0
    (by decide +kernel) child_required_sub_669_i0 common_sub_669_i0 required_origin_669_i0
theorem envelope_origin_669_i0 : ∀ x ∈ envelope_669_i0,
    x = (6, 7) ∨ ∃ j, x ∈ childrenD_669_i0 j := by decide +kernel
theorem envelope_exact_669_i0 : envelope_669_i0 =
    insert (6, 7) (Finset.univ.biUnion childrenD_669_i0) := by
  exact envelope_eq_combination childrenD_669_i0 (6, 7) envelope_669_i0
    pivot_mem_669_i0 child_envelope_sub_669_i0 envelope_origin_669_i0
def checked_669_i0 : CheckedCard where
  required := required_669_i0
  envelope := envelope_669_i0
  height := height_669_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_669_i0
def height_669 : ℕ := 14
def childrenH_669 : Fin 4 → ℕ := ![height_188, height_590, height_668, height_669_i0]
theorem height_exact_669 : height_669 = 1 + Finset.univ.sup childrenH_669 := by decide +kernel
theorem required_origin_669 : ∀ x ∈ required_669,
    (∃ j, x ∈ childrenC_669 j) ∨ ∀ j, x ∈ childrenD_669 j := by decide +kernel
theorem required_exact_669 : required_669 =
    ((Finset.univ.biUnion childrenC_669) ∪ commonEnvelope childrenD_669).erase (6, 4) := by
  exact required_eq_combination childrenC_669 childrenD_669 (6, 4) required_669
    (by decide +kernel) child_required_sub_669 common_sub_669 required_origin_669
theorem envelope_origin_669 : ∀ x ∈ envelope_669,
    x = (6, 4) ∨ ∃ j, x ∈ childrenD_669 j := by decide +kernel
theorem envelope_exact_669 : envelope_669 =
    insert (6, 4) (Finset.univ.biUnion childrenD_669) := by
  exact envelope_eq_combination childrenD_669 (6, 4) envelope_669
    pivot_mem_669 child_envelope_sub_669 envelope_origin_669
def checked_669 : CheckedCard where
  required := required_669
  envelope := envelope_669
  height := height_669
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_669
def height_693_i1 : ℕ := 11
def childrenH_693_i1 : Fin 2 → ℕ := ![height_28, height_409]
theorem height_exact_693_i1 : height_693_i1 = 1 + Finset.univ.sup childrenH_693_i1 := by decide +kernel
theorem required_origin_693_i1 : ∀ x ∈ required_693_i1,
    (∃ j, x ∈ childrenC_693_i1 j) ∨ ∀ j, x ∈ childrenD_693_i1 j := by decide +kernel
theorem required_exact_693_i1 : required_693_i1 =
    ((Finset.univ.biUnion childrenC_693_i1) ∪ commonEnvelope childrenD_693_i1).erase (5, 8) := by
  exact required_eq_combination childrenC_693_i1 childrenD_693_i1 (5, 8) required_693_i1
    (by decide +kernel) child_required_sub_693_i1 common_sub_693_i1 required_origin_693_i1
theorem envelope_origin_693_i1 : ∀ x ∈ envelope_693_i1,
    x = (5, 8) ∨ ∃ j, x ∈ childrenD_693_i1 j := by decide +kernel
theorem envelope_exact_693_i1 : envelope_693_i1 =
    insert (5, 8) (Finset.univ.biUnion childrenD_693_i1) := by
  exact envelope_eq_combination childrenD_693_i1 (5, 8) envelope_693_i1
    pivot_mem_693_i1 child_envelope_sub_693_i1 envelope_origin_693_i1
def checked_693_i1 : CheckedCard where
  required := required_693_i1
  envelope := envelope_693_i1
  height := height_693_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_693_i1
def height_693_i2 : ℕ := 11
def childrenH_693_i2 : Fin 3 → ℕ := ![height_168, height_409, height_611]
theorem height_exact_693_i2 : height_693_i2 = 1 + Finset.univ.sup childrenH_693_i2 := by decide +kernel
theorem required_origin_693_i2 : ∀ x ∈ required_693_i2,
    (∃ j, x ∈ childrenC_693_i2 j) ∨ ∀ j, x ∈ childrenD_693_i2 j := by decide +kernel
theorem required_exact_693_i2 : required_693_i2 =
    ((Finset.univ.biUnion childrenC_693_i2) ∪ commonEnvelope childrenD_693_i2).erase (5, 8) := by
  exact required_eq_combination childrenC_693_i2 childrenD_693_i2 (5, 8) required_693_i2
    (by decide +kernel) child_required_sub_693_i2 common_sub_693_i2 required_origin_693_i2
theorem envelope_origin_693_i2 : ∀ x ∈ envelope_693_i2,
    x = (5, 8) ∨ ∃ j, x ∈ childrenD_693_i2 j := by decide +kernel
theorem envelope_exact_693_i2 : envelope_693_i2 =
    insert (5, 8) (Finset.univ.biUnion childrenD_693_i2) := by
  exact envelope_eq_combination childrenD_693_i2 (5, 8) envelope_693_i2
    pivot_mem_693_i2 child_envelope_sub_693_i2 envelope_origin_693_i2
def checked_693_i2 : CheckedCard where
  required := required_693_i2
  envelope := envelope_693_i2
  height := height_693_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_693_i2
def height_693_i4 : ℕ := 6
def childrenH_693_i4 : Fin 2 → ℕ := ![height_10, height_308]
theorem height_exact_693_i4 : height_693_i4 = 1 + Finset.univ.sup childrenH_693_i4 := by decide +kernel
theorem required_origin_693_i4 : ∀ x ∈ required_693_i4,
    (∃ j, x ∈ childrenC_693_i4 j) ∨ ∀ j, x ∈ childrenD_693_i4 j := by decide +kernel
theorem required_exact_693_i4 : required_693_i4 =
    ((Finset.univ.biUnion childrenC_693_i4) ∪ commonEnvelope childrenD_693_i4).erase (5, 4) := by
  exact required_eq_combination childrenC_693_i4 childrenD_693_i4 (5, 4) required_693_i4
    (by decide +kernel) child_required_sub_693_i4 common_sub_693_i4 required_origin_693_i4
theorem envelope_origin_693_i4 : ∀ x ∈ envelope_693_i4,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_693_i4 j := by decide +kernel
theorem envelope_exact_693_i4 : envelope_693_i4 =
    insert (5, 4) (Finset.univ.biUnion childrenD_693_i4) := by
  exact envelope_eq_combination childrenD_693_i4 (5, 4) envelope_693_i4
    pivot_mem_693_i4 child_envelope_sub_693_i4 envelope_origin_693_i4
def checked_693_i4 : CheckedCard where
  required := required_693_i4
  envelope := envelope_693_i4
  height := height_693_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_693_i4
def height_693_i3 : ℕ := 7
def childrenH_693_i3 : Fin 4 → ℕ := ![height_6, height_26, height_214, height_693_i4]
theorem height_exact_693_i3 : height_693_i3 = 1 + Finset.univ.sup childrenH_693_i3 := by decide +kernel
theorem required_origin_693_i3 : ∀ x ∈ required_693_i3,
    (∃ j, x ∈ childrenC_693_i3 j) ∨ ∀ j, x ∈ childrenD_693_i3 j := by decide +kernel
theorem required_exact_693_i3 : required_693_i3 =
    ((Finset.univ.biUnion childrenC_693_i3) ∪ commonEnvelope childrenD_693_i3).erase (3, 5) := by
  exact required_eq_combination childrenC_693_i3 childrenD_693_i3 (3, 5) required_693_i3
    (by decide +kernel) child_required_sub_693_i3 common_sub_693_i3 required_origin_693_i3
theorem envelope_origin_693_i3 : ∀ x ∈ envelope_693_i3,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_693_i3 j := by decide +kernel
theorem envelope_exact_693_i3 : envelope_693_i3 =
    insert (3, 5) (Finset.univ.biUnion childrenD_693_i3) := by
  exact envelope_eq_combination childrenD_693_i3 (3, 5) envelope_693_i3
    pivot_mem_693_i3 child_envelope_sub_693_i3 envelope_origin_693_i3
def checked_693_i3 : CheckedCard where
  required := required_693_i3
  envelope := envelope_693_i3
  height := height_693_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_693_i3
def height_693_i6 : ℕ := 6
def childrenH_693_i6 : Fin 3 → ℕ := ![height_233, height_314, height_314]
theorem height_exact_693_i6 : height_693_i6 = 1 + Finset.univ.sup childrenH_693_i6 := by decide +kernel
theorem required_origin_693_i6 : ∀ x ∈ required_693_i6,
    (∃ j, x ∈ childrenC_693_i6 j) ∨ ∀ j, x ∈ childrenD_693_i6 j := by decide +kernel
theorem required_exact_693_i6 : required_693_i6 =
    ((Finset.univ.biUnion childrenC_693_i6) ∪ commonEnvelope childrenD_693_i6).erase (5, 4) := by
  exact required_eq_combination childrenC_693_i6 childrenD_693_i6 (5, 4) required_693_i6
    (by decide +kernel) child_required_sub_693_i6 common_sub_693_i6 required_origin_693_i6
theorem envelope_origin_693_i6 : ∀ x ∈ envelope_693_i6,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_693_i6 j := by decide +kernel
theorem envelope_exact_693_i6 : envelope_693_i6 =
    insert (5, 4) (Finset.univ.biUnion childrenD_693_i6) := by
  exact envelope_eq_combination childrenD_693_i6 (5, 4) envelope_693_i6
    pivot_mem_693_i6 child_envelope_sub_693_i6 envelope_origin_693_i6
def checked_693_i6 : CheckedCard where
  required := required_693_i6
  envelope := envelope_693_i6
  height := height_693_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_693_i6
def height_693_i5 : ℕ := 7
def childrenH_693_i5 : Fin 3 → ℕ := ![height_44, height_52, height_693_i6]
theorem height_exact_693_i5 : height_693_i5 = 1 + Finset.univ.sup childrenH_693_i5 := by decide +kernel
theorem required_origin_693_i5 : ∀ x ∈ required_693_i5,
    (∃ j, x ∈ childrenC_693_i5 j) ∨ ∀ j, x ∈ childrenD_693_i5 j := by decide +kernel
theorem required_exact_693_i5 : required_693_i5 =
    ((Finset.univ.biUnion childrenC_693_i5) ∪ commonEnvelope childrenD_693_i5).erase (5, 6) := by
  exact required_eq_combination childrenC_693_i5 childrenD_693_i5 (5, 6) required_693_i5
    (by decide +kernel) child_required_sub_693_i5 common_sub_693_i5 required_origin_693_i5
theorem envelope_origin_693_i5 : ∀ x ∈ envelope_693_i5,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_693_i5 j := by decide +kernel
theorem envelope_exact_693_i5 : envelope_693_i5 =
    insert (5, 6) (Finset.univ.biUnion childrenD_693_i5) := by
  exact envelope_eq_combination childrenD_693_i5 (5, 6) envelope_693_i5
    pivot_mem_693_i5 child_envelope_sub_693_i5 envelope_origin_693_i5
def checked_693_i5 : CheckedCard where
  required := required_693_i5
  envelope := envelope_693_i5
  height := height_693_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_693_i5
def height_693_i0 : ℕ := 12
def childrenH_693_i0 : Fin 5 → ℕ := ![height_319, height_693_i1, height_693_i2, height_693_i3, height_693_i5]
theorem height_exact_693_i0 : height_693_i0 = 1 + Finset.univ.sup childrenH_693_i0 := by decide +kernel
theorem required_origin_693_i0 : ∀ x ∈ required_693_i0,
    (∃ j, x ∈ childrenC_693_i0 j) ∨ ∀ j, x ∈ childrenD_693_i0 j := by decide +kernel
theorem required_exact_693_i0 : required_693_i0 =
    ((Finset.univ.biUnion childrenC_693_i0) ∪ commonEnvelope childrenD_693_i0).erase (5, 7) := by
  exact required_eq_combination childrenC_693_i0 childrenD_693_i0 (5, 7) required_693_i0
    (by decide +kernel) child_required_sub_693_i0 common_sub_693_i0 required_origin_693_i0
theorem envelope_origin_693_i0 : ∀ x ∈ envelope_693_i0,
    x = (5, 7) ∨ ∃ j, x ∈ childrenD_693_i0 j := by decide +kernel
theorem envelope_exact_693_i0 : envelope_693_i0 =
    insert (5, 7) (Finset.univ.biUnion childrenD_693_i0) := by
  exact envelope_eq_combination childrenD_693_i0 (5, 7) envelope_693_i0
    pivot_mem_693_i0 child_envelope_sub_693_i0 envelope_origin_693_i0
def checked_693_i0 : CheckedCard where
  required := required_693_i0
  envelope := envelope_693_i0
  height := height_693_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_693_i0
def height_693 : ℕ := 14
def childrenH_693 : Fin 4 → ℕ := ![height_147, height_339, height_692, height_693_i0]
theorem height_exact_693 : height_693 = 1 + Finset.univ.sup childrenH_693 := by decide +kernel
theorem required_origin_693 : ∀ x ∈ required_693,
    (∃ j, x ∈ childrenC_693 j) ∨ ∀ j, x ∈ childrenD_693 j := by decide +kernel
theorem required_exact_693 : required_693 =
    ((Finset.univ.biUnion childrenC_693) ∪ commonEnvelope childrenD_693).erase (7, 8) := by
  exact required_eq_combination childrenC_693 childrenD_693 (7, 8) required_693
    (by decide +kernel) child_required_sub_693 common_sub_693 required_origin_693
theorem envelope_origin_693 : ∀ x ∈ envelope_693,
    x = (7, 8) ∨ ∃ j, x ∈ childrenD_693 j := by decide +kernel
theorem envelope_exact_693 : envelope_693 =
    insert (7, 8) (Finset.univ.biUnion childrenD_693) := by
  exact envelope_eq_combination childrenD_693 (7, 8) envelope_693
    pivot_mem_693 child_envelope_sub_693 envelope_origin_693
def checked_693 : CheckedCard where
  required := required_693
  envelope := envelope_693
  height := height_693
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_693
end SnakyPrototype.Certificate21

end OAI
