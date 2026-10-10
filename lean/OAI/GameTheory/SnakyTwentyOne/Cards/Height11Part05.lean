import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part07
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part06
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_639_i2 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_639_i2 : Finset Cell := ⟨(([(2, 5), (2, 6), (2, 7), (2, 8), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_639_i2 : Fin 3 → Finset Cell := ![(placed21 0 (3, 3) required_21), (placed21 2 (4, 3) required_37), (placed21 6 (4, 7) required_62)]
def childrenD_639_i2 : Fin 3 → Finset Cell := ![(placed21 0 (3, 3) envelope_21), (placed21 2 (4, 3) envelope_37), (placed21 6 (4, 7) envelope_62)]
theorem common_sub_639_i2 : commonEnvelope childrenD_639_i2 ⊆ insert (3, 6) required_639_i2 := by decide +kernel
theorem child_required_sub_639_i2 : ∀ j, childrenC_639_i2 j ⊆ insert (3, 6) required_639_i2 := by decide +kernel
theorem child_envelope_sub_639_i2 : ∀ j, childrenD_639_i2 j ⊆ envelope_639_i2 := by decide +kernel
theorem pivot_mem_639_i2 : (3, 6) ∈ envelope_639_i2 := by decide +kernel
theorem children_work_639_i2 : ∀ j, Template HasSnaky 3 (childrenC_639_i2 j) (childrenD_639_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_21 0 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_37 2 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_62 6 (4, 7)).mono (by decide +kernel)
theorem row_works_639_i2 : Template HasSnaky 4 required_639_i2 envelope_639_i2 := by
  refine compose HasSnaky 3 childrenC_639_i2 childrenD_639_i2 children_work_639_i2 (3, 6)
    required_639_i2 envelope_639_i2 pivot_mem_639_i2 child_required_sub_639_i2 child_envelope_sub_639_i2 ?_
  intro b hb
  exact common_sub_639_i2 (mem_commonEnvelope childrenD_639_i2 b hb)
def required_639_i1 : Finset Cell := ⟨(([(1, 3), (1, 4), (3, 3), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_639_i1 : Finset Cell := ⟨(([(0, 3), (0, 5), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_639_i1 : Fin 4 → Finset Cell := ![(placed21 2 (4, 2) required_71), (placed21 6 (4, 6) required_73), required_639_i2, (placed21 6 (4, 6) required_451)]
def childrenD_639_i1 : Fin 4 → Finset Cell := ![(placed21 2 (4, 2) envelope_71), (placed21 6 (4, 6) envelope_73), envelope_639_i2, (placed21 6 (4, 6) envelope_451)]
theorem common_sub_639_i1 : commonEnvelope childrenD_639_i1 ⊆ insert (3, 5) required_639_i1 := by decide +kernel
theorem child_required_sub_639_i1 : ∀ j, childrenC_639_i1 j ⊆ insert (3, 5) required_639_i1 := by decide +kernel
theorem child_envelope_sub_639_i1 : ∀ j, childrenD_639_i1 j ⊆ envelope_639_i1 := by decide +kernel
theorem pivot_mem_639_i1 : (3, 5) ∈ envelope_639_i1 := by decide +kernel
theorem children_work_639_i1 : ∀ j, Template HasSnaky 5 (childrenC_639_i1 j) (childrenD_639_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_71 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_73 6 (4, 6)).mono (by decide +kernel)
  · exact row_works_639_i2.mono (by decide +kernel)
  · exact (placed21_template row_works_451 6 (4, 6)).mono (by decide +kernel)
theorem row_works_639_i1 : Template HasSnaky 6 required_639_i1 envelope_639_i1 := by
  refine compose HasSnaky 5 childrenC_639_i1 childrenD_639_i1 children_work_639_i1 (3, 5)
    required_639_i1 envelope_639_i1 pivot_mem_639_i1 child_required_sub_639_i1 child_envelope_sub_639_i1 ?_
  intro b hb
  exact common_sub_639_i1 (mem_commonEnvelope childrenD_639_i1 b hb)
def required_639_i3 : Finset Cell := ⟨(([(1, 3), (1, 4), (3, 3), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_639_i3 : Finset Cell := ⟨(([(0, 3), (0, 5), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 4), (5, 6), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_639_i3 : Fin 4 → Finset Cell := ![(placed21 2 (4, 2) required_71), (placed21 6 (4, 6) required_73), (placed21 5 (6, 2) required_435), (placed21 6 (4, 6) required_451)]
def childrenD_639_i3 : Fin 4 → Finset Cell := ![(placed21 2 (4, 2) envelope_71), (placed21 6 (4, 6) envelope_73), (placed21 5 (6, 2) envelope_435), (placed21 6 (4, 6) envelope_451)]
theorem common_sub_639_i3 : commonEnvelope childrenD_639_i3 ⊆ insert (3, 5) required_639_i3 := by decide +kernel
theorem child_required_sub_639_i3 : ∀ j, childrenC_639_i3 j ⊆ insert (3, 5) required_639_i3 := by decide +kernel
theorem child_envelope_sub_639_i3 : ∀ j, childrenD_639_i3 j ⊆ envelope_639_i3 := by decide +kernel
theorem pivot_mem_639_i3 : (3, 5) ∈ envelope_639_i3 := by decide +kernel
theorem children_work_639_i3 : ∀ j, Template HasSnaky 6 (childrenC_639_i3 j) (childrenD_639_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_71 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_73 6 (4, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 5 (6, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_451 6 (4, 6)).mono (by decide +kernel)
theorem row_works_639_i3 : Template HasSnaky 7 required_639_i3 envelope_639_i3 := by
  refine compose HasSnaky 6 childrenC_639_i3 childrenD_639_i3 children_work_639_i3 (3, 5)
    required_639_i3 envelope_639_i3 pivot_mem_639_i3 child_required_sub_639_i3 child_envelope_sub_639_i3 ?_
  intro b hb
  exact common_sub_639_i3 (mem_commonEnvelope childrenD_639_i3 b hb)
def required_639_i0 : Finset Cell := ⟨(([(1, 3), (1, 4), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_639_i0 : Finset Cell := ⟨(([(0, 3), (0, 5), (0, 6), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 4), (6, 5), (6, 6), (7, 4), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_639_i0 : Fin 4 → Finset Cell := ![(placed21 1 (0, 3) required_54), (placed21 1 (0, 2) required_638), required_639_i1, required_639_i3]
def childrenD_639_i0 : Fin 4 → Finset Cell := ![(placed21 1 (0, 3) envelope_54), (placed21 1 (0, 2) envelope_638), envelope_639_i1, envelope_639_i3]
theorem common_sub_639_i0 : commonEnvelope childrenD_639_i0 ⊆ insert (3, 3) required_639_i0 := by decide +kernel
theorem child_required_sub_639_i0 : ∀ j, childrenC_639_i0 j ⊆ insert (3, 3) required_639_i0 := by decide +kernel
theorem child_envelope_sub_639_i0 : ∀ j, childrenD_639_i0 j ⊆ envelope_639_i0 := by decide +kernel
theorem pivot_mem_639_i0 : (3, 3) ∈ envelope_639_i0 := by decide +kernel
theorem children_work_639_i0 : ∀ j, Template HasSnaky 9 (childrenC_639_i0 j) (childrenD_639_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_54 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_638 1 (0, 2)).mono (by decide +kernel)
  · exact row_works_639_i1.mono (by decide +kernel)
  · exact row_works_639_i3.mono (by decide +kernel)
theorem row_works_639_i0 : Template HasSnaky 10 required_639_i0 envelope_639_i0 := by
  refine compose HasSnaky 9 childrenC_639_i0 childrenD_639_i0 children_work_639_i0 (3, 3)
    required_639_i0 envelope_639_i0 pivot_mem_639_i0 child_required_sub_639_i0 child_envelope_sub_639_i0 ?_
  intro b hb
  exact common_sub_639_i0 (mem_commonEnvelope childrenD_639_i0 b hb)
def required_639 : Finset Cell := ⟨(([(1, 3), (1, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_639 : Finset Cell := ⟨(([(0, 3), (0, 5), (0, 6), (0, 7), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 3), (6, 4), (6, 5), (6, 6), (7, 4), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_639 : Fin 5 → Finset Cell := ![(placed21 1 (0, 3) required_50), (placed21 1 (0, 3) required_125), (placed21 0 (0, 2) required_478), (placed21 0 (0, 2) required_482), required_639_i0]
def childrenD_639 : Fin 5 → Finset Cell := ![(placed21 1 (0, 3) envelope_50), (placed21 1 (0, 3) envelope_125), (placed21 0 (0, 2) envelope_478), (placed21 0 (0, 2) envelope_482), envelope_639_i0]
theorem common_sub_639 : commonEnvelope childrenD_639 ⊆ insert (3, 4) required_639 := by decide +kernel
theorem child_required_sub_639 : ∀ j, childrenC_639 j ⊆ insert (3, 4) required_639 := by decide +kernel
theorem child_envelope_sub_639 : ∀ j, childrenD_639 j ⊆ envelope_639 := by decide +kernel
theorem pivot_mem_639 : (3, 4) ∈ envelope_639 := by decide +kernel
theorem children_work_639 : ∀ j, Template HasSnaky 10 (childrenC_639 j) (childrenD_639 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_50 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_125 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_478 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_482 0 (0, 2)).mono (by decide +kernel)
  · exact row_works_639_i0.mono (by decide +kernel)
theorem row_works_639 : Template HasSnaky 11 required_639 envelope_639 := by
  refine compose HasSnaky 10 childrenC_639 childrenD_639 children_work_639 (3, 4)
    required_639 envelope_639 pivot_mem_639 child_required_sub_639 child_envelope_sub_639 ?_
  intro b hb
  exact common_sub_639 (mem_commonEnvelope childrenD_639 b hb)
def required_646_i0 : Finset Cell := ⟨(([(3, 3), (3, 4), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_646_i0 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 4), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 4), (5, 5), (5, 6), (5, 7), (6, 4), (6, 5), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_646_i0 : Fin 3 → Finset Cell := ![(placed21 2 (4, 1) required_15), (placed21 1 (2, 2) required_72), (placed21 7 (6, 5) required_262)]
def childrenD_646_i0 : Fin 3 → Finset Cell := ![(placed21 2 (4, 1) envelope_15), (placed21 1 (2, 2) envelope_72), (placed21 7 (6, 5) envelope_262)]
theorem common_sub_646_i0 : commonEnvelope childrenD_646_i0 ⊆ insert (4, 2) required_646_i0 := by decide +kernel
theorem child_required_sub_646_i0 : ∀ j, childrenC_646_i0 j ⊆ insert (4, 2) required_646_i0 := by decide +kernel
theorem child_envelope_sub_646_i0 : ∀ j, childrenD_646_i0 j ⊆ envelope_646_i0 := by decide +kernel
theorem pivot_mem_646_i0 : (4, 2) ∈ envelope_646_i0 := by decide +kernel
theorem children_work_646_i0 : ∀ j, Template HasSnaky 5 (childrenC_646_i0 j) (childrenD_646_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_15 2 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_72 1 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_262 7 (6, 5)).mono (by decide +kernel)
theorem row_works_646_i0 : Template HasSnaky 6 required_646_i0 envelope_646_i0 := by
  refine compose HasSnaky 5 childrenC_646_i0 childrenD_646_i0 children_work_646_i0 (4, 2)
    required_646_i0 envelope_646_i0 pivot_mem_646_i0 child_required_sub_646_i0 child_envelope_sub_646_i0 ?_
  intro b hb
  exact common_sub_646_i0 (mem_commonEnvelope childrenD_646_i0 b hb)
def required_646 : Finset Cell := ⟨(([(3, 3), (3, 4), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_646 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 4), (5, 5), (5, 6), (5, 7), (6, 4), (6, 5), (6, 6), (7, 4), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_646 : Fin 6 → Finset Cell := ![(placed21 0 (1, 1) required_361), (placed21 5 (6, 1) required_361), (placed21 1 (0, 3) required_411), (placed21 5 (7, 1) required_600), (placed21 3 (0, 7) required_621), required_646_i0]
def childrenD_646 : Fin 6 → Finset Cell := ![(placed21 0 (1, 1) envelope_361), (placed21 5 (6, 1) envelope_361), (placed21 1 (0, 3) envelope_411), (placed21 5 (7, 1) envelope_600), (placed21 3 (0, 7) envelope_621), envelope_646_i0]
theorem common_sub_646 : commonEnvelope childrenD_646 ⊆ insert (4, 4) required_646 := by decide +kernel
theorem child_required_sub_646 : ∀ j, childrenC_646 j ⊆ insert (4, 4) required_646 := by decide +kernel
theorem child_envelope_sub_646 : ∀ j, childrenD_646 j ⊆ envelope_646 := by decide +kernel
theorem pivot_mem_646 : (4, 4) ∈ envelope_646 := by decide +kernel
theorem children_work_646 : ∀ j, Template HasSnaky 10 (childrenC_646 j) (childrenD_646 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_361 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_361 5 (6, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_411 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_600 5 (7, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_621 3 (0, 7)).mono (by decide +kernel)
  · exact row_works_646_i0.mono (by decide +kernel)
theorem row_works_646 : Template HasSnaky 11 required_646 envelope_646 := by
  refine compose HasSnaky 10 childrenC_646 childrenD_646 children_work_646 (4, 4)
    required_646 envelope_646 pivot_mem_646 child_required_sub_646 child_envelope_sub_646 ?_
  intro b hb
  exact common_sub_646 (mem_commonEnvelope childrenD_646 b hb)
def required_653_i0 : Finset Cell := ⟨(([(2, 4), (3, 3), (3, 4), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_653_i0 : Finset Cell := ⟨(([(0, 4), (0, 5), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (2, 6), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 4), (5, 5), (5, 6), (5, 7), (6, 4), (6, 5), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_653_i0 : Fin 3 → Finset Cell := ![(placed21 1 (0, 3) required_206), (placed21 0 (2, 1) required_301), (placed21 5 (5, 3) required_405)]
def childrenD_653_i0 : Fin 3 → Finset Cell := ![(placed21 1 (0, 3) envelope_206), (placed21 0 (2, 1) envelope_301), (placed21 5 (5, 3) envelope_405)]
theorem common_sub_653_i0 : commonEnvelope childrenD_653_i0 ⊆ insert (4, 4) required_653_i0 := by decide +kernel
theorem child_required_sub_653_i0 : ∀ j, childrenC_653_i0 j ⊆ insert (4, 4) required_653_i0 := by decide +kernel
theorem child_envelope_sub_653_i0 : ∀ j, childrenD_653_i0 j ⊆ envelope_653_i0 := by decide +kernel
theorem pivot_mem_653_i0 : (4, 4) ∈ envelope_653_i0 := by decide +kernel
theorem children_work_653_i0 : ∀ j, Template HasSnaky 8 (childrenC_653_i0 j) (childrenD_653_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_206 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_301 0 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_405 5 (5, 3)).mono (by decide +kernel)
theorem row_works_653_i0 : Template HasSnaky 9 required_653_i0 envelope_653_i0 := by
  refine compose HasSnaky 8 childrenC_653_i0 childrenD_653_i0 children_work_653_i0 (4, 4)
    required_653_i0 envelope_653_i0 pivot_mem_653_i0 child_required_sub_653_i0 child_envelope_sub_653_i0 ?_
  intro b hb
  exact common_sub_653_i0 (mem_commonEnvelope childrenD_653_i0 b hb)
def required_653 : Finset Cell := ⟨(([(3, 3), (3, 4), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_653 : Finset Cell := ⟨(([(0, 4), (0, 5), (1, 2), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_653 : Fin 4 → Finset Cell := ![(placed21 3 (0, 4) required_53), (placed21 5 (6, 3) required_53), (placed21 0 (1, 0) required_652), required_653_i0]
def childrenD_653 : Fin 4 → Finset Cell := ![(placed21 3 (0, 4) envelope_53), (placed21 5 (6, 3) envelope_53), (placed21 0 (1, 0) envelope_652), envelope_653_i0]
theorem common_sub_653 : commonEnvelope childrenD_653 ⊆ insert (2, 4) required_653 := by decide +kernel
theorem child_required_sub_653 : ∀ j, childrenC_653 j ⊆ insert (2, 4) required_653 := by decide +kernel
theorem child_envelope_sub_653 : ∀ j, childrenD_653 j ⊆ envelope_653 := by decide +kernel
theorem pivot_mem_653 : (2, 4) ∈ envelope_653 := by decide +kernel
theorem children_work_653 : ∀ j, Template HasSnaky 10 (childrenC_653 j) (childrenD_653 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_53 3 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_53 5 (6, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_652 0 (1, 0)).mono (by decide +kernel)
  · exact row_works_653_i0.mono (by decide +kernel)
theorem row_works_653 : Template HasSnaky 11 required_653 envelope_653 := by
  refine compose HasSnaky 10 childrenC_653 childrenD_653 children_work_653 (2, 4)
    required_653 envelope_653 pivot_mem_653 child_required_sub_653 child_envelope_sub_653 ?_
  intro b hb
  exact common_sub_653 (mem_commonEnvelope childrenD_653 b hb)
def required_660_i1 : Finset Cell := ⟨(([(3, 5), (4, 4), (4, 5), (5, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_660_i1 : Finset Cell := ⟨(([(2, 6), (3, 5), (3, 6), (4, 4), (4, 5), (4, 6), (5, 4), (5, 5), (6, 5), (7, 5), (8, 4), (8, 5), (8, 6), (9, 4), (9, 5), (9, 6), (10, 4), (10, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_660_i1 : Fin 2 → Finset Cell := ![(placed21 5 (7, 5) required_6), (placed21 1 (4, 4) required_18)]
def childrenD_660_i1 : Fin 2 → Finset Cell := ![(placed21 5 (7, 5) envelope_6), (placed21 1 (4, 4) envelope_18)]
theorem common_sub_660_i1 : commonEnvelope childrenD_660_i1 ⊆ insert (7, 5) required_660_i1 := by decide +kernel
theorem child_required_sub_660_i1 : ∀ j, childrenC_660_i1 j ⊆ insert (7, 5) required_660_i1 := by decide +kernel
theorem child_envelope_sub_660_i1 : ∀ j, childrenD_660_i1 j ⊆ envelope_660_i1 := by decide +kernel
theorem pivot_mem_660_i1 : (7, 5) ∈ envelope_660_i1 := by decide +kernel
theorem children_work_660_i1 : ∀ j, Template HasSnaky 4 (childrenC_660_i1 j) (childrenD_660_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 5 (7, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_18 1 (4, 4)).mono (by decide +kernel)
theorem row_works_660_i1 : Template HasSnaky 5 required_660_i1 envelope_660_i1 := by
  refine compose HasSnaky 4 childrenC_660_i1 childrenD_660_i1 children_work_660_i1 (7, 5)
    required_660_i1 envelope_660_i1 pivot_mem_660_i1 child_required_sub_660_i1 child_envelope_sub_660_i1 ?_
  intro b hb
  exact common_sub_660_i1 (mem_commonEnvelope childrenD_660_i1 b hb)
def required_660_i2 : Finset Cell := ⟨(([(3, 5), (4, 4), (4, 5), (5, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_660_i2 : Finset Cell := ⟨(([(2, 6), (3, 5), (3, 6), (4, 4), (4, 5), (4, 6), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 4), (7, 5), (8, 5), (8, 6), (9, 5), (9, 6), (10, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_660_i2 : Fin 2 → Finset Cell := ![(placed21 5 (7, 5) required_6), (placed21 0 (3, 2) required_252)]
def childrenD_660_i2 : Fin 2 → Finset Cell := ![(placed21 5 (7, 5) envelope_6), (placed21 0 (3, 2) envelope_252)]
theorem common_sub_660_i2 : commonEnvelope childrenD_660_i2 ⊆ insert (7, 5) required_660_i2 := by decide +kernel
theorem child_required_sub_660_i2 : ∀ j, childrenC_660_i2 j ⊆ insert (7, 5) required_660_i2 := by decide +kernel
theorem child_envelope_sub_660_i2 : ∀ j, childrenD_660_i2 j ⊆ envelope_660_i2 := by decide +kernel
theorem pivot_mem_660_i2 : (7, 5) ∈ envelope_660_i2 := by decide +kernel
theorem children_work_660_i2 : ∀ j, Template HasSnaky 5 (childrenC_660_i2 j) (childrenD_660_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 5 (7, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_252 0 (3, 2)).mono (by decide +kernel)
theorem row_works_660_i2 : Template HasSnaky 6 required_660_i2 envelope_660_i2 := by
  refine compose HasSnaky 5 childrenC_660_i2 childrenD_660_i2 children_work_660_i2 (7, 5)
    required_660_i2 envelope_660_i2 pivot_mem_660_i2 child_required_sub_660_i2 child_envelope_sub_660_i2 ?_
  intro b hb
  exact common_sub_660_i2 (mem_commonEnvelope childrenD_660_i2 b hb)
def required_660_i0 : Finset Cell := ⟨(([(3, 5), (4, 4), (4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_660_i0 : Finset Cell := ⟨(([(2, 6), (3, 5), (3, 6), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 7), (7, 8), (7, 9), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (10, 2), (10, 4), (10, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_660_i0 : Fin 4 → Finset Cell := ![(placed21 3 (2, 6) required_9), required_660_i1, (placed21 0 (3, 0) required_659), required_660_i2]
def childrenD_660_i0 : Fin 4 → Finset Cell := ![(placed21 3 (2, 6) envelope_9), envelope_660_i1, (placed21 0 (3, 0) envelope_659), envelope_660_i2]
theorem common_sub_660_i0 : commonEnvelope childrenD_660_i0 ⊆ insert (6, 5) required_660_i0 := by decide +kernel
theorem child_required_sub_660_i0 : ∀ j, childrenC_660_i0 j ⊆ insert (6, 5) required_660_i0 := by decide +kernel
theorem child_envelope_sub_660_i0 : ∀ j, childrenD_660_i0 j ⊆ envelope_660_i0 := by decide +kernel
theorem pivot_mem_660_i0 : (6, 5) ∈ envelope_660_i0 := by decide +kernel
theorem children_work_660_i0 : ∀ j, Template HasSnaky 9 (childrenC_660_i0 j) (childrenD_660_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_9 3 (2, 6)).mono (by decide +kernel)
  · exact row_works_660_i1.mono (by decide +kernel)
  · exact (placed21_template row_works_659 0 (3, 0)).mono (by decide +kernel)
  · exact row_works_660_i2.mono (by decide +kernel)
theorem row_works_660_i0 : Template HasSnaky 10 required_660_i0 envelope_660_i0 := by
  refine compose HasSnaky 9 childrenC_660_i0 childrenD_660_i0 children_work_660_i0 (6, 5)
    required_660_i0 envelope_660_i0 pivot_mem_660_i0 child_required_sub_660_i0 child_envelope_sub_660_i0 ?_
  intro b hb
  exact common_sub_660_i0 (mem_commonEnvelope childrenD_660_i0 b hb)
def required_660 : Finset Cell := ⟨(([(4, 4), (4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_660 : Finset Cell := ⟨(([(0, 4), (0, 6), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 7), (7, 8), (7, 9), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (10, 2), (10, 4), (10, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_660 : Fin 4 → Finset Cell := ![(placed21 5 (7, 4) required_13), (placed21 2 (6, 3) required_137), (placed21 6 (6, 8) required_332), required_660_i0]
def childrenD_660 : Fin 4 → Finset Cell := ![(placed21 5 (7, 4) envelope_13), (placed21 2 (6, 3) envelope_137), (placed21 6 (6, 8) envelope_332), envelope_660_i0]
theorem common_sub_660 : commonEnvelope childrenD_660 ⊆ insert (3, 5) required_660 := by decide +kernel
theorem child_required_sub_660 : ∀ j, childrenC_660 j ⊆ insert (3, 5) required_660 := by decide +kernel
theorem child_envelope_sub_660 : ∀ j, childrenD_660 j ⊆ envelope_660 := by decide +kernel
theorem pivot_mem_660 : (3, 5) ∈ envelope_660 := by decide +kernel
theorem children_work_660 : ∀ j, Template HasSnaky 10 (childrenC_660 j) (childrenD_660 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 5 (7, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_137 2 (6, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_332 6 (6, 8)).mono (by decide +kernel)
  · exact row_works_660_i0.mono (by decide +kernel)
theorem row_works_660 : Template HasSnaky 11 required_660 envelope_660 := by
  refine compose HasSnaky 10 childrenC_660 childrenD_660 children_work_660 (3, 5)
    required_660 envelope_660 pivot_mem_660 child_required_sub_660 child_envelope_sub_660 ?_
  intro b hb
  exact common_sub_660 (mem_commonEnvelope childrenD_660 b hb)
def required_663 : Finset Cell := ⟨(([(2, 4), (2, 5), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_663 : Finset Cell := ⟨(([(0, 5), (1, 5), (1, 7), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 2), (8, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_663 : Fin 8 → Finset Cell := ![(placed21 4 (1, 7) required_134), (placed21 4 (1, 7) required_180), (placed21 4 (1, 8) required_435), (placed21 0 (1, 2) required_507), (placed21 4 (2, 7) required_558), (placed21 4 (1, 9) required_562), (placed21 0 (1, 3) required_580), required_662]
def childrenD_663 : Fin 8 → Finset Cell := ![(placed21 4 (1, 7) envelope_134), (placed21 4 (1, 7) envelope_180), (placed21 4 (1, 8) envelope_435), (placed21 0 (1, 2) envelope_507), (placed21 4 (2, 7) envelope_558), (placed21 4 (1, 9) envelope_562), (placed21 0 (1, 3) envelope_580), envelope_662]
theorem common_sub_663 : commonEnvelope childrenD_663 ⊆ insert (4, 5) required_663 := by decide +kernel
theorem child_required_sub_663 : ∀ j, childrenC_663 j ⊆ insert (4, 5) required_663 := by decide +kernel
theorem child_envelope_sub_663 : ∀ j, childrenD_663 j ⊆ envelope_663 := by decide +kernel
theorem pivot_mem_663 : (4, 5) ∈ envelope_663 := by decide +kernel
theorem children_work_663 : ∀ j, Template HasSnaky 10 (childrenC_663 j) (childrenD_663 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_134 4 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_180 4 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 4 (1, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_507 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_558 4 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_562 4 (1, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_580 0 (1, 3)).mono (by decide +kernel)
  · exact row_works_662.mono (by decide +kernel)
theorem row_works_663 : Template HasSnaky 11 required_663 envelope_663 := by
  refine compose HasSnaky 10 childrenC_663 childrenD_663 children_work_663 (4, 5)
    required_663 envelope_663 pivot_mem_663 child_required_sub_663 child_envelope_sub_663 ?_
  intro b hb
  exact common_sub_663 (mem_commonEnvelope childrenD_663 b hb)
def required_664 : Finset Cell := ⟨(([(4, 4), (4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_664 : Finset Cell := ⟨(([(0, 4), (0, 6), (1, 4), (1, 5), (1, 6), (2, 4), (2, 5), (2, 6), (3, 5), (3, 7), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (10, 2), (10, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_664 : Fin 7 → Finset Cell := ![(placed21 4 (3, 7) required_134), (placed21 4 (3, 7) required_180), (placed21 2 (7, 2) required_309), (placed21 4 (3, 8) required_435), (placed21 4 (4, 7) required_558), (placed21 0 (3, 3) required_580), (placed21 0 (2, 0) required_662)]
def childrenD_664 : Fin 7 → Finset Cell := ![(placed21 4 (3, 7) envelope_134), (placed21 4 (3, 7) envelope_180), (placed21 2 (7, 2) envelope_309), (placed21 4 (3, 8) envelope_435), (placed21 4 (4, 7) envelope_558), (placed21 0 (3, 3) envelope_580), (placed21 0 (2, 0) envelope_662)]
theorem common_sub_664 : commonEnvelope childrenD_664 ⊆ insert (6, 5) required_664 := by decide +kernel
theorem child_required_sub_664 : ∀ j, childrenC_664 j ⊆ insert (6, 5) required_664 := by decide +kernel
theorem child_envelope_sub_664 : ∀ j, childrenD_664 j ⊆ envelope_664 := by decide +kernel
theorem pivot_mem_664 : (6, 5) ∈ envelope_664 := by decide +kernel
theorem children_work_664 : ∀ j, Template HasSnaky 10 (childrenC_664 j) (childrenD_664 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_134 4 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_180 4 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_309 2 (7, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 4 (3, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_558 4 (4, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_580 0 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_662 0 (2, 0)).mono (by decide +kernel)
theorem row_works_664 : Template HasSnaky 11 required_664 envelope_664 := by
  refine compose HasSnaky 10 childrenC_664 childrenD_664 children_work_664 (6, 5)
    required_664 envelope_664 pivot_mem_664 child_required_sub_664 child_envelope_sub_664 ?_
  intro b hb
  exact common_sub_664 (mem_commonEnvelope childrenD_664 b hb)
def required_676_i0 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_676_i0 : Finset Cell := ⟨(([(0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 2), (5, 4), (5, 5), (5, 6), (5, 7), (6, 4), (6, 5), (6, 6), (7, 4), (7, 5), (7, 6), (8, 4), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_676_i0 : Fin 2 → Finset Cell := ![(placed21 6 (4, 6) required_55), (placed21 0 (1, 2) required_380)]
def childrenD_676_i0 : Fin 2 → Finset Cell := ![(placed21 6 (4, 6) envelope_55), (placed21 0 (1, 2) envelope_380)]
theorem common_sub_676_i0 : commonEnvelope childrenD_676_i0 ⊆ insert (2, 4) required_676_i0 := by decide +kernel
theorem child_required_sub_676_i0 : ∀ j, childrenC_676_i0 j ⊆ insert (2, 4) required_676_i0 := by decide +kernel
theorem child_envelope_sub_676_i0 : ∀ j, childrenD_676_i0 j ⊆ envelope_676_i0 := by decide +kernel
theorem pivot_mem_676_i0 : (2, 4) ∈ envelope_676_i0 := by decide +kernel
theorem children_work_676_i0 : ∀ j, Template HasSnaky 9 (childrenC_676_i0 j) (childrenD_676_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_55 6 (4, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_380 0 (1, 2)).mono (by decide +kernel)
theorem row_works_676_i0 : Template HasSnaky 10 required_676_i0 envelope_676_i0 := by
  refine compose HasSnaky 9 childrenC_676_i0 childrenD_676_i0 children_work_676_i0 (2, 4)
    required_676_i0 envelope_676_i0 pivot_mem_676_i0 child_required_sub_676_i0 child_envelope_sub_676_i0 ?_
  intro b hb
  exact common_sub_676_i0 (mem_commonEnvelope childrenD_676_i0 b hb)
def required_676 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_676 : Finset Cell := ⟨(([(0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 4), (6, 5), (6, 6), (7, 4), (7, 5), (7, 6), (8, 4), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_676 : Fin 4 → Finset Cell := ![(placed21 3 (0, 3) required_7), (placed21 0 (1, 2) required_8), (placed21 1 (0, 2) required_9), required_676_i0]
def childrenD_676 : Fin 4 → Finset Cell := ![(placed21 3 (0, 3) envelope_7), (placed21 0 (1, 2) envelope_8), (placed21 1 (0, 2) envelope_9), envelope_676_i0]
theorem common_sub_676 : commonEnvelope childrenD_676 ⊆ insert (4, 3) required_676 := by decide +kernel
theorem child_required_sub_676 : ∀ j, childrenC_676 j ⊆ insert (4, 3) required_676 := by decide +kernel
theorem child_envelope_sub_676 : ∀ j, childrenD_676 j ⊆ envelope_676 := by decide +kernel
theorem pivot_mem_676 : (4, 3) ∈ envelope_676 := by decide +kernel
theorem children_work_676 : ∀ j, Template HasSnaky 10 (childrenC_676 j) (childrenD_676 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 3 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 1 (0, 2)).mono (by decide +kernel)
  · exact row_works_676_i0.mono (by decide +kernel)
theorem row_works_676 : Template HasSnaky 11 required_676 envelope_676 := by
  refine compose HasSnaky 10 childrenC_676 childrenD_676 children_work_676 (4, 3)
    required_676 envelope_676 pivot_mem_676 child_required_sub_676 child_envelope_sub_676 ?_
  intro b hb
  exact common_sub_676 (mem_commonEnvelope childrenD_676 b hb)
def required_685_i4 : Finset Cell := ⟨(([(2, 1), (3, 2), (3, 3), (3, 4), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_685_i4 : Finset Cell := ⟨(([(2, 0), (2, 1), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1), (6, 2), (7, 0), (7, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_685_i4 : Fin 2 → Finset Cell := ![(placed21 7 (3, 4) required_5), (placed21 0 (2, 0) required_312)]
def childrenD_685_i4 : Fin 2 → Finset Cell := ![(placed21 7 (3, 4) envelope_5), (placed21 0 (2, 0) envelope_312)]
theorem common_sub_685_i4 : commonEnvelope childrenD_685_i4 ⊆ insert (3, 1) required_685_i4 := by decide +kernel
theorem child_required_sub_685_i4 : ∀ j, childrenC_685_i4 j ⊆ insert (3, 1) required_685_i4 := by decide +kernel
theorem child_envelope_sub_685_i4 : ∀ j, childrenD_685_i4 j ⊆ envelope_685_i4 := by decide +kernel
theorem pivot_mem_685_i4 : (3, 1) ∈ envelope_685_i4 := by decide +kernel
theorem children_work_685_i4 : ∀ j, Template HasSnaky 5 (childrenC_685_i4 j) (childrenD_685_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_312 0 (2, 0)).mono (by decide +kernel)
theorem row_works_685_i4 : Template HasSnaky 6 required_685_i4 envelope_685_i4 := by
  refine compose HasSnaky 5 childrenC_685_i4 childrenD_685_i4 children_work_685_i4 (3, 1)
    required_685_i4 envelope_685_i4 pivot_mem_685_i4 child_required_sub_685_i4 child_envelope_sub_685_i4 ?_
  intro b hb
  exact common_sub_685_i4 (mem_commonEnvelope childrenD_685_i4 b hb)
def required_685_i3 : Finset Cell := ⟨(([(3, 2), (3, 3), (3, 4), (3, 5), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_685_i3 : Finset Cell := ⟨(([(2, 0), (2, 1), (2, 2), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1), (6, 2), (7, 0), (7, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_685_i3 : Fin 2 → Finset Cell := ![(placed21 7 (3, 5) required_4), required_685_i4]
def childrenD_685_i3 : Fin 2 → Finset Cell := ![(placed21 7 (3, 5) envelope_4), envelope_685_i4]
theorem common_sub_685_i3 : commonEnvelope childrenD_685_i3 ⊆ insert (2, 1) required_685_i3 := by decide +kernel
theorem child_required_sub_685_i3 : ∀ j, childrenC_685_i3 j ⊆ insert (2, 1) required_685_i3 := by decide +kernel
theorem child_envelope_sub_685_i3 : ∀ j, childrenD_685_i3 j ⊆ envelope_685_i3 := by decide +kernel
theorem pivot_mem_685_i3 : (2, 1) ∈ envelope_685_i3 := by decide +kernel
theorem children_work_685_i3 : ∀ j, Template HasSnaky 6 (childrenC_685_i3 j) (childrenD_685_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 7 (3, 5)).mono (by decide +kernel)
  · exact row_works_685_i4.mono (by decide +kernel)
theorem row_works_685_i3 : Template HasSnaky 7 required_685_i3 envelope_685_i3 := by
  refine compose HasSnaky 6 childrenC_685_i3 childrenD_685_i3 children_work_685_i3 (2, 1)
    required_685_i3 envelope_685_i3 pivot_mem_685_i3 child_required_sub_685_i3 child_envelope_sub_685_i3 ?_
  intro b hb
  exact common_sub_685_i3 (mem_commonEnvelope childrenD_685_i3 b hb)
def required_685_i2 : Finset Cell := ⟨(([(3, 2), (3, 3), (3, 4), (3, 5), (4, 5), (5, 5), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_685_i2 : Finset Cell := ⟨(([(2, 0), (2, 1), (2, 2), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 5), (5, 0), (5, 1), (5, 2), (5, 5), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 0), (7, 2), (7, 4), (7, 5), (7, 6), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_685_i2 : Fin 2 → Finset Cell := ![(placed21 4 (3, 6) required_351), required_685_i3]
def childrenD_685_i2 : Fin 2 → Finset Cell := ![(placed21 4 (3, 6) envelope_351), envelope_685_i3]
theorem common_sub_685_i2 : commonEnvelope childrenD_685_i2 ⊆ insert (6, 2) required_685_i2 := by decide +kernel
theorem child_required_sub_685_i2 : ∀ j, childrenC_685_i2 j ⊆ insert (6, 2) required_685_i2 := by decide +kernel
theorem child_envelope_sub_685_i2 : ∀ j, childrenD_685_i2 j ⊆ envelope_685_i2 := by decide +kernel
theorem pivot_mem_685_i2 : (6, 2) ∈ envelope_685_i2 := by decide +kernel
theorem children_work_685_i2 : ∀ j, Template HasSnaky 7 (childrenC_685_i2 j) (childrenD_685_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_351 4 (3, 6)).mono (by decide +kernel)
  · exact row_works_685_i3.mono (by decide +kernel)
theorem row_works_685_i2 : Template HasSnaky 8 required_685_i2 envelope_685_i2 := by
  refine compose HasSnaky 7 childrenC_685_i2 childrenD_685_i2 children_work_685_i2 (6, 2)
    required_685_i2 envelope_685_i2 pivot_mem_685_i2 child_required_sub_685_i2 child_envelope_sub_685_i2 ?_
  intro b hb
  exact common_sub_685_i2 (mem_commonEnvelope childrenD_685_i2 b hb)
def required_685_i1 : Finset Cell := ⟨(([(3, 2), (3, 3), (3, 4), (3, 5), (4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_685_i1 : Finset Cell := ⟨(([(2, 0), (2, 1), (2, 2), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 5), (5, 0), (5, 1), (5, 2), (5, 4), (5, 5), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 0), (7, 2), (7, 4), (7, 5), (7, 6), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_685_i1 : Fin 2 → Finset Cell := ![(placed21 1 (2, 2) required_96), required_685_i2]
def childrenD_685_i1 : Fin 2 → Finset Cell := ![(placed21 1 (2, 2) envelope_96), envelope_685_i2]
theorem common_sub_685_i1 : commonEnvelope childrenD_685_i1 ⊆ insert (6, 4) required_685_i1 := by decide +kernel
theorem child_required_sub_685_i1 : ∀ j, childrenC_685_i1 j ⊆ insert (6, 4) required_685_i1 := by decide +kernel
theorem child_envelope_sub_685_i1 : ∀ j, childrenD_685_i1 j ⊆ envelope_685_i1 := by decide +kernel
theorem pivot_mem_685_i1 : (6, 4) ∈ envelope_685_i1 := by decide +kernel
theorem children_work_685_i1 : ∀ j, Template HasSnaky 8 (childrenC_685_i1 j) (childrenD_685_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_96 1 (2, 2)).mono (by decide +kernel)
  · exact row_works_685_i2.mono (by decide +kernel)
theorem row_works_685_i1 : Template HasSnaky 9 required_685_i1 envelope_685_i1 := by
  refine compose HasSnaky 8 childrenC_685_i1 childrenD_685_i1 children_work_685_i1 (6, 4)
    required_685_i1 envelope_685_i1 pivot_mem_685_i1 child_required_sub_685_i1 child_envelope_sub_685_i1 ?_
  intro b hb
  exact common_sub_685_i1 (mem_commonEnvelope childrenD_685_i1 b hb)
def required_685_i0 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_685_i0 : Finset Cell := ⟨(([(2, 0), (2, 1), (2, 2), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 4), (5, 5), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 0), (7, 2), (7, 4), (7, 5), (7, 6), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_685_i0 : Fin 2 → Finset Cell := ![(placed21 1 (3, 2) required_5), required_685_i1]
def childrenD_685_i0 : Fin 2 → Finset Cell := ![(placed21 1 (3, 2) envelope_5), envelope_685_i1]
theorem common_sub_685_i0 : commonEnvelope childrenD_685_i0 ⊆ insert (3, 2) required_685_i0 := by decide +kernel
theorem child_required_sub_685_i0 : ∀ j, childrenC_685_i0 j ⊆ insert (3, 2) required_685_i0 := by decide +kernel
theorem child_envelope_sub_685_i0 : ∀ j, childrenD_685_i0 j ⊆ envelope_685_i0 := by decide +kernel
theorem pivot_mem_685_i0 : (3, 2) ∈ envelope_685_i0 := by decide +kernel
theorem children_work_685_i0 : ∀ j, Template HasSnaky 9 (childrenC_685_i0 j) (childrenD_685_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (3, 2)).mono (by decide +kernel)
  · exact row_works_685_i1.mono (by decide +kernel)
theorem row_works_685_i0 : Template HasSnaky 10 required_685_i0 envelope_685_i0 := by
  refine compose HasSnaky 9 childrenC_685_i0 childrenD_685_i0 children_work_685_i0 (3, 2)
    required_685_i0 envelope_685_i0 pivot_mem_685_i0 child_required_sub_685_i0 child_envelope_sub_685_i0 ?_
  intro b hb
  exact common_sub_685_i0 (mem_commonEnvelope childrenD_685_i0 b hb)
def required_685 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_685 : Finset Cell := ⟨(([(0, 6), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 0), (7, 2), (7, 4), (7, 5), (7, 6), (7, 7), (8, 4), (8, 5), (8, 6), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_685 : Fin 6 → Finset Cell := ![(placed21 3 (1, 6) required_67), (placed21 7 (7, 6) required_175), (placed21 0 (2, 2) required_228), (placed21 4 (2, 8) required_435), (placed21 0 (3, 2) required_531), required_685_i0]
def childrenD_685 : Fin 6 → Finset Cell := ![(placed21 3 (1, 6) envelope_67), (placed21 7 (7, 6) envelope_175), (placed21 0 (2, 2) envelope_228), (placed21 4 (2, 8) envelope_435), (placed21 0 (3, 2) envelope_531), envelope_685_i0]
theorem common_sub_685 : commonEnvelope childrenD_685 ⊆ insert (5, 5) required_685 := by decide +kernel
theorem child_required_sub_685 : ∀ j, childrenC_685 j ⊆ insert (5, 5) required_685 := by decide +kernel
theorem child_envelope_sub_685 : ∀ j, childrenD_685 j ⊆ envelope_685 := by decide +kernel
theorem pivot_mem_685 : (5, 5) ∈ envelope_685 := by decide +kernel
theorem children_work_685 : ∀ j, Template HasSnaky 10 (childrenC_685 j) (childrenD_685 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_67 3 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_175 7 (7, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_228 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 4 (2, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_531 0 (3, 2)).mono (by decide +kernel)
  · exact row_works_685_i0.mono (by decide +kernel)
theorem row_works_685 : Template HasSnaky 11 required_685 envelope_685 := by
  refine compose HasSnaky 10 childrenC_685 childrenD_685 children_work_685 (5, 5)
    required_685 envelope_685 pivot_mem_685 child_required_sub_685 child_envelope_sub_685 ?_
  intro b hb
  exact common_sub_685 (mem_commonEnvelope childrenD_685 b hb)
def height_639_i2 : ℕ := 4
def childrenH_639_i2 : Fin 3 → ℕ := ![height_21, height_37, height_62]
theorem height_exact_639_i2 : height_639_i2 = 1 + Finset.univ.sup childrenH_639_i2 := by decide +kernel
theorem required_origin_639_i2 : ∀ x ∈ required_639_i2,
    (∃ j, x ∈ childrenC_639_i2 j) ∨ ∀ j, x ∈ childrenD_639_i2 j := by decide +kernel
theorem required_exact_639_i2 : required_639_i2 =
    ((Finset.univ.biUnion childrenC_639_i2) ∪ commonEnvelope childrenD_639_i2).erase (3, 6) := by
  exact required_eq_combination childrenC_639_i2 childrenD_639_i2 (3, 6) required_639_i2
    (by decide +kernel) child_required_sub_639_i2 common_sub_639_i2 required_origin_639_i2
theorem envelope_origin_639_i2 : ∀ x ∈ envelope_639_i2,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_639_i2 j := by decide +kernel
theorem envelope_exact_639_i2 : envelope_639_i2 =
    insert (3, 6) (Finset.univ.biUnion childrenD_639_i2) := by
  exact envelope_eq_combination childrenD_639_i2 (3, 6) envelope_639_i2
    pivot_mem_639_i2 child_envelope_sub_639_i2 envelope_origin_639_i2
def checked_639_i2 : CheckedCard where
  required := required_639_i2
  envelope := envelope_639_i2
  height := height_639_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_639_i2
def height_639_i1 : ℕ := 6
def childrenH_639_i1 : Fin 4 → ℕ := ![height_71, height_73, height_639_i2, height_451]
theorem height_exact_639_i1 : height_639_i1 = 1 + Finset.univ.sup childrenH_639_i1 := by decide +kernel
theorem required_origin_639_i1 : ∀ x ∈ required_639_i1,
    (∃ j, x ∈ childrenC_639_i1 j) ∨ ∀ j, x ∈ childrenD_639_i1 j := by decide +kernel
theorem required_exact_639_i1 : required_639_i1 =
    ((Finset.univ.biUnion childrenC_639_i1) ∪ commonEnvelope childrenD_639_i1).erase (3, 5) := by
  exact required_eq_combination childrenC_639_i1 childrenD_639_i1 (3, 5) required_639_i1
    (by decide +kernel) child_required_sub_639_i1 common_sub_639_i1 required_origin_639_i1
theorem envelope_origin_639_i1 : ∀ x ∈ envelope_639_i1,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_639_i1 j := by decide +kernel
theorem envelope_exact_639_i1 : envelope_639_i1 =
    insert (3, 5) (Finset.univ.biUnion childrenD_639_i1) := by
  exact envelope_eq_combination childrenD_639_i1 (3, 5) envelope_639_i1
    pivot_mem_639_i1 child_envelope_sub_639_i1 envelope_origin_639_i1
def checked_639_i1 : CheckedCard where
  required := required_639_i1
  envelope := envelope_639_i1
  height := height_639_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_639_i1
def height_639_i3 : ℕ := 7
def childrenH_639_i3 : Fin 4 → ℕ := ![height_71, height_73, height_435, height_451]
theorem height_exact_639_i3 : height_639_i3 = 1 + Finset.univ.sup childrenH_639_i3 := by decide +kernel
theorem required_origin_639_i3 : ∀ x ∈ required_639_i3,
    (∃ j, x ∈ childrenC_639_i3 j) ∨ ∀ j, x ∈ childrenD_639_i3 j := by decide +kernel
theorem required_exact_639_i3 : required_639_i3 =
    ((Finset.univ.biUnion childrenC_639_i3) ∪ commonEnvelope childrenD_639_i3).erase (3, 5) := by
  exact required_eq_combination childrenC_639_i3 childrenD_639_i3 (3, 5) required_639_i3
    (by decide +kernel) child_required_sub_639_i3 common_sub_639_i3 required_origin_639_i3
theorem envelope_origin_639_i3 : ∀ x ∈ envelope_639_i3,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_639_i3 j := by decide +kernel
theorem envelope_exact_639_i3 : envelope_639_i3 =
    insert (3, 5) (Finset.univ.biUnion childrenD_639_i3) := by
  exact envelope_eq_combination childrenD_639_i3 (3, 5) envelope_639_i3
    pivot_mem_639_i3 child_envelope_sub_639_i3 envelope_origin_639_i3
def checked_639_i3 : CheckedCard where
  required := required_639_i3
  envelope := envelope_639_i3
  height := height_639_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_639_i3
def height_639_i0 : ℕ := 10
def childrenH_639_i0 : Fin 4 → ℕ := ![height_54, height_638, height_639_i1, height_639_i3]
theorem height_exact_639_i0 : height_639_i0 = 1 + Finset.univ.sup childrenH_639_i0 := by decide +kernel
theorem required_origin_639_i0 : ∀ x ∈ required_639_i0,
    (∃ j, x ∈ childrenC_639_i0 j) ∨ ∀ j, x ∈ childrenD_639_i0 j := by decide +kernel
theorem required_exact_639_i0 : required_639_i0 =
    ((Finset.univ.biUnion childrenC_639_i0) ∪ commonEnvelope childrenD_639_i0).erase (3, 3) := by
  exact required_eq_combination childrenC_639_i0 childrenD_639_i0 (3, 3) required_639_i0
    (by decide +kernel) child_required_sub_639_i0 common_sub_639_i0 required_origin_639_i0
theorem envelope_origin_639_i0 : ∀ x ∈ envelope_639_i0,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_639_i0 j := by decide +kernel
theorem envelope_exact_639_i0 : envelope_639_i0 =
    insert (3, 3) (Finset.univ.biUnion childrenD_639_i0) := by
  exact envelope_eq_combination childrenD_639_i0 (3, 3) envelope_639_i0
    pivot_mem_639_i0 child_envelope_sub_639_i0 envelope_origin_639_i0
def checked_639_i0 : CheckedCard where
  required := required_639_i0
  envelope := envelope_639_i0
  height := height_639_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_639_i0
def height_639 : ℕ := 11
def childrenH_639 : Fin 5 → ℕ := ![height_50, height_125, height_478, height_482, height_639_i0]
theorem height_exact_639 : height_639 = 1 + Finset.univ.sup childrenH_639 := by decide +kernel
theorem required_origin_639 : ∀ x ∈ required_639,
    (∃ j, x ∈ childrenC_639 j) ∨ ∀ j, x ∈ childrenD_639 j := by decide +kernel
theorem required_exact_639 : required_639 =
    ((Finset.univ.biUnion childrenC_639) ∪ commonEnvelope childrenD_639).erase (3, 4) := by
  exact required_eq_combination childrenC_639 childrenD_639 (3, 4) required_639
    (by decide +kernel) child_required_sub_639 common_sub_639 required_origin_639
theorem envelope_origin_639 : ∀ x ∈ envelope_639,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_639 j := by decide +kernel
theorem envelope_exact_639 : envelope_639 =
    insert (3, 4) (Finset.univ.biUnion childrenD_639) := by
  exact envelope_eq_combination childrenD_639 (3, 4) envelope_639
    pivot_mem_639 child_envelope_sub_639 envelope_origin_639
def checked_639 : CheckedCard where
  required := required_639
  envelope := envelope_639
  height := height_639
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_639
def height_646_i0 : ℕ := 6
def childrenH_646_i0 : Fin 3 → ℕ := ![height_15, height_72, height_262]
theorem height_exact_646_i0 : height_646_i0 = 1 + Finset.univ.sup childrenH_646_i0 := by decide +kernel
theorem required_origin_646_i0 : ∀ x ∈ required_646_i0,
    (∃ j, x ∈ childrenC_646_i0 j) ∨ ∀ j, x ∈ childrenD_646_i0 j := by decide +kernel
theorem required_exact_646_i0 : required_646_i0 =
    ((Finset.univ.biUnion childrenC_646_i0) ∪ commonEnvelope childrenD_646_i0).erase (4, 2) := by
  exact required_eq_combination childrenC_646_i0 childrenD_646_i0 (4, 2) required_646_i0
    (by decide +kernel) child_required_sub_646_i0 common_sub_646_i0 required_origin_646_i0
theorem envelope_origin_646_i0 : ∀ x ∈ envelope_646_i0,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_646_i0 j := by decide +kernel
theorem envelope_exact_646_i0 : envelope_646_i0 =
    insert (4, 2) (Finset.univ.biUnion childrenD_646_i0) := by
  exact envelope_eq_combination childrenD_646_i0 (4, 2) envelope_646_i0
    pivot_mem_646_i0 child_envelope_sub_646_i0 envelope_origin_646_i0
def checked_646_i0 : CheckedCard where
  required := required_646_i0
  envelope := envelope_646_i0
  height := height_646_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_646_i0
def height_646 : ℕ := 11
def childrenH_646 : Fin 6 → ℕ := ![height_361, height_361, height_411, height_600, height_621, height_646_i0]
theorem height_exact_646 : height_646 = 1 + Finset.univ.sup childrenH_646 := by decide +kernel
theorem required_origin_646 : ∀ x ∈ required_646,
    (∃ j, x ∈ childrenC_646 j) ∨ ∀ j, x ∈ childrenD_646 j := by decide +kernel
theorem required_exact_646 : required_646 =
    ((Finset.univ.biUnion childrenC_646) ∪ commonEnvelope childrenD_646).erase (4, 4) := by
  exact required_eq_combination childrenC_646 childrenD_646 (4, 4) required_646
    (by decide +kernel) child_required_sub_646 common_sub_646 required_origin_646
theorem envelope_origin_646 : ∀ x ∈ envelope_646,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_646 j := by decide +kernel
theorem envelope_exact_646 : envelope_646 =
    insert (4, 4) (Finset.univ.biUnion childrenD_646) := by
  exact envelope_eq_combination childrenD_646 (4, 4) envelope_646
    pivot_mem_646 child_envelope_sub_646 envelope_origin_646
def checked_646 : CheckedCard where
  required := required_646
  envelope := envelope_646
  height := height_646
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_646
def height_653_i0 : ℕ := 9
def childrenH_653_i0 : Fin 3 → ℕ := ![height_206, height_301, height_405]
theorem height_exact_653_i0 : height_653_i0 = 1 + Finset.univ.sup childrenH_653_i0 := by decide +kernel
theorem required_origin_653_i0 : ∀ x ∈ required_653_i0,
    (∃ j, x ∈ childrenC_653_i0 j) ∨ ∀ j, x ∈ childrenD_653_i0 j := by decide +kernel
theorem required_exact_653_i0 : required_653_i0 =
    ((Finset.univ.biUnion childrenC_653_i0) ∪ commonEnvelope childrenD_653_i0).erase (4, 4) := by
  exact required_eq_combination childrenC_653_i0 childrenD_653_i0 (4, 4) required_653_i0
    (by decide +kernel) child_required_sub_653_i0 common_sub_653_i0 required_origin_653_i0
theorem envelope_origin_653_i0 : ∀ x ∈ envelope_653_i0,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_653_i0 j := by decide +kernel
theorem envelope_exact_653_i0 : envelope_653_i0 =
    insert (4, 4) (Finset.univ.biUnion childrenD_653_i0) := by
  exact envelope_eq_combination childrenD_653_i0 (4, 4) envelope_653_i0
    pivot_mem_653_i0 child_envelope_sub_653_i0 envelope_origin_653_i0
def checked_653_i0 : CheckedCard where
  required := required_653_i0
  envelope := envelope_653_i0
  height := height_653_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_653_i0
def height_653 : ℕ := 11
def childrenH_653 : Fin 4 → ℕ := ![height_53, height_53, height_652, height_653_i0]
theorem height_exact_653 : height_653 = 1 + Finset.univ.sup childrenH_653 := by decide +kernel
theorem required_origin_653 : ∀ x ∈ required_653,
    (∃ j, x ∈ childrenC_653 j) ∨ ∀ j, x ∈ childrenD_653 j := by decide +kernel
theorem required_exact_653 : required_653 =
    ((Finset.univ.biUnion childrenC_653) ∪ commonEnvelope childrenD_653).erase (2, 4) := by
  exact required_eq_combination childrenC_653 childrenD_653 (2, 4) required_653
    (by decide +kernel) child_required_sub_653 common_sub_653 required_origin_653
theorem envelope_origin_653 : ∀ x ∈ envelope_653,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_653 j := by decide +kernel
theorem envelope_exact_653 : envelope_653 =
    insert (2, 4) (Finset.univ.biUnion childrenD_653) := by
  exact envelope_eq_combination childrenD_653 (2, 4) envelope_653
    pivot_mem_653 child_envelope_sub_653 envelope_origin_653
def checked_653 : CheckedCard where
  required := required_653
  envelope := envelope_653
  height := height_653
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_653
def height_660_i1 : ℕ := 5
def childrenH_660_i1 : Fin 2 → ℕ := ![height_6, height_18]
theorem height_exact_660_i1 : height_660_i1 = 1 + Finset.univ.sup childrenH_660_i1 := by decide +kernel
theorem required_origin_660_i1 : ∀ x ∈ required_660_i1,
    (∃ j, x ∈ childrenC_660_i1 j) ∨ ∀ j, x ∈ childrenD_660_i1 j := by decide +kernel
theorem required_exact_660_i1 : required_660_i1 =
    ((Finset.univ.biUnion childrenC_660_i1) ∪ commonEnvelope childrenD_660_i1).erase (7, 5) := by
  exact required_eq_combination childrenC_660_i1 childrenD_660_i1 (7, 5) required_660_i1
    (by decide +kernel) child_required_sub_660_i1 common_sub_660_i1 required_origin_660_i1
theorem envelope_origin_660_i1 : ∀ x ∈ envelope_660_i1,
    x = (7, 5) ∨ ∃ j, x ∈ childrenD_660_i1 j := by decide +kernel
theorem envelope_exact_660_i1 : envelope_660_i1 =
    insert (7, 5) (Finset.univ.biUnion childrenD_660_i1) := by
  exact envelope_eq_combination childrenD_660_i1 (7, 5) envelope_660_i1
    pivot_mem_660_i1 child_envelope_sub_660_i1 envelope_origin_660_i1
def checked_660_i1 : CheckedCard where
  required := required_660_i1
  envelope := envelope_660_i1
  height := height_660_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_660_i1
def height_660_i2 : ℕ := 6
def childrenH_660_i2 : Fin 2 → ℕ := ![height_6, height_252]
theorem height_exact_660_i2 : height_660_i2 = 1 + Finset.univ.sup childrenH_660_i2 := by decide +kernel
theorem required_origin_660_i2 : ∀ x ∈ required_660_i2,
    (∃ j, x ∈ childrenC_660_i2 j) ∨ ∀ j, x ∈ childrenD_660_i2 j := by decide +kernel
theorem required_exact_660_i2 : required_660_i2 =
    ((Finset.univ.biUnion childrenC_660_i2) ∪ commonEnvelope childrenD_660_i2).erase (7, 5) := by
  exact required_eq_combination childrenC_660_i2 childrenD_660_i2 (7, 5) required_660_i2
    (by decide +kernel) child_required_sub_660_i2 common_sub_660_i2 required_origin_660_i2
theorem envelope_origin_660_i2 : ∀ x ∈ envelope_660_i2,
    x = (7, 5) ∨ ∃ j, x ∈ childrenD_660_i2 j := by decide +kernel
theorem envelope_exact_660_i2 : envelope_660_i2 =
    insert (7, 5) (Finset.univ.biUnion childrenD_660_i2) := by
  exact envelope_eq_combination childrenD_660_i2 (7, 5) envelope_660_i2
    pivot_mem_660_i2 child_envelope_sub_660_i2 envelope_origin_660_i2
def checked_660_i2 : CheckedCard where
  required := required_660_i2
  envelope := envelope_660_i2
  height := height_660_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_660_i2
def height_660_i0 : ℕ := 10
def childrenH_660_i0 : Fin 4 → ℕ := ![height_9, height_660_i1, height_659, height_660_i2]
theorem height_exact_660_i0 : height_660_i0 = 1 + Finset.univ.sup childrenH_660_i0 := by decide +kernel
theorem required_origin_660_i0 : ∀ x ∈ required_660_i0,
    (∃ j, x ∈ childrenC_660_i0 j) ∨ ∀ j, x ∈ childrenD_660_i0 j := by decide +kernel
theorem required_exact_660_i0 : required_660_i0 =
    ((Finset.univ.biUnion childrenC_660_i0) ∪ commonEnvelope childrenD_660_i0).erase (6, 5) := by
  exact required_eq_combination childrenC_660_i0 childrenD_660_i0 (6, 5) required_660_i0
    (by decide +kernel) child_required_sub_660_i0 common_sub_660_i0 required_origin_660_i0
theorem envelope_origin_660_i0 : ∀ x ∈ envelope_660_i0,
    x = (6, 5) ∨ ∃ j, x ∈ childrenD_660_i0 j := by decide +kernel
theorem envelope_exact_660_i0 : envelope_660_i0 =
    insert (6, 5) (Finset.univ.biUnion childrenD_660_i0) := by
  exact envelope_eq_combination childrenD_660_i0 (6, 5) envelope_660_i0
    pivot_mem_660_i0 child_envelope_sub_660_i0 envelope_origin_660_i0
def checked_660_i0 : CheckedCard where
  required := required_660_i0
  envelope := envelope_660_i0
  height := height_660_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_660_i0
def height_660 : ℕ := 11
def childrenH_660 : Fin 4 → ℕ := ![height_13, height_137, height_332, height_660_i0]
theorem height_exact_660 : height_660 = 1 + Finset.univ.sup childrenH_660 := by decide +kernel
theorem required_origin_660 : ∀ x ∈ required_660,
    (∃ j, x ∈ childrenC_660 j) ∨ ∀ j, x ∈ childrenD_660 j := by decide +kernel
theorem required_exact_660 : required_660 =
    ((Finset.univ.biUnion childrenC_660) ∪ commonEnvelope childrenD_660).erase (3, 5) := by
  exact required_eq_combination childrenC_660 childrenD_660 (3, 5) required_660
    (by decide +kernel) child_required_sub_660 common_sub_660 required_origin_660
theorem envelope_origin_660 : ∀ x ∈ envelope_660,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_660 j := by decide +kernel
theorem envelope_exact_660 : envelope_660 =
    insert (3, 5) (Finset.univ.biUnion childrenD_660) := by
  exact envelope_eq_combination childrenD_660 (3, 5) envelope_660
    pivot_mem_660 child_envelope_sub_660 envelope_origin_660
def checked_660 : CheckedCard where
  required := required_660
  envelope := envelope_660
  height := height_660
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_660
def height_663 : ℕ := 11
def childrenH_663 : Fin 8 → ℕ := ![height_134, height_180, height_435, height_507, height_558, height_562, height_580, height_662]
theorem height_exact_663 : height_663 = 1 + Finset.univ.sup childrenH_663 := by decide +kernel
theorem required_origin_663 : ∀ x ∈ required_663,
    (∃ j, x ∈ childrenC_663 j) ∨ ∀ j, x ∈ childrenD_663 j := by decide +kernel
theorem required_exact_663 : required_663 =
    ((Finset.univ.biUnion childrenC_663) ∪ commonEnvelope childrenD_663).erase (4, 5) := by
  exact required_eq_combination childrenC_663 childrenD_663 (4, 5) required_663
    (by decide +kernel) child_required_sub_663 common_sub_663 required_origin_663
theorem envelope_origin_663 : ∀ x ∈ envelope_663,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_663 j := by decide +kernel
theorem envelope_exact_663 : envelope_663 =
    insert (4, 5) (Finset.univ.biUnion childrenD_663) := by
  exact envelope_eq_combination childrenD_663 (4, 5) envelope_663
    pivot_mem_663 child_envelope_sub_663 envelope_origin_663
def checked_663 : CheckedCard where
  required := required_663
  envelope := envelope_663
  height := height_663
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_663
def height_664 : ℕ := 11
def childrenH_664 : Fin 7 → ℕ := ![height_134, height_180, height_309, height_435, height_558, height_580, height_662]
theorem height_exact_664 : height_664 = 1 + Finset.univ.sup childrenH_664 := by decide +kernel
theorem required_origin_664 : ∀ x ∈ required_664,
    (∃ j, x ∈ childrenC_664 j) ∨ ∀ j, x ∈ childrenD_664 j := by decide +kernel
theorem required_exact_664 : required_664 =
    ((Finset.univ.biUnion childrenC_664) ∪ commonEnvelope childrenD_664).erase (6, 5) := by
  exact required_eq_combination childrenC_664 childrenD_664 (6, 5) required_664
    (by decide +kernel) child_required_sub_664 common_sub_664 required_origin_664
theorem envelope_origin_664 : ∀ x ∈ envelope_664,
    x = (6, 5) ∨ ∃ j, x ∈ childrenD_664 j := by decide +kernel
theorem envelope_exact_664 : envelope_664 =
    insert (6, 5) (Finset.univ.biUnion childrenD_664) := by
  exact envelope_eq_combination childrenD_664 (6, 5) envelope_664
    pivot_mem_664 child_envelope_sub_664 envelope_origin_664
def checked_664 : CheckedCard where
  required := required_664
  envelope := envelope_664
  height := height_664
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_664
def height_676_i0 : ℕ := 10
def childrenH_676_i0 : Fin 2 → ℕ := ![height_55, height_380]
theorem height_exact_676_i0 : height_676_i0 = 1 + Finset.univ.sup childrenH_676_i0 := by decide +kernel
theorem required_origin_676_i0 : ∀ x ∈ required_676_i0,
    (∃ j, x ∈ childrenC_676_i0 j) ∨ ∀ j, x ∈ childrenD_676_i0 j := by decide +kernel
theorem required_exact_676_i0 : required_676_i0 =
    ((Finset.univ.biUnion childrenC_676_i0) ∪ commonEnvelope childrenD_676_i0).erase (2, 4) := by
  exact required_eq_combination childrenC_676_i0 childrenD_676_i0 (2, 4) required_676_i0
    (by decide +kernel) child_required_sub_676_i0 common_sub_676_i0 required_origin_676_i0
theorem envelope_origin_676_i0 : ∀ x ∈ envelope_676_i0,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_676_i0 j := by decide +kernel
theorem envelope_exact_676_i0 : envelope_676_i0 =
    insert (2, 4) (Finset.univ.biUnion childrenD_676_i0) := by
  exact envelope_eq_combination childrenD_676_i0 (2, 4) envelope_676_i0
    pivot_mem_676_i0 child_envelope_sub_676_i0 envelope_origin_676_i0
def checked_676_i0 : CheckedCard where
  required := required_676_i0
  envelope := envelope_676_i0
  height := height_676_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_676_i0
def height_676 : ℕ := 11
def childrenH_676 : Fin 4 → ℕ := ![height_7, height_8, height_9, height_676_i0]
theorem height_exact_676 : height_676 = 1 + Finset.univ.sup childrenH_676 := by decide +kernel
theorem required_origin_676 : ∀ x ∈ required_676,
    (∃ j, x ∈ childrenC_676 j) ∨ ∀ j, x ∈ childrenD_676 j := by decide +kernel
theorem required_exact_676 : required_676 =
    ((Finset.univ.biUnion childrenC_676) ∪ commonEnvelope childrenD_676).erase (4, 3) := by
  exact required_eq_combination childrenC_676 childrenD_676 (4, 3) required_676
    (by decide +kernel) child_required_sub_676 common_sub_676 required_origin_676
theorem envelope_origin_676 : ∀ x ∈ envelope_676,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_676 j := by decide +kernel
theorem envelope_exact_676 : envelope_676 =
    insert (4, 3) (Finset.univ.biUnion childrenD_676) := by
  exact envelope_eq_combination childrenD_676 (4, 3) envelope_676
    pivot_mem_676 child_envelope_sub_676 envelope_origin_676
def checked_676 : CheckedCard where
  required := required_676
  envelope := envelope_676
  height := height_676
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_676
def height_685_i4 : ℕ := 6
def childrenH_685_i4 : Fin 2 → ℕ := ![height_5, height_312]
theorem height_exact_685_i4 : height_685_i4 = 1 + Finset.univ.sup childrenH_685_i4 := by decide +kernel
theorem required_origin_685_i4 : ∀ x ∈ required_685_i4,
    (∃ j, x ∈ childrenC_685_i4 j) ∨ ∀ j, x ∈ childrenD_685_i4 j := by decide +kernel
theorem required_exact_685_i4 : required_685_i4 =
    ((Finset.univ.biUnion childrenC_685_i4) ∪ commonEnvelope childrenD_685_i4).erase (3, 1) := by
  exact required_eq_combination childrenC_685_i4 childrenD_685_i4 (3, 1) required_685_i4
    (by decide +kernel) child_required_sub_685_i4 common_sub_685_i4 required_origin_685_i4
theorem envelope_origin_685_i4 : ∀ x ∈ envelope_685_i4,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_685_i4 j := by decide +kernel
theorem envelope_exact_685_i4 : envelope_685_i4 =
    insert (3, 1) (Finset.univ.biUnion childrenD_685_i4) := by
  exact envelope_eq_combination childrenD_685_i4 (3, 1) envelope_685_i4
    pivot_mem_685_i4 child_envelope_sub_685_i4 envelope_origin_685_i4
def checked_685_i4 : CheckedCard where
  required := required_685_i4
  envelope := envelope_685_i4
  height := height_685_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_685_i4
def height_685_i3 : ℕ := 7
def childrenH_685_i3 : Fin 2 → ℕ := ![height_4, height_685_i4]
theorem height_exact_685_i3 : height_685_i3 = 1 + Finset.univ.sup childrenH_685_i3 := by decide +kernel
theorem required_origin_685_i3 : ∀ x ∈ required_685_i3,
    (∃ j, x ∈ childrenC_685_i3 j) ∨ ∀ j, x ∈ childrenD_685_i3 j := by decide +kernel
theorem required_exact_685_i3 : required_685_i3 =
    ((Finset.univ.biUnion childrenC_685_i3) ∪ commonEnvelope childrenD_685_i3).erase (2, 1) := by
  exact required_eq_combination childrenC_685_i3 childrenD_685_i3 (2, 1) required_685_i3
    (by decide +kernel) child_required_sub_685_i3 common_sub_685_i3 required_origin_685_i3
theorem envelope_origin_685_i3 : ∀ x ∈ envelope_685_i3,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_685_i3 j := by decide +kernel
theorem envelope_exact_685_i3 : envelope_685_i3 =
    insert (2, 1) (Finset.univ.biUnion childrenD_685_i3) := by
  exact envelope_eq_combination childrenD_685_i3 (2, 1) envelope_685_i3
    pivot_mem_685_i3 child_envelope_sub_685_i3 envelope_origin_685_i3
def checked_685_i3 : CheckedCard where
  required := required_685_i3
  envelope := envelope_685_i3
  height := height_685_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_685_i3
def height_685_i2 : ℕ := 8
def childrenH_685_i2 : Fin 2 → ℕ := ![height_351, height_685_i3]
theorem height_exact_685_i2 : height_685_i2 = 1 + Finset.univ.sup childrenH_685_i2 := by decide +kernel
theorem required_origin_685_i2 : ∀ x ∈ required_685_i2,
    (∃ j, x ∈ childrenC_685_i2 j) ∨ ∀ j, x ∈ childrenD_685_i2 j := by decide +kernel
theorem required_exact_685_i2 : required_685_i2 =
    ((Finset.univ.biUnion childrenC_685_i2) ∪ commonEnvelope childrenD_685_i2).erase (6, 2) := by
  exact required_eq_combination childrenC_685_i2 childrenD_685_i2 (6, 2) required_685_i2
    (by decide +kernel) child_required_sub_685_i2 common_sub_685_i2 required_origin_685_i2
theorem envelope_origin_685_i2 : ∀ x ∈ envelope_685_i2,
    x = (6, 2) ∨ ∃ j, x ∈ childrenD_685_i2 j := by decide +kernel
theorem envelope_exact_685_i2 : envelope_685_i2 =
    insert (6, 2) (Finset.univ.biUnion childrenD_685_i2) := by
  exact envelope_eq_combination childrenD_685_i2 (6, 2) envelope_685_i2
    pivot_mem_685_i2 child_envelope_sub_685_i2 envelope_origin_685_i2
def checked_685_i2 : CheckedCard where
  required := required_685_i2
  envelope := envelope_685_i2
  height := height_685_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_685_i2
def height_685_i1 : ℕ := 9
def childrenH_685_i1 : Fin 2 → ℕ := ![height_96, height_685_i2]
theorem height_exact_685_i1 : height_685_i1 = 1 + Finset.univ.sup childrenH_685_i1 := by decide +kernel
theorem required_origin_685_i1 : ∀ x ∈ required_685_i1,
    (∃ j, x ∈ childrenC_685_i1 j) ∨ ∀ j, x ∈ childrenD_685_i1 j := by decide +kernel
theorem required_exact_685_i1 : required_685_i1 =
    ((Finset.univ.biUnion childrenC_685_i1) ∪ commonEnvelope childrenD_685_i1).erase (6, 4) := by
  exact required_eq_combination childrenC_685_i1 childrenD_685_i1 (6, 4) required_685_i1
    (by decide +kernel) child_required_sub_685_i1 common_sub_685_i1 required_origin_685_i1
theorem envelope_origin_685_i1 : ∀ x ∈ envelope_685_i1,
    x = (6, 4) ∨ ∃ j, x ∈ childrenD_685_i1 j := by decide +kernel
theorem envelope_exact_685_i1 : envelope_685_i1 =
    insert (6, 4) (Finset.univ.biUnion childrenD_685_i1) := by
  exact envelope_eq_combination childrenD_685_i1 (6, 4) envelope_685_i1
    pivot_mem_685_i1 child_envelope_sub_685_i1 envelope_origin_685_i1
def checked_685_i1 : CheckedCard where
  required := required_685_i1
  envelope := envelope_685_i1
  height := height_685_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_685_i1
def height_685_i0 : ℕ := 10
def childrenH_685_i0 : Fin 2 → ℕ := ![height_5, height_685_i1]
theorem height_exact_685_i0 : height_685_i0 = 1 + Finset.univ.sup childrenH_685_i0 := by decide +kernel
theorem required_origin_685_i0 : ∀ x ∈ required_685_i0,
    (∃ j, x ∈ childrenC_685_i0 j) ∨ ∀ j, x ∈ childrenD_685_i0 j := by decide +kernel
theorem required_exact_685_i0 : required_685_i0 =
    ((Finset.univ.biUnion childrenC_685_i0) ∪ commonEnvelope childrenD_685_i0).erase (3, 2) := by
  exact required_eq_combination childrenC_685_i0 childrenD_685_i0 (3, 2) required_685_i0
    (by decide +kernel) child_required_sub_685_i0 common_sub_685_i0 required_origin_685_i0
theorem envelope_origin_685_i0 : ∀ x ∈ envelope_685_i0,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_685_i0 j := by decide +kernel
theorem envelope_exact_685_i0 : envelope_685_i0 =
    insert (3, 2) (Finset.univ.biUnion childrenD_685_i0) := by
  exact envelope_eq_combination childrenD_685_i0 (3, 2) envelope_685_i0
    pivot_mem_685_i0 child_envelope_sub_685_i0 envelope_origin_685_i0
def checked_685_i0 : CheckedCard where
  required := required_685_i0
  envelope := envelope_685_i0
  height := height_685_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_685_i0
def height_685 : ℕ := 11
def childrenH_685 : Fin 6 → ℕ := ![height_67, height_175, height_228, height_435, height_531, height_685_i0]
theorem height_exact_685 : height_685 = 1 + Finset.univ.sup childrenH_685 := by decide +kernel
theorem required_origin_685 : ∀ x ∈ required_685,
    (∃ j, x ∈ childrenC_685 j) ∨ ∀ j, x ∈ childrenD_685 j := by decide +kernel
theorem required_exact_685 : required_685 =
    ((Finset.univ.biUnion childrenC_685) ∪ commonEnvelope childrenD_685).erase (5, 5) := by
  exact required_eq_combination childrenC_685 childrenD_685 (5, 5) required_685
    (by decide +kernel) child_required_sub_685 common_sub_685 required_origin_685
theorem envelope_origin_685 : ∀ x ∈ envelope_685,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_685 j := by decide +kernel
theorem envelope_exact_685 : envelope_685 =
    insert (5, 5) (Finset.univ.biUnion childrenD_685) := by
  exact envelope_eq_combination childrenD_685 (5, 5) envelope_685
    pivot_mem_685 child_envelope_sub_685 envelope_origin_685
def checked_685 : CheckedCard where
  required := required_685
  envelope := envelope_685
  height := height_685
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_685
end SnakyPrototype.Certificate21

end OAI
