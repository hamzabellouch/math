import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part08
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part05
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_632_i2 : Finset Cell := ⟨(([(1, 4), (3, 3), (3, 4), (3, 5), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_632_i2 : Finset Cell := ⟨(([(1, 2), (1, 4), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (5, 3), (5, 4), (5, 5), (5, 6), (6, 3), (6, 4), (6, 5), (6, 6), (7, 4), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_632_i2 : Fin 2 → Finset Cell := ![(placed21 3 (1, 5) required_92), (placed21 1 (1, 2) required_378)]
def childrenD_632_i2 : Fin 2 → Finset Cell := ![(placed21 3 (1, 5) envelope_92), (placed21 1 (1, 2) envelope_378)]
theorem common_sub_632_i2 : commonEnvelope childrenD_632_i2 ⊆ insert (3, 2) required_632_i2 := by decide +kernel
theorem child_required_sub_632_i2 : ∀ j, childrenC_632_i2 j ⊆ insert (3, 2) required_632_i2 := by decide +kernel
theorem child_envelope_sub_632_i2 : ∀ j, childrenD_632_i2 j ⊆ envelope_632_i2 := by decide +kernel
theorem pivot_mem_632_i2 : (3, 2) ∈ envelope_632_i2 := by decide +kernel
theorem children_work_632_i2 : ∀ j, Template HasSnaky 6 (childrenC_632_i2 j) (childrenD_632_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_92 3 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_378 1 (1, 2)).mono (by decide +kernel)
theorem row_works_632_i2 : Template HasSnaky 7 required_632_i2 envelope_632_i2 := by
  refine compose HasSnaky 6 childrenC_632_i2 childrenD_632_i2 children_work_632_i2 (3, 2)
    required_632_i2 envelope_632_i2 pivot_mem_632_i2 child_required_sub_632_i2 child_envelope_sub_632_i2 ?_
  intro b hb
  exact common_sub_632_i2 (mem_commonEnvelope childrenD_632_i2 b hb)
def required_632_i1 : Finset Cell := ⟨(([(1, 4), (3, 3), (3, 4), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_632_i1 : Finset Cell := ⟨(([(0, 4), (1, 2), (1, 4), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (5, 3), (5, 4), (5, 5), (5, 6), (6, 3), (6, 4), (6, 5), (6, 6), (7, 4), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_632_i1 : Fin 4 → Finset Cell := ![(placed21 2 (4, 2) required_10), (placed21 4 (3, 6) required_52), (placed21 0 (0, 2) required_82), required_632_i2]
def childrenD_632_i1 : Fin 4 → Finset Cell := ![(placed21 2 (4, 2) envelope_10), (placed21 4 (3, 6) envelope_52), (placed21 0 (0, 2) envelope_82), envelope_632_i2]
theorem common_sub_632_i1 : commonEnvelope childrenD_632_i1 ⊆ insert (3, 5) required_632_i1 := by decide +kernel
theorem child_required_sub_632_i1 : ∀ j, childrenC_632_i1 j ⊆ insert (3, 5) required_632_i1 := by decide +kernel
theorem child_envelope_sub_632_i1 : ∀ j, childrenD_632_i1 j ⊆ envelope_632_i1 := by decide +kernel
theorem pivot_mem_632_i1 : (3, 5) ∈ envelope_632_i1 := by decide +kernel
theorem children_work_632_i1 : ∀ j, Template HasSnaky 7 (childrenC_632_i1 j) (childrenD_632_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 4 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_82 0 (0, 2)).mono (by decide +kernel)
  · exact row_works_632_i2.mono (by decide +kernel)
theorem row_works_632_i1 : Template HasSnaky 8 required_632_i1 envelope_632_i1 := by
  refine compose HasSnaky 7 childrenC_632_i1 childrenD_632_i1 children_work_632_i1 (3, 5)
    required_632_i1 envelope_632_i1 pivot_mem_632_i1 child_required_sub_632_i1 child_envelope_sub_632_i1 ?_
  intro b hb
  exact common_sub_632_i1 (mem_commonEnvelope childrenD_632_i1 b hb)
def required_632_i0 : Finset Cell := ⟨(([(1, 4), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_632_i0 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 2), (1, 4), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 3), (5, 4), (5, 5), (5, 6), (6, 3), (6, 4), (6, 5), (6, 6), (7, 4), (7, 5), (7, 6), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_632_i0 : Fin 4 → Finset Cell := ![(placed21 3 (0, 4) required_54), (placed21 5 (6, 2) required_294), required_632_i1, required_631]
def childrenD_632_i0 : Fin 4 → Finset Cell := ![(placed21 3 (0, 4) envelope_54), (placed21 5 (6, 2) envelope_294), envelope_632_i1, envelope_631]
theorem common_sub_632_i0 : commonEnvelope childrenD_632_i0 ⊆ insert (3, 4) required_632_i0 := by decide +kernel
theorem child_required_sub_632_i0 : ∀ j, childrenC_632_i0 j ⊆ insert (3, 4) required_632_i0 := by decide +kernel
theorem child_envelope_sub_632_i0 : ∀ j, childrenD_632_i0 j ⊆ envelope_632_i0 := by decide +kernel
theorem pivot_mem_632_i0 : (3, 4) ∈ envelope_632_i0 := by decide +kernel
theorem children_work_632_i0 : ∀ j, Template HasSnaky 10 (childrenC_632_i0 j) (childrenD_632_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_54 3 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_294 5 (6, 2)).mono (by decide +kernel)
  · exact row_works_632_i1.mono (by decide +kernel)
  · exact row_works_631.mono (by decide +kernel)
theorem row_works_632_i0 : Template HasSnaky 11 required_632_i0 envelope_632_i0 := by
  refine compose HasSnaky 10 childrenC_632_i0 childrenD_632_i0 children_work_632_i0 (3, 4)
    required_632_i0 envelope_632_i0 pivot_mem_632_i0 child_required_sub_632_i0 child_envelope_sub_632_i0 ?_
  intro b hb
  exact common_sub_632_i0 (mem_commonEnvelope childrenD_632_i0 b hb)
def required_632 : Finset Cell := ⟨(([(1, 3), (1, 4), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_632 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 4), (7, 5), (7, 6), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_632 : Fin 5 → Finset Cell := ![(placed21 3 (0, 4) required_50), (placed21 3 (0, 4) required_125), (placed21 5 (5, 2) required_454), (placed21 0 (1, 2) required_455), required_632_i0]
def childrenD_632 : Fin 5 → Finset Cell := ![(placed21 3 (0, 4) envelope_50), (placed21 3 (0, 4) envelope_125), (placed21 5 (5, 2) envelope_454), (placed21 0 (1, 2) envelope_455), envelope_632_i0]
theorem common_sub_632 : commonEnvelope childrenD_632 ⊆ insert (3, 3) required_632 := by decide +kernel
theorem child_required_sub_632 : ∀ j, childrenC_632 j ⊆ insert (3, 3) required_632 := by decide +kernel
theorem child_envelope_sub_632 : ∀ j, childrenD_632 j ⊆ envelope_632 := by decide +kernel
theorem pivot_mem_632 : (3, 3) ∈ envelope_632 := by decide +kernel
theorem children_work_632 : ∀ j, Template HasSnaky 11 (childrenC_632 j) (childrenD_632 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_50 3 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_125 3 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_454 5 (5, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_455 0 (1, 2)).mono (by decide +kernel)
  · exact row_works_632_i0.mono (by decide +kernel)
theorem row_works_632 : Template HasSnaky 12 required_632 envelope_632 := by
  refine compose HasSnaky 11 childrenC_632 childrenD_632 children_work_632 (3, 3)
    required_632 envelope_632 pivot_mem_632 child_required_sub_632 child_envelope_sub_632 ?_
  intro b hb
  exact common_sub_632 (mem_commonEnvelope childrenD_632 b hb)
def required_635_i0 : Finset Cell := ⟨(([(2, 3), (2, 4), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_635_i0 : Finset Cell := ⟨(([(0, 6), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 5), (5, 6), (5, 7), (6, 5), (6, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_635_i0 : Fin 3 → Finset Cell := ![(placed21 2 (2, 2) required_7), (placed21 0 (1, 2) required_9), (placed21 1 (0, 3) required_395)]
def childrenD_635_i0 : Fin 3 → Finset Cell := ![(placed21 2 (2, 2) envelope_7), (placed21 0 (1, 2) envelope_9), (placed21 1 (0, 3) envelope_395)]
theorem common_sub_635_i0 : commonEnvelope childrenD_635_i0 ⊆ insert (2, 6) required_635_i0 := by decide +kernel
theorem child_required_sub_635_i0 : ∀ j, childrenC_635_i0 j ⊆ insert (2, 6) required_635_i0 := by decide +kernel
theorem child_envelope_sub_635_i0 : ∀ j, childrenD_635_i0 j ⊆ envelope_635_i0 := by decide +kernel
theorem pivot_mem_635_i0 : (2, 6) ∈ envelope_635_i0 := by decide +kernel
theorem children_work_635_i0 : ∀ j, Template HasSnaky 8 (childrenC_635_i0 j) (childrenD_635_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 2 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_395 1 (0, 3)).mono (by decide +kernel)
theorem row_works_635_i0 : Template HasSnaky 9 required_635_i0 envelope_635_i0 := by
  refine compose HasSnaky 8 childrenC_635_i0 childrenD_635_i0 children_work_635_i0 (2, 6)
    required_635_i0 envelope_635_i0 pivot_mem_635_i0 child_required_sub_635_i0 child_envelope_sub_635_i0 ?_
  intro b hb
  exact common_sub_635_i0 (mem_commonEnvelope childrenD_635_i0 b hb)
def required_635 : Finset Cell := ⟨(([(2, 4), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_635 : Finset Cell := ⟨(([(0, 3), (0, 6), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 5), (6, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_635 : Fin 5 → Finset Cell := ![(placed21 4 (1, 7) required_14), (placed21 6 (3, 7) required_33), (placed21 3 (0, 6) required_181), (placed21 3 (0, 6) required_589), required_635_i0]
def childrenD_635 : Fin 5 → Finset Cell := ![(placed21 4 (1, 7) envelope_14), (placed21 6 (3, 7) envelope_33), (placed21 3 (0, 6) envelope_181), (placed21 3 (0, 6) envelope_589), envelope_635_i0]
theorem common_sub_635 : commonEnvelope childrenD_635 ⊆ insert (2, 3) required_635 := by decide +kernel
theorem child_required_sub_635 : ∀ j, childrenC_635 j ⊆ insert (2, 3) required_635 := by decide +kernel
theorem child_envelope_sub_635 : ∀ j, childrenD_635 j ⊆ envelope_635 := by decide +kernel
theorem pivot_mem_635 : (2, 3) ∈ envelope_635 := by decide +kernel
theorem children_work_635 : ∀ j, Template HasSnaky 11 (childrenC_635 j) (childrenD_635 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_14 4 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_33 6 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_181 3 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_589 3 (0, 6)).mono (by decide +kernel)
  · exact row_works_635_i0.mono (by decide +kernel)
theorem row_works_635 : Template HasSnaky 12 required_635 envelope_635 := by
  refine compose HasSnaky 11 childrenC_635 childrenD_635 children_work_635 (2, 3)
    required_635 envelope_635 pivot_mem_635 child_required_sub_635 child_envelope_sub_635 ?_
  intro b hb
  exact common_sub_635 (mem_commonEnvelope childrenD_635 b hb)
def required_649_i7 : Finset Cell := ⟨(([(2, 3), (2, 5), (2, 6), (3, 3), (3, 4), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_649_i7 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 5), (2, 6), (3, 3), (3, 4), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_649_i7 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) required_0), (placed21 2 (4, 2) required_78)]
def childrenD_649_i7 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) envelope_0), (placed21 2 (4, 2) envelope_78)]
theorem common_sub_649_i7 : commonEnvelope childrenD_649_i7 ⊆ insert (1, 3) required_649_i7 := by decide +kernel
theorem child_required_sub_649_i7 : ∀ j, childrenC_649_i7 j ⊆ insert (1, 3) required_649_i7 := by decide +kernel
theorem child_envelope_sub_649_i7 : ∀ j, childrenD_649_i7 j ⊆ envelope_649_i7 := by decide +kernel
theorem pivot_mem_649_i7 : (1, 3) ∈ envelope_649_i7 := by decide +kernel
theorem children_work_649_i7 : ∀ j, Template HasSnaky 3 (childrenC_649_i7 j) (childrenD_649_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 0 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_78 2 (4, 2)).mono (by decide +kernel)
theorem row_works_649_i7 : Template HasSnaky 4 required_649_i7 envelope_649_i7 := by
  refine compose HasSnaky 3 childrenC_649_i7 childrenD_649_i7 children_work_649_i7 (1, 3)
    required_649_i7 envelope_649_i7 pivot_mem_649_i7 child_required_sub_649_i7 child_envelope_sub_649_i7 ?_
  intro b hb
  exact common_sub_649_i7 (mem_commonEnvelope childrenD_649_i7 b hb)
def required_649_i6 : Finset Cell := ⟨(([(2, 5), (2, 6), (3, 3), (3, 4), (3, 5), (3, 6), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_649_i6 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 5), (2, 6), (3, 3), (3, 4), (3, 5), (3, 6), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_649_i6 : Fin 2 → Finset Cell := ![(placed21 7 (3, 6) required_5), required_649_i7]
def childrenD_649_i6 : Fin 2 → Finset Cell := ![(placed21 7 (3, 6) envelope_5), envelope_649_i7]
theorem common_sub_649_i6 : commonEnvelope childrenD_649_i6 ⊆ insert (2, 3) required_649_i6 := by decide +kernel
theorem child_required_sub_649_i6 : ∀ j, childrenC_649_i6 j ⊆ insert (2, 3) required_649_i6 := by decide +kernel
theorem child_envelope_sub_649_i6 : ∀ j, childrenD_649_i6 j ⊆ envelope_649_i6 := by decide +kernel
theorem pivot_mem_649_i6 : (2, 3) ∈ envelope_649_i6 := by decide +kernel
theorem children_work_649_i6 : ∀ j, Template HasSnaky 4 (childrenC_649_i6 j) (childrenD_649_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (3, 6)).mono (by decide +kernel)
  · exact row_works_649_i7.mono (by decide +kernel)
theorem row_works_649_i6 : Template HasSnaky 5 required_649_i6 envelope_649_i6 := by
  refine compose HasSnaky 4 childrenC_649_i6 childrenD_649_i6 children_work_649_i6 (2, 3)
    required_649_i6 envelope_649_i6 pivot_mem_649_i6 child_required_sub_649_i6 child_envelope_sub_649_i6 ?_
  intro b hb
  exact common_sub_649_i6 (mem_commonEnvelope childrenD_649_i6 b hb)
def required_649_i5 : Finset Cell := ⟨(([(2, 5), (2, 6), (3, 3), (3, 5), (3, 6), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_649_i5 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_649_i5 : Fin 2 → Finset Cell := ![(placed21 5 (3, 3) required_5), required_649_i6]
def childrenD_649_i5 : Fin 2 → Finset Cell := ![(placed21 5 (3, 3) envelope_5), envelope_649_i6]
theorem common_sub_649_i5 : commonEnvelope childrenD_649_i5 ⊆ insert (3, 4) required_649_i5 := by decide +kernel
theorem child_required_sub_649_i5 : ∀ j, childrenC_649_i5 j ⊆ insert (3, 4) required_649_i5 := by decide +kernel
theorem child_envelope_sub_649_i5 : ∀ j, childrenD_649_i5 j ⊆ envelope_649_i5 := by decide +kernel
theorem pivot_mem_649_i5 : (3, 4) ∈ envelope_649_i5 := by decide +kernel
theorem children_work_649_i5 : ∀ j, Template HasSnaky 5 (childrenC_649_i5 j) (childrenD_649_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (3, 3)).mono (by decide +kernel)
  · exact row_works_649_i6.mono (by decide +kernel)
theorem row_works_649_i5 : Template HasSnaky 6 required_649_i5 envelope_649_i5 := by
  refine compose HasSnaky 5 childrenC_649_i5 childrenD_649_i5 children_work_649_i5 (3, 4)
    required_649_i5 envelope_649_i5 pivot_mem_649_i5 child_required_sub_649_i5 child_envelope_sub_649_i5 ?_
  intro b hb
  exact common_sub_649_i5 (mem_commonEnvelope childrenD_649_i5 b hb)
def required_649_i4 : Finset Cell := ⟨(([(2, 5), (3, 3), (3, 5), (3, 6), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_649_i4 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (4, 3), (4, 4), (4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_649_i4 : Fin 2 → Finset Cell := ![(placed21 5 (5, 5) required_15), required_649_i5]
def childrenD_649_i4 : Fin 2 → Finset Cell := ![(placed21 5 (5, 5) envelope_15), envelope_649_i5]
theorem common_sub_649_i4 : commonEnvelope childrenD_649_i4 ⊆ insert (2, 6) required_649_i4 := by decide +kernel
theorem child_required_sub_649_i4 : ∀ j, childrenC_649_i4 j ⊆ insert (2, 6) required_649_i4 := by decide +kernel
theorem child_envelope_sub_649_i4 : ∀ j, childrenD_649_i4 j ⊆ envelope_649_i4 := by decide +kernel
theorem pivot_mem_649_i4 : (2, 6) ∈ envelope_649_i4 := by decide +kernel
theorem children_work_649_i4 : ∀ j, Template HasSnaky 6 (childrenC_649_i4 j) (childrenD_649_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_15 5 (5, 5)).mono (by decide +kernel)
  · exact row_works_649_i5.mono (by decide +kernel)
theorem row_works_649_i4 : Template HasSnaky 7 required_649_i4 envelope_649_i4 := by
  refine compose HasSnaky 6 childrenC_649_i4 childrenD_649_i4 children_work_649_i4 (2, 6)
    required_649_i4 envelope_649_i4 pivot_mem_649_i4 child_required_sub_649_i4 child_envelope_sub_649_i4 ?_
  intro b hb
  exact common_sub_649_i4 (mem_commonEnvelope childrenD_649_i4 b hb)
def required_649_i3 : Finset Cell := ⟨(([(2, 5), (3, 5), (3, 6), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_649_i3 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 3), (4, 4), (4, 5), (4, 6), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_649_i3 : Fin 2 → Finset Cell := ![(placed21 7 (4, 6) required_5), required_649_i4]
def childrenD_649_i3 : Fin 2 → Finset Cell := ![(placed21 7 (4, 6) envelope_5), envelope_649_i4]
theorem common_sub_649_i3 : commonEnvelope childrenD_649_i3 ⊆ insert (3, 3) required_649_i3 := by decide +kernel
theorem child_required_sub_649_i3 : ∀ j, childrenC_649_i3 j ⊆ insert (3, 3) required_649_i3 := by decide +kernel
theorem child_envelope_sub_649_i3 : ∀ j, childrenD_649_i3 j ⊆ envelope_649_i3 := by decide +kernel
theorem pivot_mem_649_i3 : (3, 3) ∈ envelope_649_i3 := by decide +kernel
theorem children_work_649_i3 : ∀ j, Template HasSnaky 7 (childrenC_649_i3 j) (childrenD_649_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (4, 6)).mono (by decide +kernel)
  · exact row_works_649_i4.mono (by decide +kernel)
theorem row_works_649_i3 : Template HasSnaky 8 required_649_i3 envelope_649_i3 := by
  refine compose HasSnaky 7 childrenC_649_i3 childrenD_649_i3 children_work_649_i3 (3, 3)
    required_649_i3 envelope_649_i3 pivot_mem_649_i3 child_required_sub_649_i3 child_envelope_sub_649_i3 ?_
  intro b hb
  exact common_sub_649_i3 (mem_commonEnvelope childrenD_649_i3 b hb)
def required_649_i2 : Finset Cell := ⟨(([(2, 5), (3, 5), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_649_i2 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 3), (4, 4), (4, 5), (4, 6), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_649_i2 : Fin 2 → Finset Cell := ![(placed21 5 (4, 3) required_5), required_649_i3]
def childrenD_649_i2 : Fin 2 → Finset Cell := ![(placed21 5 (4, 3) envelope_5), envelope_649_i3]
theorem common_sub_649_i2 : commonEnvelope childrenD_649_i2 ⊆ insert (3, 6) required_649_i2 := by decide +kernel
theorem child_required_sub_649_i2 : ∀ j, childrenC_649_i2 j ⊆ insert (3, 6) required_649_i2 := by decide +kernel
theorem child_envelope_sub_649_i2 : ∀ j, childrenD_649_i2 j ⊆ envelope_649_i2 := by decide +kernel
theorem pivot_mem_649_i2 : (3, 6) ∈ envelope_649_i2 := by decide +kernel
theorem children_work_649_i2 : ∀ j, Template HasSnaky 8 (childrenC_649_i2 j) (childrenD_649_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (4, 3)).mono (by decide +kernel)
  · exact row_works_649_i3.mono (by decide +kernel)
theorem row_works_649_i2 : Template HasSnaky 9 required_649_i2 envelope_649_i2 := by
  refine compose HasSnaky 8 childrenC_649_i2 childrenD_649_i2 children_work_649_i2 (3, 6)
    required_649_i2 envelope_649_i2 pivot_mem_649_i2 child_required_sub_649_i2 child_envelope_sub_649_i2 ?_
  intro b hb
  exact common_sub_649_i2 (mem_commonEnvelope childrenD_649_i2 b hb)
def required_649_i1 : Finset Cell := ⟨(([(2, 5), (3, 5), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_649_i1 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 5), (5, 7), (5, 8), (5, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_649_i1 : Fin 4 → Finset Cell := ![(placed21 0 (3, 2) required_19), (placed21 0 (3, 2) required_84), (placed21 1 (3, 3) required_314), required_649_i2]
def childrenD_649_i1 : Fin 4 → Finset Cell := ![(placed21 0 (3, 2) envelope_19), (placed21 0 (3, 2) envelope_84), (placed21 1 (3, 3) envelope_314), envelope_649_i2]
theorem common_sub_649_i1 : commonEnvelope childrenD_649_i1 ⊆ insert (4, 6) required_649_i1 := by decide +kernel
theorem child_required_sub_649_i1 : ∀ j, childrenC_649_i1 j ⊆ insert (4, 6) required_649_i1 := by decide +kernel
theorem child_envelope_sub_649_i1 : ∀ j, childrenD_649_i1 j ⊆ envelope_649_i1 := by decide +kernel
theorem pivot_mem_649_i1 : (4, 6) ∈ envelope_649_i1 := by decide +kernel
theorem children_work_649_i1 : ∀ j, Template HasSnaky 9 (childrenC_649_i1 j) (childrenD_649_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_19 0 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_84 0 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_314 1 (3, 3)).mono (by decide +kernel)
  · exact row_works_649_i2.mono (by decide +kernel)
theorem row_works_649_i1 : Template HasSnaky 10 required_649_i1 envelope_649_i1 := by
  refine compose HasSnaky 9 childrenC_649_i1 childrenD_649_i1 children_work_649_i1 (4, 6)
    required_649_i1 envelope_649_i1 pivot_mem_649_i1 child_required_sub_649_i1 child_envelope_sub_649_i1 ?_
  intro b hb
  exact common_sub_649_i1 (mem_commonEnvelope childrenD_649_i1 b hb)
def required_649_i0 : Finset Cell := ⟨(([(2, 5), (3, 5), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_649_i0 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 5), (5, 7), (5, 8), (5, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_649_i0 : Fin 4 → Finset Cell := ![(placed21 4 (3, 6) required_10), (placed21 2 (4, 2) required_44), (placed21 4 (3, 6) required_63), required_649_i1]
def childrenD_649_i0 : Fin 4 → Finset Cell := ![(placed21 4 (3, 6) envelope_10), (placed21 2 (4, 2) envelope_44), (placed21 4 (3, 6) envelope_63), envelope_649_i1]
theorem common_sub_649_i0 : commonEnvelope childrenD_649_i0 ⊆ insert (4, 3) required_649_i0 := by decide +kernel
theorem child_required_sub_649_i0 : ∀ j, childrenC_649_i0 j ⊆ insert (4, 3) required_649_i0 := by decide +kernel
theorem child_envelope_sub_649_i0 : ∀ j, childrenD_649_i0 j ⊆ envelope_649_i0 := by decide +kernel
theorem pivot_mem_649_i0 : (4, 3) ∈ envelope_649_i0 := by decide +kernel
theorem children_work_649_i0 : ∀ j, Template HasSnaky 10 (childrenC_649_i0 j) (childrenD_649_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 4 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_44 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_63 4 (3, 6)).mono (by decide +kernel)
  · exact row_works_649_i1.mono (by decide +kernel)
theorem row_works_649_i0 : Template HasSnaky 11 required_649_i0 envelope_649_i0 := by
  refine compose HasSnaky 10 childrenC_649_i0 childrenD_649_i0 children_work_649_i0 (4, 3)
    required_649_i0 envelope_649_i0 pivot_mem_649_i0 child_required_sub_649_i0 child_envelope_sub_649_i0 ?_
  intro b hb
  exact common_sub_649_i0 (mem_commonEnvelope childrenD_649_i0 b hb)
def required_649 : Finset Cell := ⟨(([(2, 5), (3, 5), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_649 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 7), (5, 8), (5, 9), (6, 4), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_649 : Fin 3 → Finset Cell := ![(placed21 3 (1, 5) required_52), (placed21 0 (1, 1) required_523), required_649_i0]
def childrenD_649 : Fin 3 → Finset Cell := ![(placed21 3 (1, 5) envelope_52), (placed21 0 (1, 1) envelope_523), envelope_649_i0]
theorem common_sub_649 : commonEnvelope childrenD_649 ⊆ insert (4, 4) required_649 := by decide +kernel
theorem child_required_sub_649 : ∀ j, childrenC_649 j ⊆ insert (4, 4) required_649 := by decide +kernel
theorem child_envelope_sub_649 : ∀ j, childrenD_649 j ⊆ envelope_649 := by decide +kernel
theorem pivot_mem_649 : (4, 4) ∈ envelope_649 := by decide +kernel
theorem children_work_649 : ∀ j, Template HasSnaky 11 (childrenC_649 j) (childrenD_649 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 3 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_523 0 (1, 1)).mono (by decide +kernel)
  · exact row_works_649_i0.mono (by decide +kernel)
theorem row_works_649 : Template HasSnaky 12 required_649 envelope_649 := by
  refine compose HasSnaky 11 childrenC_649 childrenD_649 children_work_649 (4, 4)
    required_649 envelope_649 pivot_mem_649 child_required_sub_649 child_envelope_sub_649 ?_
  intro b hb
  exact common_sub_649 (mem_commonEnvelope childrenD_649 b hb)
def required_654_i1 : Finset Cell := ⟨(([(3, 3), (3, 4), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_654_i1 : Finset Cell := ⟨(([(1, 4), (2, 4), (3, 3), (3, 4), (3, 5), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (6, 3), (6, 5), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_654_i1 : Fin 2 → Finset Cell := ![(placed21 7 (4, 7) required_0), (placed21 3 (1, 7) required_502)]
def childrenD_654_i1 : Fin 2 → Finset Cell := ![(placed21 7 (4, 7) envelope_0), (placed21 3 (1, 7) envelope_502)]
theorem common_sub_654_i1 : commonEnvelope childrenD_654_i1 ⊆ insert (4, 6) required_654_i1 := by decide +kernel
theorem child_required_sub_654_i1 : ∀ j, childrenC_654_i1 j ⊆ insert (4, 6) required_654_i1 := by decide +kernel
theorem child_envelope_sub_654_i1 : ∀ j, childrenD_654_i1 j ⊆ envelope_654_i1 := by decide +kernel
theorem pivot_mem_654_i1 : (4, 6) ∈ envelope_654_i1 := by decide +kernel
theorem children_work_654_i1 : ∀ j, Template HasSnaky 5 (childrenC_654_i1 j) (childrenD_654_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (4, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_502 3 (1, 7)).mono (by decide +kernel)
theorem row_works_654_i1 : Template HasSnaky 6 required_654_i1 envelope_654_i1 := by
  refine compose HasSnaky 5 childrenC_654_i1 childrenD_654_i1 children_work_654_i1 (4, 6)
    required_654_i1 envelope_654_i1 pivot_mem_654_i1 child_required_sub_654_i1 child_envelope_sub_654_i1 ?_
  intro b hb
  exact common_sub_654_i1 (mem_commonEnvelope childrenD_654_i1 b hb)
def required_654_i0 : Finset Cell := ⟨(([(3, 3), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_654_i0 : Finset Cell := ⟨(([(0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 5), (6, 6), (7, 2), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_654_i0 : Fin 4 → Finset Cell := ![(placed21 0 (3, 1) required_53), (placed21 6 (4, 7) required_53), (placed21 6 (7, 8) required_651), required_654_i1]
def childrenD_654_i0 : Fin 4 → Finset Cell := ![(placed21 0 (3, 1) envelope_53), (placed21 6 (4, 7) envelope_53), (placed21 6 (7, 8) envelope_651), envelope_654_i1]
theorem common_sub_654_i0 : commonEnvelope childrenD_654_i0 ⊆ insert (4, 5) required_654_i0 := by decide +kernel
theorem child_required_sub_654_i0 : ∀ j, childrenC_654_i0 j ⊆ insert (4, 5) required_654_i0 := by decide +kernel
theorem child_envelope_sub_654_i0 : ∀ j, childrenD_654_i0 j ⊆ envelope_654_i0 := by decide +kernel
theorem pivot_mem_654_i0 : (4, 5) ∈ envelope_654_i0 := by decide +kernel
theorem children_work_654_i0 : ∀ j, Template HasSnaky 8 (childrenC_654_i0 j) (childrenD_654_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_53 0 (3, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_53 6 (4, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_651 6 (7, 8)).mono (by decide +kernel)
  · exact row_works_654_i1.mono (by decide +kernel)
theorem row_works_654_i0 : Template HasSnaky 9 required_654_i0 envelope_654_i0 := by
  refine compose HasSnaky 8 childrenC_654_i0 childrenD_654_i0 children_work_654_i0 (4, 5)
    required_654_i0 envelope_654_i0 pivot_mem_654_i0 child_required_sub_654_i0 child_envelope_sub_654_i0 ?_
  intro b hb
  exact common_sub_654_i0 (mem_commonEnvelope childrenD_654_i0 b hb)
def required_654 : Finset Cell := ⟨(([(3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_654 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 3), (8, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_654 : Fin 8 → Finset Cell := ![(placed21 1 (0, 2) required_248), (placed21 1 (0, 2) required_300), (placed21 1 (0, 1) required_436), (placed21 4 (1, 7) required_449), (placed21 0 (1, 1) required_509), (placed21 4 (1, 7) required_510), (placed21 3 (0, 7) required_653), required_654_i0]
def childrenD_654 : Fin 8 → Finset Cell := ![(placed21 1 (0, 2) envelope_248), (placed21 1 (0, 2) envelope_300), (placed21 1 (0, 1) envelope_436), (placed21 4 (1, 7) envelope_449), (placed21 0 (1, 1) envelope_509), (placed21 4 (1, 7) envelope_510), (placed21 3 (0, 7) envelope_653), envelope_654_i0]
theorem common_sub_654 : commonEnvelope childrenD_654 ⊆ insert (4, 4) required_654 := by decide +kernel
theorem child_required_sub_654 : ∀ j, childrenC_654 j ⊆ insert (4, 4) required_654 := by decide +kernel
theorem child_envelope_sub_654 : ∀ j, childrenD_654 j ⊆ envelope_654 := by decide +kernel
theorem pivot_mem_654 : (4, 4) ∈ envelope_654 := by decide +kernel
theorem children_work_654 : ∀ j, Template HasSnaky 11 (childrenC_654 j) (childrenD_654 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_248 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_300 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_436 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_449 4 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_509 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_510 4 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_653 3 (0, 7)).mono (by decide +kernel)
  · exact row_works_654_i0.mono (by decide +kernel)
theorem row_works_654 : Template HasSnaky 12 required_654 envelope_654 := by
  refine compose HasSnaky 11 childrenC_654 childrenD_654 children_work_654 (4, 4)
    required_654 envelope_654 pivot_mem_654 child_required_sub_654 child_envelope_sub_654 ?_
  intro b hb
  exact common_sub_654 (mem_commonEnvelope childrenD_654 b hb)
def required_677 : Finset Cell := ⟨(([(3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_677 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 5), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_677 : Fin 5 → Finset Cell := ![(placed21 6 (4, 7) required_13), (placed21 4 (2, 7) required_14), (placed21 6 (4, 7) required_33), (placed21 3 (1, 6) required_589), (placed21 1 (0, 2) required_676)]
def childrenD_677 : Fin 5 → Finset Cell := ![(placed21 6 (4, 7) envelope_13), (placed21 4 (2, 7) envelope_14), (placed21 6 (4, 7) envelope_33), (placed21 3 (1, 6) envelope_589), (placed21 1 (0, 2) envelope_676)]
theorem common_sub_677 : commonEnvelope childrenD_677 ⊆ insert (3, 3) required_677 := by decide +kernel
theorem child_required_sub_677 : ∀ j, childrenC_677 j ⊆ insert (3, 3) required_677 := by decide +kernel
theorem child_envelope_sub_677 : ∀ j, childrenD_677 j ⊆ envelope_677 := by decide +kernel
theorem pivot_mem_677 : (3, 3) ∈ envelope_677 := by decide +kernel
theorem children_work_677 : ∀ j, Template HasSnaky 11 (childrenC_677 j) (childrenD_677 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 6 (4, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_14 4 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_33 6 (4, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_589 3 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_676 1 (0, 2)).mono (by decide +kernel)
theorem row_works_677 : Template HasSnaky 12 required_677 envelope_677 := by
  refine compose HasSnaky 11 childrenC_677 childrenD_677 children_work_677 (3, 3)
    required_677 envelope_677 pivot_mem_677 child_required_sub_677 child_envelope_sub_677 ?_
  intro b hb
  exact common_sub_677 (mem_commonEnvelope childrenD_677 b hb)
def required_687 : Finset Cell := ⟨(([(3, 4), (4, 4), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_687 : Finset Cell := ⟨(([(0, 3), (0, 5), (0, 6), (0, 7), (0, 8), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 6), (2, 7), (2, 8), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 0), (6, 1), (6, 2), (6, 3), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 5), (8, 6), (8, 7), (9, 5), (9, 6), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_687 : Fin 4 → Finset Cell := ![(placed21 1 (2, 4) required_44), (placed21 2 (6, 0) required_324), (placed21 1 (0, 1) required_685), (placed21 0 (1, 1) required_686)]
def childrenD_687 : Fin 4 → Finset Cell := ![(placed21 1 (2, 4) envelope_44), (placed21 2 (6, 0) envelope_324), (placed21 1 (0, 1) envelope_685), (placed21 0 (1, 1) envelope_686)]
theorem common_sub_687 : commonEnvelope childrenD_687 ⊆ insert (5, 5) required_687 := by decide +kernel
theorem child_required_sub_687 : ∀ j, childrenC_687 j ⊆ insert (5, 5) required_687 := by decide +kernel
theorem child_envelope_sub_687 : ∀ j, childrenD_687 j ⊆ envelope_687 := by decide +kernel
theorem pivot_mem_687 : (5, 5) ∈ envelope_687 := by decide +kernel
theorem children_work_687 : ∀ j, Template HasSnaky 11 (childrenC_687 j) (childrenD_687 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 1 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_324 2 (6, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_685 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_686 0 (1, 1)).mono (by decide +kernel)
theorem row_works_687 : Template HasSnaky 12 required_687 envelope_687 := by
  refine compose HasSnaky 11 childrenC_687 childrenD_687 children_work_687 (5, 5)
    required_687 envelope_687 pivot_mem_687 child_required_sub_687 child_envelope_sub_687 ?_
  intro b hb
  exact common_sub_687 (mem_commonEnvelope childrenD_687 b hb)
def height_632_i2 : ℕ := 7
def childrenH_632_i2 : Fin 2 → ℕ := ![height_92, height_378]
theorem height_exact_632_i2 : height_632_i2 = 1 + Finset.univ.sup childrenH_632_i2 := by decide +kernel
theorem required_origin_632_i2 : ∀ x ∈ required_632_i2,
    (∃ j, x ∈ childrenC_632_i2 j) ∨ ∀ j, x ∈ childrenD_632_i2 j := by decide +kernel
theorem required_exact_632_i2 : required_632_i2 =
    ((Finset.univ.biUnion childrenC_632_i2) ∪ commonEnvelope childrenD_632_i2).erase (3, 2) := by
  exact required_eq_combination childrenC_632_i2 childrenD_632_i2 (3, 2) required_632_i2
    (by decide +kernel) child_required_sub_632_i2 common_sub_632_i2 required_origin_632_i2
theorem envelope_origin_632_i2 : ∀ x ∈ envelope_632_i2,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_632_i2 j := by decide +kernel
theorem envelope_exact_632_i2 : envelope_632_i2 =
    insert (3, 2) (Finset.univ.biUnion childrenD_632_i2) := by
  exact envelope_eq_combination childrenD_632_i2 (3, 2) envelope_632_i2
    pivot_mem_632_i2 child_envelope_sub_632_i2 envelope_origin_632_i2
def checked_632_i2 : CheckedCard where
  required := required_632_i2
  envelope := envelope_632_i2
  height := height_632_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_632_i2
def height_632_i1 : ℕ := 8
def childrenH_632_i1 : Fin 4 → ℕ := ![height_10, height_52, height_82, height_632_i2]
theorem height_exact_632_i1 : height_632_i1 = 1 + Finset.univ.sup childrenH_632_i1 := by decide +kernel
theorem required_origin_632_i1 : ∀ x ∈ required_632_i1,
    (∃ j, x ∈ childrenC_632_i1 j) ∨ ∀ j, x ∈ childrenD_632_i1 j := by decide +kernel
theorem required_exact_632_i1 : required_632_i1 =
    ((Finset.univ.biUnion childrenC_632_i1) ∪ commonEnvelope childrenD_632_i1).erase (3, 5) := by
  exact required_eq_combination childrenC_632_i1 childrenD_632_i1 (3, 5) required_632_i1
    (by decide +kernel) child_required_sub_632_i1 common_sub_632_i1 required_origin_632_i1
theorem envelope_origin_632_i1 : ∀ x ∈ envelope_632_i1,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_632_i1 j := by decide +kernel
theorem envelope_exact_632_i1 : envelope_632_i1 =
    insert (3, 5) (Finset.univ.biUnion childrenD_632_i1) := by
  exact envelope_eq_combination childrenD_632_i1 (3, 5) envelope_632_i1
    pivot_mem_632_i1 child_envelope_sub_632_i1 envelope_origin_632_i1
def checked_632_i1 : CheckedCard where
  required := required_632_i1
  envelope := envelope_632_i1
  height := height_632_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_632_i1
def height_632_i0 : ℕ := 11
def childrenH_632_i0 : Fin 4 → ℕ := ![height_54, height_294, height_632_i1, height_631]
theorem height_exact_632_i0 : height_632_i0 = 1 + Finset.univ.sup childrenH_632_i0 := by decide +kernel
theorem required_origin_632_i0 : ∀ x ∈ required_632_i0,
    (∃ j, x ∈ childrenC_632_i0 j) ∨ ∀ j, x ∈ childrenD_632_i0 j := by decide +kernel
theorem required_exact_632_i0 : required_632_i0 =
    ((Finset.univ.biUnion childrenC_632_i0) ∪ commonEnvelope childrenD_632_i0).erase (3, 4) := by
  exact required_eq_combination childrenC_632_i0 childrenD_632_i0 (3, 4) required_632_i0
    (by decide +kernel) child_required_sub_632_i0 common_sub_632_i0 required_origin_632_i0
theorem envelope_origin_632_i0 : ∀ x ∈ envelope_632_i0,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_632_i0 j := by decide +kernel
theorem envelope_exact_632_i0 : envelope_632_i0 =
    insert (3, 4) (Finset.univ.biUnion childrenD_632_i0) := by
  exact envelope_eq_combination childrenD_632_i0 (3, 4) envelope_632_i0
    pivot_mem_632_i0 child_envelope_sub_632_i0 envelope_origin_632_i0
def checked_632_i0 : CheckedCard where
  required := required_632_i0
  envelope := envelope_632_i0
  height := height_632_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_632_i0
def height_632 : ℕ := 12
def childrenH_632 : Fin 5 → ℕ := ![height_50, height_125, height_454, height_455, height_632_i0]
theorem height_exact_632 : height_632 = 1 + Finset.univ.sup childrenH_632 := by decide +kernel
theorem required_origin_632 : ∀ x ∈ required_632,
    (∃ j, x ∈ childrenC_632 j) ∨ ∀ j, x ∈ childrenD_632 j := by decide +kernel
theorem required_exact_632 : required_632 =
    ((Finset.univ.biUnion childrenC_632) ∪ commonEnvelope childrenD_632).erase (3, 3) := by
  exact required_eq_combination childrenC_632 childrenD_632 (3, 3) required_632
    (by decide +kernel) child_required_sub_632 common_sub_632 required_origin_632
theorem envelope_origin_632 : ∀ x ∈ envelope_632,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_632 j := by decide +kernel
theorem envelope_exact_632 : envelope_632 =
    insert (3, 3) (Finset.univ.biUnion childrenD_632) := by
  exact envelope_eq_combination childrenD_632 (3, 3) envelope_632
    pivot_mem_632 child_envelope_sub_632 envelope_origin_632
def checked_632 : CheckedCard where
  required := required_632
  envelope := envelope_632
  height := height_632
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_632
def height_635_i0 : ℕ := 9
def childrenH_635_i0 : Fin 3 → ℕ := ![height_7, height_9, height_395]
theorem height_exact_635_i0 : height_635_i0 = 1 + Finset.univ.sup childrenH_635_i0 := by decide +kernel
theorem required_origin_635_i0 : ∀ x ∈ required_635_i0,
    (∃ j, x ∈ childrenC_635_i0 j) ∨ ∀ j, x ∈ childrenD_635_i0 j := by decide +kernel
theorem required_exact_635_i0 : required_635_i0 =
    ((Finset.univ.biUnion childrenC_635_i0) ∪ commonEnvelope childrenD_635_i0).erase (2, 6) := by
  exact required_eq_combination childrenC_635_i0 childrenD_635_i0 (2, 6) required_635_i0
    (by decide +kernel) child_required_sub_635_i0 common_sub_635_i0 required_origin_635_i0
theorem envelope_origin_635_i0 : ∀ x ∈ envelope_635_i0,
    x = (2, 6) ∨ ∃ j, x ∈ childrenD_635_i0 j := by decide +kernel
theorem envelope_exact_635_i0 : envelope_635_i0 =
    insert (2, 6) (Finset.univ.biUnion childrenD_635_i0) := by
  exact envelope_eq_combination childrenD_635_i0 (2, 6) envelope_635_i0
    pivot_mem_635_i0 child_envelope_sub_635_i0 envelope_origin_635_i0
def checked_635_i0 : CheckedCard where
  required := required_635_i0
  envelope := envelope_635_i0
  height := height_635_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_635_i0
def height_635 : ℕ := 12
def childrenH_635 : Fin 5 → ℕ := ![height_14, height_33, height_181, height_589, height_635_i0]
theorem height_exact_635 : height_635 = 1 + Finset.univ.sup childrenH_635 := by decide +kernel
theorem required_origin_635 : ∀ x ∈ required_635,
    (∃ j, x ∈ childrenC_635 j) ∨ ∀ j, x ∈ childrenD_635 j := by decide +kernel
theorem required_exact_635 : required_635 =
    ((Finset.univ.biUnion childrenC_635) ∪ commonEnvelope childrenD_635).erase (2, 3) := by
  exact required_eq_combination childrenC_635 childrenD_635 (2, 3) required_635
    (by decide +kernel) child_required_sub_635 common_sub_635 required_origin_635
theorem envelope_origin_635 : ∀ x ∈ envelope_635,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_635 j := by decide +kernel
theorem envelope_exact_635 : envelope_635 =
    insert (2, 3) (Finset.univ.biUnion childrenD_635) := by
  exact envelope_eq_combination childrenD_635 (2, 3) envelope_635
    pivot_mem_635 child_envelope_sub_635 envelope_origin_635
def checked_635 : CheckedCard where
  required := required_635
  envelope := envelope_635
  height := height_635
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_635
def height_649_i7 : ℕ := 4
def childrenH_649_i7 : Fin 2 → ℕ := ![height_0, height_78]
theorem height_exact_649_i7 : height_649_i7 = 1 + Finset.univ.sup childrenH_649_i7 := by decide +kernel
theorem required_origin_649_i7 : ∀ x ∈ required_649_i7,
    (∃ j, x ∈ childrenC_649_i7 j) ∨ ∀ j, x ∈ childrenD_649_i7 j := by decide +kernel
theorem required_exact_649_i7 : required_649_i7 =
    ((Finset.univ.biUnion childrenC_649_i7) ∪ commonEnvelope childrenD_649_i7).erase (1, 3) := by
  exact required_eq_combination childrenC_649_i7 childrenD_649_i7 (1, 3) required_649_i7
    (by decide +kernel) child_required_sub_649_i7 common_sub_649_i7 required_origin_649_i7
theorem envelope_origin_649_i7 : ∀ x ∈ envelope_649_i7,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_649_i7 j := by decide +kernel
theorem envelope_exact_649_i7 : envelope_649_i7 =
    insert (1, 3) (Finset.univ.biUnion childrenD_649_i7) := by
  exact envelope_eq_combination childrenD_649_i7 (1, 3) envelope_649_i7
    pivot_mem_649_i7 child_envelope_sub_649_i7 envelope_origin_649_i7
def checked_649_i7 : CheckedCard where
  required := required_649_i7
  envelope := envelope_649_i7
  height := height_649_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_649_i7
def height_649_i6 : ℕ := 5
def childrenH_649_i6 : Fin 2 → ℕ := ![height_5, height_649_i7]
theorem height_exact_649_i6 : height_649_i6 = 1 + Finset.univ.sup childrenH_649_i6 := by decide +kernel
theorem required_origin_649_i6 : ∀ x ∈ required_649_i6,
    (∃ j, x ∈ childrenC_649_i6 j) ∨ ∀ j, x ∈ childrenD_649_i6 j := by decide +kernel
theorem required_exact_649_i6 : required_649_i6 =
    ((Finset.univ.biUnion childrenC_649_i6) ∪ commonEnvelope childrenD_649_i6).erase (2, 3) := by
  exact required_eq_combination childrenC_649_i6 childrenD_649_i6 (2, 3) required_649_i6
    (by decide +kernel) child_required_sub_649_i6 common_sub_649_i6 required_origin_649_i6
theorem envelope_origin_649_i6 : ∀ x ∈ envelope_649_i6,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_649_i6 j := by decide +kernel
theorem envelope_exact_649_i6 : envelope_649_i6 =
    insert (2, 3) (Finset.univ.biUnion childrenD_649_i6) := by
  exact envelope_eq_combination childrenD_649_i6 (2, 3) envelope_649_i6
    pivot_mem_649_i6 child_envelope_sub_649_i6 envelope_origin_649_i6
def checked_649_i6 : CheckedCard where
  required := required_649_i6
  envelope := envelope_649_i6
  height := height_649_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_649_i6
def height_649_i5 : ℕ := 6
def childrenH_649_i5 : Fin 2 → ℕ := ![height_5, height_649_i6]
theorem height_exact_649_i5 : height_649_i5 = 1 + Finset.univ.sup childrenH_649_i5 := by decide +kernel
theorem required_origin_649_i5 : ∀ x ∈ required_649_i5,
    (∃ j, x ∈ childrenC_649_i5 j) ∨ ∀ j, x ∈ childrenD_649_i5 j := by decide +kernel
theorem required_exact_649_i5 : required_649_i5 =
    ((Finset.univ.biUnion childrenC_649_i5) ∪ commonEnvelope childrenD_649_i5).erase (3, 4) := by
  exact required_eq_combination childrenC_649_i5 childrenD_649_i5 (3, 4) required_649_i5
    (by decide +kernel) child_required_sub_649_i5 common_sub_649_i5 required_origin_649_i5
theorem envelope_origin_649_i5 : ∀ x ∈ envelope_649_i5,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_649_i5 j := by decide +kernel
theorem envelope_exact_649_i5 : envelope_649_i5 =
    insert (3, 4) (Finset.univ.biUnion childrenD_649_i5) := by
  exact envelope_eq_combination childrenD_649_i5 (3, 4) envelope_649_i5
    pivot_mem_649_i5 child_envelope_sub_649_i5 envelope_origin_649_i5
def checked_649_i5 : CheckedCard where
  required := required_649_i5
  envelope := envelope_649_i5
  height := height_649_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_649_i5
def height_649_i4 : ℕ := 7
def childrenH_649_i4 : Fin 2 → ℕ := ![height_15, height_649_i5]
theorem height_exact_649_i4 : height_649_i4 = 1 + Finset.univ.sup childrenH_649_i4 := by decide +kernel
theorem required_origin_649_i4 : ∀ x ∈ required_649_i4,
    (∃ j, x ∈ childrenC_649_i4 j) ∨ ∀ j, x ∈ childrenD_649_i4 j := by decide +kernel
theorem required_exact_649_i4 : required_649_i4 =
    ((Finset.univ.biUnion childrenC_649_i4) ∪ commonEnvelope childrenD_649_i4).erase (2, 6) := by
  exact required_eq_combination childrenC_649_i4 childrenD_649_i4 (2, 6) required_649_i4
    (by decide +kernel) child_required_sub_649_i4 common_sub_649_i4 required_origin_649_i4
theorem envelope_origin_649_i4 : ∀ x ∈ envelope_649_i4,
    x = (2, 6) ∨ ∃ j, x ∈ childrenD_649_i4 j := by decide +kernel
theorem envelope_exact_649_i4 : envelope_649_i4 =
    insert (2, 6) (Finset.univ.biUnion childrenD_649_i4) := by
  exact envelope_eq_combination childrenD_649_i4 (2, 6) envelope_649_i4
    pivot_mem_649_i4 child_envelope_sub_649_i4 envelope_origin_649_i4
def checked_649_i4 : CheckedCard where
  required := required_649_i4
  envelope := envelope_649_i4
  height := height_649_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_649_i4
def height_649_i3 : ℕ := 8
def childrenH_649_i3 : Fin 2 → ℕ := ![height_5, height_649_i4]
theorem height_exact_649_i3 : height_649_i3 = 1 + Finset.univ.sup childrenH_649_i3 := by decide +kernel
theorem required_origin_649_i3 : ∀ x ∈ required_649_i3,
    (∃ j, x ∈ childrenC_649_i3 j) ∨ ∀ j, x ∈ childrenD_649_i3 j := by decide +kernel
theorem required_exact_649_i3 : required_649_i3 =
    ((Finset.univ.biUnion childrenC_649_i3) ∪ commonEnvelope childrenD_649_i3).erase (3, 3) := by
  exact required_eq_combination childrenC_649_i3 childrenD_649_i3 (3, 3) required_649_i3
    (by decide +kernel) child_required_sub_649_i3 common_sub_649_i3 required_origin_649_i3
theorem envelope_origin_649_i3 : ∀ x ∈ envelope_649_i3,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_649_i3 j := by decide +kernel
theorem envelope_exact_649_i3 : envelope_649_i3 =
    insert (3, 3) (Finset.univ.biUnion childrenD_649_i3) := by
  exact envelope_eq_combination childrenD_649_i3 (3, 3) envelope_649_i3
    pivot_mem_649_i3 child_envelope_sub_649_i3 envelope_origin_649_i3
def checked_649_i3 : CheckedCard where
  required := required_649_i3
  envelope := envelope_649_i3
  height := height_649_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_649_i3
def height_649_i2 : ℕ := 9
def childrenH_649_i2 : Fin 2 → ℕ := ![height_5, height_649_i3]
theorem height_exact_649_i2 : height_649_i2 = 1 + Finset.univ.sup childrenH_649_i2 := by decide +kernel
theorem required_origin_649_i2 : ∀ x ∈ required_649_i2,
    (∃ j, x ∈ childrenC_649_i2 j) ∨ ∀ j, x ∈ childrenD_649_i2 j := by decide +kernel
theorem required_exact_649_i2 : required_649_i2 =
    ((Finset.univ.biUnion childrenC_649_i2) ∪ commonEnvelope childrenD_649_i2).erase (3, 6) := by
  exact required_eq_combination childrenC_649_i2 childrenD_649_i2 (3, 6) required_649_i2
    (by decide +kernel) child_required_sub_649_i2 common_sub_649_i2 required_origin_649_i2
theorem envelope_origin_649_i2 : ∀ x ∈ envelope_649_i2,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_649_i2 j := by decide +kernel
theorem envelope_exact_649_i2 : envelope_649_i2 =
    insert (3, 6) (Finset.univ.biUnion childrenD_649_i2) := by
  exact envelope_eq_combination childrenD_649_i2 (3, 6) envelope_649_i2
    pivot_mem_649_i2 child_envelope_sub_649_i2 envelope_origin_649_i2
def checked_649_i2 : CheckedCard where
  required := required_649_i2
  envelope := envelope_649_i2
  height := height_649_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_649_i2
def height_649_i1 : ℕ := 10
def childrenH_649_i1 : Fin 4 → ℕ := ![height_19, height_84, height_314, height_649_i2]
theorem height_exact_649_i1 : height_649_i1 = 1 + Finset.univ.sup childrenH_649_i1 := by decide +kernel
theorem required_origin_649_i1 : ∀ x ∈ required_649_i1,
    (∃ j, x ∈ childrenC_649_i1 j) ∨ ∀ j, x ∈ childrenD_649_i1 j := by decide +kernel
theorem required_exact_649_i1 : required_649_i1 =
    ((Finset.univ.biUnion childrenC_649_i1) ∪ commonEnvelope childrenD_649_i1).erase (4, 6) := by
  exact required_eq_combination childrenC_649_i1 childrenD_649_i1 (4, 6) required_649_i1
    (by decide +kernel) child_required_sub_649_i1 common_sub_649_i1 required_origin_649_i1
theorem envelope_origin_649_i1 : ∀ x ∈ envelope_649_i1,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_649_i1 j := by decide +kernel
theorem envelope_exact_649_i1 : envelope_649_i1 =
    insert (4, 6) (Finset.univ.biUnion childrenD_649_i1) := by
  exact envelope_eq_combination childrenD_649_i1 (4, 6) envelope_649_i1
    pivot_mem_649_i1 child_envelope_sub_649_i1 envelope_origin_649_i1
def checked_649_i1 : CheckedCard where
  required := required_649_i1
  envelope := envelope_649_i1
  height := height_649_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_649_i1
def height_649_i0 : ℕ := 11
def childrenH_649_i0 : Fin 4 → ℕ := ![height_10, height_44, height_63, height_649_i1]
theorem height_exact_649_i0 : height_649_i0 = 1 + Finset.univ.sup childrenH_649_i0 := by decide +kernel
theorem required_origin_649_i0 : ∀ x ∈ required_649_i0,
    (∃ j, x ∈ childrenC_649_i0 j) ∨ ∀ j, x ∈ childrenD_649_i0 j := by decide +kernel
theorem required_exact_649_i0 : required_649_i0 =
    ((Finset.univ.biUnion childrenC_649_i0) ∪ commonEnvelope childrenD_649_i0).erase (4, 3) := by
  exact required_eq_combination childrenC_649_i0 childrenD_649_i0 (4, 3) required_649_i0
    (by decide +kernel) child_required_sub_649_i0 common_sub_649_i0 required_origin_649_i0
theorem envelope_origin_649_i0 : ∀ x ∈ envelope_649_i0,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_649_i0 j := by decide +kernel
theorem envelope_exact_649_i0 : envelope_649_i0 =
    insert (4, 3) (Finset.univ.biUnion childrenD_649_i0) := by
  exact envelope_eq_combination childrenD_649_i0 (4, 3) envelope_649_i0
    pivot_mem_649_i0 child_envelope_sub_649_i0 envelope_origin_649_i0
def checked_649_i0 : CheckedCard where
  required := required_649_i0
  envelope := envelope_649_i0
  height := height_649_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_649_i0
def height_649 : ℕ := 12
def childrenH_649 : Fin 3 → ℕ := ![height_52, height_523, height_649_i0]
theorem height_exact_649 : height_649 = 1 + Finset.univ.sup childrenH_649 := by decide +kernel
theorem required_origin_649 : ∀ x ∈ required_649,
    (∃ j, x ∈ childrenC_649 j) ∨ ∀ j, x ∈ childrenD_649 j := by decide +kernel
theorem required_exact_649 : required_649 =
    ((Finset.univ.biUnion childrenC_649) ∪ commonEnvelope childrenD_649).erase (4, 4) := by
  exact required_eq_combination childrenC_649 childrenD_649 (4, 4) required_649
    (by decide +kernel) child_required_sub_649 common_sub_649 required_origin_649
theorem envelope_origin_649 : ∀ x ∈ envelope_649,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_649 j := by decide +kernel
theorem envelope_exact_649 : envelope_649 =
    insert (4, 4) (Finset.univ.biUnion childrenD_649) := by
  exact envelope_eq_combination childrenD_649 (4, 4) envelope_649
    pivot_mem_649 child_envelope_sub_649 envelope_origin_649
def checked_649 : CheckedCard where
  required := required_649
  envelope := envelope_649
  height := height_649
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_649
def height_654_i1 : ℕ := 6
def childrenH_654_i1 : Fin 2 → ℕ := ![height_0, height_502]
theorem height_exact_654_i1 : height_654_i1 = 1 + Finset.univ.sup childrenH_654_i1 := by decide +kernel
theorem required_origin_654_i1 : ∀ x ∈ required_654_i1,
    (∃ j, x ∈ childrenC_654_i1 j) ∨ ∀ j, x ∈ childrenD_654_i1 j := by decide +kernel
theorem required_exact_654_i1 : required_654_i1 =
    ((Finset.univ.biUnion childrenC_654_i1) ∪ commonEnvelope childrenD_654_i1).erase (4, 6) := by
  exact required_eq_combination childrenC_654_i1 childrenD_654_i1 (4, 6) required_654_i1
    (by decide +kernel) child_required_sub_654_i1 common_sub_654_i1 required_origin_654_i1
theorem envelope_origin_654_i1 : ∀ x ∈ envelope_654_i1,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_654_i1 j := by decide +kernel
theorem envelope_exact_654_i1 : envelope_654_i1 =
    insert (4, 6) (Finset.univ.biUnion childrenD_654_i1) := by
  exact envelope_eq_combination childrenD_654_i1 (4, 6) envelope_654_i1
    pivot_mem_654_i1 child_envelope_sub_654_i1 envelope_origin_654_i1
def checked_654_i1 : CheckedCard where
  required := required_654_i1
  envelope := envelope_654_i1
  height := height_654_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_654_i1
def height_654_i0 : ℕ := 9
def childrenH_654_i0 : Fin 4 → ℕ := ![height_53, height_53, height_651, height_654_i1]
theorem height_exact_654_i0 : height_654_i0 = 1 + Finset.univ.sup childrenH_654_i0 := by decide +kernel
theorem required_origin_654_i0 : ∀ x ∈ required_654_i0,
    (∃ j, x ∈ childrenC_654_i0 j) ∨ ∀ j, x ∈ childrenD_654_i0 j := by decide +kernel
theorem required_exact_654_i0 : required_654_i0 =
    ((Finset.univ.biUnion childrenC_654_i0) ∪ commonEnvelope childrenD_654_i0).erase (4, 5) := by
  exact required_eq_combination childrenC_654_i0 childrenD_654_i0 (4, 5) required_654_i0
    (by decide +kernel) child_required_sub_654_i0 common_sub_654_i0 required_origin_654_i0
theorem envelope_origin_654_i0 : ∀ x ∈ envelope_654_i0,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_654_i0 j := by decide +kernel
theorem envelope_exact_654_i0 : envelope_654_i0 =
    insert (4, 5) (Finset.univ.biUnion childrenD_654_i0) := by
  exact envelope_eq_combination childrenD_654_i0 (4, 5) envelope_654_i0
    pivot_mem_654_i0 child_envelope_sub_654_i0 envelope_origin_654_i0
def checked_654_i0 : CheckedCard where
  required := required_654_i0
  envelope := envelope_654_i0
  height := height_654_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_654_i0
def height_654 : ℕ := 12
def childrenH_654 : Fin 8 → ℕ := ![height_248, height_300, height_436, height_449, height_509, height_510, height_653, height_654_i0]
theorem height_exact_654 : height_654 = 1 + Finset.univ.sup childrenH_654 := by decide +kernel
theorem required_origin_654 : ∀ x ∈ required_654,
    (∃ j, x ∈ childrenC_654 j) ∨ ∀ j, x ∈ childrenD_654 j := by decide +kernel
theorem required_exact_654 : required_654 =
    ((Finset.univ.biUnion childrenC_654) ∪ commonEnvelope childrenD_654).erase (4, 4) := by
  exact required_eq_combination childrenC_654 childrenD_654 (4, 4) required_654
    (by decide +kernel) child_required_sub_654 common_sub_654 required_origin_654
theorem envelope_origin_654 : ∀ x ∈ envelope_654,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_654 j := by decide +kernel
theorem envelope_exact_654 : envelope_654 =
    insert (4, 4) (Finset.univ.biUnion childrenD_654) := by
  exact envelope_eq_combination childrenD_654 (4, 4) envelope_654
    pivot_mem_654 child_envelope_sub_654 envelope_origin_654
def checked_654 : CheckedCard where
  required := required_654
  envelope := envelope_654
  height := height_654
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_654
def height_677 : ℕ := 12
def childrenH_677 : Fin 5 → ℕ := ![height_13, height_14, height_33, height_589, height_676]
theorem height_exact_677 : height_677 = 1 + Finset.univ.sup childrenH_677 := by decide +kernel
theorem required_origin_677 : ∀ x ∈ required_677,
    (∃ j, x ∈ childrenC_677 j) ∨ ∀ j, x ∈ childrenD_677 j := by decide +kernel
theorem required_exact_677 : required_677 =
    ((Finset.univ.biUnion childrenC_677) ∪ commonEnvelope childrenD_677).erase (3, 3) := by
  exact required_eq_combination childrenC_677 childrenD_677 (3, 3) required_677
    (by decide +kernel) child_required_sub_677 common_sub_677 required_origin_677
theorem envelope_origin_677 : ∀ x ∈ envelope_677,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_677 j := by decide +kernel
theorem envelope_exact_677 : envelope_677 =
    insert (3, 3) (Finset.univ.biUnion childrenD_677) := by
  exact envelope_eq_combination childrenD_677 (3, 3) envelope_677
    pivot_mem_677 child_envelope_sub_677 envelope_origin_677
def checked_677 : CheckedCard where
  required := required_677
  envelope := envelope_677
  height := height_677
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_677
def height_687 : ℕ := 12
def childrenH_687 : Fin 4 → ℕ := ![height_44, height_324, height_685, height_686]
theorem height_exact_687 : height_687 = 1 + Finset.univ.sup childrenH_687 := by decide +kernel
theorem required_origin_687 : ∀ x ∈ required_687,
    (∃ j, x ∈ childrenC_687 j) ∨ ∀ j, x ∈ childrenD_687 j := by decide +kernel
theorem required_exact_687 : required_687 =
    ((Finset.univ.biUnion childrenC_687) ∪ commonEnvelope childrenD_687).erase (5, 5) := by
  exact required_eq_combination childrenC_687 childrenD_687 (5, 5) required_687
    (by decide +kernel) child_required_sub_687 common_sub_687 required_origin_687
theorem envelope_origin_687 : ∀ x ∈ envelope_687,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_687 j := by decide +kernel
theorem envelope_exact_687 : envelope_687 =
    insert (5, 5) (Finset.univ.biUnion childrenD_687) := by
  exact envelope_eq_combination childrenD_687 (5, 5) envelope_687
    pivot_mem_687 child_envelope_sub_687 envelope_origin_687
def checked_687 : CheckedCard where
  required := required_687
  envelope := envelope_687
  height := height_687
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_687
end SnakyPrototype.Certificate21

end OAI
