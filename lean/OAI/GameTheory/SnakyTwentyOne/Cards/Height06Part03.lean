import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part04
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_336_i1 : Finset Cell := ⟨(([(0, 1), (1, 2), (1, 3), (1, 4), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_336_i1 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 5), (0, 6), (0, 7), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 2), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_336_i1 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) required_4), (placed21 2 (2, 2) required_37)]
def childrenD_336_i1 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) envelope_4), (placed21 2 (2, 2) envelope_37)]
theorem common_sub_336_i1 : commonEnvelope childrenD_336_i1 ⊆ insert (1, 5) required_336_i1 := by decide +kernel
theorem child_required_sub_336_i1 : ∀ j, childrenC_336_i1 j ⊆ insert (1, 5) required_336_i1 := by decide +kernel
theorem child_envelope_sub_336_i1 : ∀ j, childrenD_336_i1 j ⊆ envelope_336_i1 := by decide +kernel
theorem pivot_mem_336_i1 : (1, 5) ∈ envelope_336_i1 := by decide +kernel
theorem children_work_336_i1 : ∀ j, Template HasSnaky 3 (childrenC_336_i1 j) (childrenD_336_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 7 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_37 2 (2, 2)).mono (by decide +kernel)
theorem row_works_336_i1 : Template HasSnaky 4 required_336_i1 envelope_336_i1 := by
  refine compose HasSnaky 3 childrenC_336_i1 childrenD_336_i1 children_work_336_i1 (1, 5)
    required_336_i1 envelope_336_i1 pivot_mem_336_i1 child_required_sub_336_i1 child_envelope_sub_336_i1 ?_
  intro b hb
  exact common_sub_336_i1 (mem_commonEnvelope childrenD_336_i1 b hb)
def required_336_i0 : Finset Cell := ⟨(([(0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_336_i0 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 5), (0, 6), (0, 7), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 2), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_336_i0 : Fin 2 → Finset Cell := ![(placed21 1 (1, 0) required_5), required_336_i1]
def childrenD_336_i0 : Fin 2 → Finset Cell := ![(placed21 1 (1, 0) envelope_5), envelope_336_i1]
theorem common_sub_336_i0 : commonEnvelope childrenD_336_i0 ⊆ insert (2, 3) required_336_i0 := by decide +kernel
theorem child_required_sub_336_i0 : ∀ j, childrenC_336_i0 j ⊆ insert (2, 3) required_336_i0 := by decide +kernel
theorem child_envelope_sub_336_i0 : ∀ j, childrenD_336_i0 j ⊆ envelope_336_i0 := by decide +kernel
theorem pivot_mem_336_i0 : (2, 3) ∈ envelope_336_i0 := by decide +kernel
theorem children_work_336_i0 : ∀ j, Template HasSnaky 4 (childrenC_336_i0 j) (childrenD_336_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (1, 0)).mono (by decide +kernel)
  · exact row_works_336_i1.mono (by decide +kernel)
theorem row_works_336_i0 : Template HasSnaky 5 required_336_i0 envelope_336_i0 := by
  refine compose HasSnaky 4 childrenC_336_i0 childrenD_336_i0 children_work_336_i0 (2, 3)
    required_336_i0 envelope_336_i0 pivot_mem_336_i0 child_required_sub_336_i0 child_envelope_sub_336_i0 ?_
  intro b hb
  exact common_sub_336_i0 (mem_commonEnvelope childrenD_336_i0 b hb)
def required_336 : Finset Cell := ⟨(([(0, 1), (1, 0), (1, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_336 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 5), (0, 6), (0, 7), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_336 : Fin 3 → Finset Cell := ![(placed21 0 (1, 0) required_6), (placed21 0 (0, 1) required_18), required_336_i0]
def childrenD_336 : Fin 3 → Finset Cell := ![(placed21 0 (1, 0) envelope_6), (placed21 0 (0, 1) envelope_18), envelope_336_i0]
theorem common_sub_336 : commonEnvelope childrenD_336 ⊆ insert (1, 4) required_336 := by decide +kernel
theorem child_required_sub_336 : ∀ j, childrenC_336 j ⊆ insert (1, 4) required_336 := by decide +kernel
theorem child_envelope_sub_336 : ∀ j, childrenD_336 j ⊆ envelope_336 := by decide +kernel
theorem pivot_mem_336 : (1, 4) ∈ envelope_336 := by decide +kernel
theorem children_work_336 : ∀ j, Template HasSnaky 5 (childrenC_336 j) (childrenD_336 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_18 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_336_i0.mono (by decide +kernel)
theorem row_works_336 : Template HasSnaky 6 required_336 envelope_336 := by
  refine compose HasSnaky 5 childrenC_336 childrenD_336 children_work_336 (1, 4)
    required_336 envelope_336 pivot_mem_336 child_required_sub_336 child_envelope_sub_336 ?_
  intro b hb
  exact common_sub_336 (mem_commonEnvelope childrenD_336 b hb)
def required_340_i0 : Finset Cell := ⟨(([(0, 3), (0, 6), (1, 3), (1, 4), (1, 5), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_340_i0 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 6), (0, 7), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 4), (2, 5), (2, 7), (2, 8), (2, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_340_i0 : Fin 2 → Finset Cell := ![(placed21 5 (1, 3) required_5), (placed21 0 (0, 3) required_91)]
def childrenD_340_i0 : Fin 2 → Finset Cell := ![(placed21 5 (1, 3) envelope_5), (placed21 0 (0, 3) envelope_91)]
theorem common_sub_340_i0 : commonEnvelope childrenD_340_i0 ⊆ insert (1, 6) required_340_i0 := by decide +kernel
theorem child_required_sub_340_i0 : ∀ j, childrenC_340_i0 j ⊆ insert (1, 6) required_340_i0 := by decide +kernel
theorem child_envelope_sub_340_i0 : ∀ j, childrenD_340_i0 j ⊆ envelope_340_i0 := by decide +kernel
theorem pivot_mem_340_i0 : (1, 6) ∈ envelope_340_i0 := by decide +kernel
theorem children_work_340_i0 : ∀ j, Template HasSnaky 4 (childrenC_340_i0 j) (childrenD_340_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_91 0 (0, 3)).mono (by decide +kernel)
theorem row_works_340_i0 : Template HasSnaky 5 required_340_i0 envelope_340_i0 := by
  refine compose HasSnaky 4 childrenC_340_i0 childrenD_340_i0 children_work_340_i0 (1, 6)
    required_340_i0 envelope_340_i0 pivot_mem_340_i0 child_required_sub_340_i0 child_envelope_sub_340_i0 ?_
  intro b hb
  exact common_sub_340_i0 (mem_commonEnvelope childrenD_340_i0 b hb)
def required_340 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (1, 5), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_340 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 7), (2, 8), (2, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_340 : Fin 3 → Finset Cell := ![(placed21 2 (1, 2) required_139), (placed21 4 (0, 6) required_148), required_340_i0]
def childrenD_340 : Fin 3 → Finset Cell := ![(placed21 2 (1, 2) envelope_139), (placed21 4 (0, 6) envelope_148), envelope_340_i0]
theorem common_sub_340 : commonEnvelope childrenD_340 ⊆ insert (0, 6) required_340 := by decide +kernel
theorem child_required_sub_340 : ∀ j, childrenC_340 j ⊆ insert (0, 6) required_340 := by decide +kernel
theorem child_envelope_sub_340 : ∀ j, childrenD_340 j ⊆ envelope_340 := by decide +kernel
theorem pivot_mem_340 : (0, 6) ∈ envelope_340 := by decide +kernel
theorem children_work_340 : ∀ j, Template HasSnaky 5 (childrenC_340 j) (childrenD_340 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_139 2 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_148 4 (0, 6)).mono (by decide +kernel)
  · exact row_works_340_i0.mono (by decide +kernel)
theorem row_works_340 : Template HasSnaky 6 required_340 envelope_340 := by
  refine compose HasSnaky 5 childrenC_340 childrenD_340 children_work_340 (0, 6)
    required_340 envelope_340 pivot_mem_340 child_required_sub_340 child_envelope_sub_340 ?_
  intro b hb
  exact common_sub_340 (mem_commonEnvelope childrenD_340 b hb)
def required_343 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 2), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_343 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_343 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) required_5), required_342]
def childrenD_343 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) envelope_5), envelope_342]
theorem common_sub_343 : commonEnvelope childrenD_343 ⊆ insert (3, 3) required_343 := by decide +kernel
theorem child_required_sub_343 : ∀ j, childrenC_343 j ⊆ insert (3, 3) required_343 := by decide +kernel
theorem child_envelope_sub_343 : ∀ j, childrenD_343 j ⊆ envelope_343 := by decide +kernel
theorem pivot_mem_343 : (3, 3) ∈ envelope_343 := by decide +kernel
theorem children_work_343 : ∀ j, Template HasSnaky 5 (childrenC_343 j) (childrenD_343 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 2)).mono (by decide +kernel)
  · exact row_works_342.mono (by decide +kernel)
theorem row_works_343 : Template HasSnaky 6 required_343 envelope_343 := by
  refine compose HasSnaky 5 childrenC_343 childrenD_343 children_work_343 (3, 3)
    required_343 envelope_343 pivot_mem_343 child_required_sub_343 child_envelope_sub_343 ?_
  intro b hb
  exact common_sub_343 (mem_commonEnvelope childrenD_343 b hb)
def required_346 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_346 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_346 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) required_0), (placed21 4 (0, 5) required_342)]
def childrenD_346 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) envelope_0), (placed21 4 (0, 5) envelope_342)]
theorem common_sub_346 : commonEnvelope childrenD_346 ⊆ insert (2, 3) required_346 := by decide +kernel
theorem child_required_sub_346 : ∀ j, childrenC_346 j ⊆ insert (2, 3) required_346 := by decide +kernel
theorem child_envelope_sub_346 : ∀ j, childrenD_346 j ⊆ envelope_346 := by decide +kernel
theorem pivot_mem_346 : (2, 3) ∈ envelope_346 := by decide +kernel
theorem children_work_346 : ∀ j, Template HasSnaky 5 (childrenC_346 j) (childrenD_346 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_342 4 (0, 5)).mono (by decide +kernel)
theorem row_works_346 : Template HasSnaky 6 required_346 envelope_346 := by
  refine compose HasSnaky 5 childrenC_346 childrenD_346 children_work_346 (2, 3)
    required_346 envelope_346 pivot_mem_346 child_required_sub_346 child_envelope_sub_346 ?_
  intro b hb
  exact common_sub_346 (mem_commonEnvelope childrenD_346 b hb)
def required_348_i0 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 4), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_348_i0 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_348_i0 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) required_5), (placed21 1 (2, 0) required_311)]
def childrenD_348_i0 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) envelope_5), (placed21 1 (2, 0) envelope_311)]
theorem common_sub_348_i0 : commonEnvelope childrenD_348_i0 ⊆ insert (3, 0) required_348_i0 := by decide +kernel
theorem child_required_sub_348_i0 : ∀ j, childrenC_348_i0 j ⊆ insert (3, 0) required_348_i0 := by decide +kernel
theorem child_envelope_sub_348_i0 : ∀ j, childrenD_348_i0 j ⊆ envelope_348_i0 := by decide +kernel
theorem pivot_mem_348_i0 : (3, 0) ∈ envelope_348_i0 := by decide +kernel
theorem children_work_348_i0 : ∀ j, Template HasSnaky 4 (childrenC_348_i0 j) (childrenD_348_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_311 1 (2, 0)).mono (by decide +kernel)
theorem row_works_348_i0 : Template HasSnaky 5 required_348_i0 envelope_348_i0 := by
  refine compose HasSnaky 4 childrenC_348_i0 childrenD_348_i0 children_work_348_i0 (3, 0)
    required_348_i0 envelope_348_i0 pivot_mem_348_i0 child_required_sub_348_i0 child_envelope_sub_348_i0 ?_
  intro b hb
  exact common_sub_348_i0 (mem_commonEnvelope childrenD_348_i0 b hb)
def required_348 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 4), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_348 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 2), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_348 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_5), required_348_i0]
def childrenD_348 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_5), envelope_348_i0]
theorem common_sub_348 : commonEnvelope childrenD_348 ⊆ insert (3, 1) required_348 := by decide +kernel
theorem child_required_sub_348 : ∀ j, childrenC_348 j ⊆ insert (3, 1) required_348 := by decide +kernel
theorem child_envelope_sub_348 : ∀ j, childrenD_348 j ⊆ envelope_348 := by decide +kernel
theorem pivot_mem_348 : (3, 1) ∈ envelope_348 := by decide +kernel
theorem children_work_348 : ∀ j, Template HasSnaky 5 (childrenC_348 j) (childrenD_348 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_348_i0.mono (by decide +kernel)
theorem row_works_348 : Template HasSnaky 6 required_348 envelope_348 := by
  refine compose HasSnaky 5 childrenC_348 childrenD_348 children_work_348 (3, 1)
    required_348 envelope_348 pivot_mem_348 child_required_sub_348 child_envelope_sub_348 ?_
  intro b hb
  exact common_sub_348 (mem_commonEnvelope childrenD_348 b hb)
def required_349_i0 : Finset Cell := ⟨(([(1, 4), (3, 3), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_349_i0 : Finset Cell := ⟨(([(0, 4), (1, 4), (2, 4), (2, 6), (2, 7), (2, 8), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 6), (4, 7), (4, 8), (5, 3), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_349_i0 : Fin 2 → Finset Cell := ![(placed21 2 (4, 2) required_10), (placed21 3 (0, 4) required_54)]
def childrenD_349_i0 : Fin 2 → Finset Cell := ![(placed21 2 (4, 2) envelope_10), (placed21 3 (0, 4) envelope_54)]
theorem common_sub_349_i0 : commonEnvelope childrenD_349_i0 ⊆ insert (4, 3) required_349_i0 := by decide +kernel
theorem child_required_sub_349_i0 : ∀ j, childrenC_349_i0 j ⊆ insert (4, 3) required_349_i0 := by decide +kernel
theorem child_envelope_sub_349_i0 : ∀ j, childrenD_349_i0 j ⊆ envelope_349_i0 := by decide +kernel
theorem pivot_mem_349_i0 : (4, 3) ∈ envelope_349_i0 := by decide +kernel
theorem children_work_349_i0 : ∀ j, Template HasSnaky 4 (childrenC_349_i0 j) (childrenD_349_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_54 3 (0, 4)).mono (by decide +kernel)
theorem row_works_349_i0 : Template HasSnaky 5 required_349_i0 envelope_349_i0 := by
  refine compose HasSnaky 4 childrenC_349_i0 childrenD_349_i0 children_work_349_i0 (4, 3)
    required_349_i0 envelope_349_i0 pivot_mem_349_i0 child_required_sub_349_i0 child_envelope_sub_349_i0 ?_
  intro b hb
  exact common_sub_349_i0 (mem_commonEnvelope childrenD_349_i0 b hb)
def required_349 : Finset Cell := ⟨(([(1, 4), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_349 : Finset Cell := ⟨(([(0, 4), (1, 4), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 3), (5, 5), (6, 3), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_349 : Fin 4 → Finset Cell := ![(placed21 2 (4, 1) required_12), (placed21 0 (0, 2) required_165), (placed21 4 (0, 6) required_216), required_349_i0]
def childrenD_349 : Fin 4 → Finset Cell := ![(placed21 2 (4, 1) envelope_12), (placed21 0 (0, 2) envelope_165), (placed21 4 (0, 6) envelope_216), envelope_349_i0]
theorem common_sub_349 : commonEnvelope childrenD_349 ⊆ insert (3, 5) required_349 := by decide +kernel
theorem child_required_sub_349 : ∀ j, childrenC_349 j ⊆ insert (3, 5) required_349 := by decide +kernel
theorem child_envelope_sub_349 : ∀ j, childrenD_349 j ⊆ envelope_349 := by decide +kernel
theorem pivot_mem_349 : (3, 5) ∈ envelope_349 := by decide +kernel
theorem children_work_349 : ∀ j, Template HasSnaky 5 (childrenC_349 j) (childrenD_349 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 2 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_165 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_216 4 (0, 6)).mono (by decide +kernel)
  · exact row_works_349_i0.mono (by decide +kernel)
theorem row_works_349 : Template HasSnaky 6 required_349 envelope_349 := by
  refine compose HasSnaky 5 childrenC_349 childrenD_349 children_work_349 (3, 5)
    required_349 envelope_349 pivot_mem_349 child_required_sub_349 child_envelope_sub_349 ?_
  intro b hb
  exact common_sub_349 (mem_commonEnvelope childrenD_349 b hb)
def required_358 : Finset Cell := ⟨(([(0, 1), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_358 : Finset Cell := ⟨(([(0, 1), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 2), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_358 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) required_5), (placed21 3 (0, 4) required_357)]
def childrenD_358 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) envelope_5), (placed21 3 (0, 4) envelope_357)]
theorem common_sub_358 : commonEnvelope childrenD_358 ⊆ insert (2, 4) required_358 := by decide +kernel
theorem child_required_sub_358 : ∀ j, childrenC_358 j ⊆ insert (2, 4) required_358 := by decide +kernel
theorem child_envelope_sub_358 : ∀ j, childrenD_358 j ⊆ envelope_358 := by decide +kernel
theorem pivot_mem_358 : (2, 4) ∈ envelope_358 := by decide +kernel
theorem children_work_358 : ∀ j, Template HasSnaky 5 (childrenC_358 j) (childrenD_358 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_357 3 (0, 4)).mono (by decide +kernel)
theorem row_works_358 : Template HasSnaky 6 required_358 envelope_358 := by
  refine compose HasSnaky 5 childrenC_358 childrenD_358 children_work_358 (2, 4)
    required_358 envelope_358 pivot_mem_358 child_required_sub_358 child_envelope_sub_358 ?_
  intro b hb
  exact common_sub_358 (mem_commonEnvelope childrenD_358 b hb)
def required_360_i0 : Finset Cell := ⟨(([(1, 1), (1, 2), (2, 1), (2, 2), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_360_i0 : Finset Cell := ⟨(([(0, 2), (1, 0), (1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (4, 1), (5, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_360_i0 : Fin 2 → Finset Cell := ![(placed21 7 (2, 4) required_5), (placed21 3 (0, 4) required_45)]
def childrenD_360_i0 : Fin 2 → Finset Cell := ![(placed21 7 (2, 4) envelope_5), (placed21 3 (0, 4) envelope_45)]
theorem common_sub_360_i0 : commonEnvelope childrenD_360_i0 ⊆ insert (2, 3) required_360_i0 := by decide +kernel
theorem child_required_sub_360_i0 : ∀ j, childrenC_360_i0 j ⊆ insert (2, 3) required_360_i0 := by decide +kernel
theorem child_envelope_sub_360_i0 : ∀ j, childrenD_360_i0 j ⊆ envelope_360_i0 := by decide +kernel
theorem pivot_mem_360_i0 : (2, 3) ∈ envelope_360_i0 := by decide +kernel
theorem children_work_360_i0 : ∀ j, Template HasSnaky 3 (childrenC_360_i0 j) (childrenD_360_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_45 3 (0, 4)).mono (by decide +kernel)
theorem row_works_360_i0 : Template HasSnaky 4 required_360_i0 envelope_360_i0 := by
  refine compose HasSnaky 3 childrenC_360_i0 childrenD_360_i0 children_work_360_i0 (2, 3)
    required_360_i0 envelope_360_i0 pivot_mem_360_i0 child_required_sub_360_i0 child_envelope_sub_360_i0 ?_
  intro b hb
  exact common_sub_360_i0 (mem_commonEnvelope childrenD_360_i0 b hb)
def required_360 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (2, 1), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_360 : Finset Cell := ⟨(([(0, 2), (1, 0), (1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (5, 1), (5, 2), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_360 : Fin 3 → Finset Cell := ![(placed21 2 (2, 0) required_22), (placed21 1 (0, 1) required_347), required_360_i0]
def childrenD_360 : Fin 3 → Finset Cell := ![(placed21 2 (2, 0) envelope_22), (placed21 1 (0, 1) envelope_347), envelope_360_i0]
theorem common_sub_360 : commonEnvelope childrenD_360 ⊆ insert (2, 4) required_360 := by decide +kernel
theorem child_required_sub_360 : ∀ j, childrenC_360 j ⊆ insert (2, 4) required_360 := by decide +kernel
theorem child_envelope_sub_360 : ∀ j, childrenD_360 j ⊆ envelope_360 := by decide +kernel
theorem pivot_mem_360 : (2, 4) ∈ envelope_360 := by decide +kernel
theorem children_work_360 : ∀ j, Template HasSnaky 5 (childrenC_360 j) (childrenD_360 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_22 2 (2, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_347 1 (0, 1)).mono (by decide +kernel)
  · exact row_works_360_i0.mono (by decide +kernel)
theorem row_works_360 : Template HasSnaky 6 required_360 envelope_360 := by
  refine compose HasSnaky 5 childrenC_360 childrenD_360 children_work_360 (2, 4)
    required_360 envelope_360 pivot_mem_360 child_required_sub_360 child_envelope_sub_360 ?_
  intro b hb
  exact common_sub_360 (mem_commonEnvelope childrenD_360 b hb)
def required_363 : Finset Cell := ⟨(([(0, 2), (0, 3), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_363 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_363 : Fin 2 → Finset Cell := ![(placed21 0 (3, 1) required_44), required_362]
def childrenD_363 : Fin 2 → Finset Cell := ![(placed21 0 (3, 1) envelope_44), envelope_362]
theorem common_sub_363 : commonEnvelope childrenD_363 ⊆ insert (4, 4) required_363 := by decide +kernel
theorem child_required_sub_363 : ∀ j, childrenC_363 j ⊆ insert (4, 4) required_363 := by decide +kernel
theorem child_envelope_sub_363 : ∀ j, childrenD_363 j ⊆ envelope_363 := by decide +kernel
theorem pivot_mem_363 : (4, 4) ∈ envelope_363 := by decide +kernel
theorem children_work_363 : ∀ j, Template HasSnaky 5 (childrenC_363 j) (childrenD_363 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 0 (3, 1)).mono (by decide +kernel)
  · exact row_works_362.mono (by decide +kernel)
theorem row_works_363 : Template HasSnaky 6 required_363 envelope_363 := by
  refine compose HasSnaky 5 childrenC_363 childrenD_363 children_work_363 (4, 4)
    required_363 envelope_363 pivot_mem_363 child_required_sub_363 child_envelope_sub_363 ?_
  intro b hb
  exact common_sub_363 (mem_commonEnvelope childrenD_363 b hb)
def required_364 : Finset Cell := ⟨(([(0, 2), (0, 3), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_364 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_364 : Fin 2 → Finset Cell := ![(placed21 0 (3, 1) required_52), required_362]
def childrenD_364 : Fin 2 → Finset Cell := ![(placed21 0 (3, 1) envelope_52), envelope_362]
theorem common_sub_364 : commonEnvelope childrenD_364 ⊆ insert (4, 4) required_364 := by decide +kernel
theorem child_required_sub_364 : ∀ j, childrenC_364 j ⊆ insert (4, 4) required_364 := by decide +kernel
theorem child_envelope_sub_364 : ∀ j, childrenD_364 j ⊆ envelope_364 := by decide +kernel
theorem pivot_mem_364 : (4, 4) ∈ envelope_364 := by decide +kernel
theorem children_work_364 : ∀ j, Template HasSnaky 5 (childrenC_364 j) (childrenD_364 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 0 (3, 1)).mono (by decide +kernel)
  · exact row_works_362.mono (by decide +kernel)
theorem row_works_364 : Template HasSnaky 6 required_364 envelope_364 := by
  refine compose HasSnaky 5 childrenC_364 childrenD_364 children_work_364 (4, 4)
    required_364 envelope_364 pivot_mem_364 child_required_sub_364 child_envelope_sub_364 ?_
  intro b hb
  exact common_sub_364 (mem_commonEnvelope childrenD_364 b hb)
def required_367 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_367 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 5), (0, 6), (0, 7), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_367 : Fin 3 → Finset Cell := ![(placed21 1 (0, 2) required_8), (placed21 6 (2, 6) required_9), required_366]
def childrenD_367 : Fin 3 → Finset Cell := ![(placed21 1 (0, 2) envelope_8), (placed21 6 (2, 6) envelope_9), envelope_366]
theorem common_sub_367 : commonEnvelope childrenD_367 ⊆ insert (1, 5) required_367 := by decide +kernel
theorem child_required_sub_367 : ∀ j, childrenC_367 j ⊆ insert (1, 5) required_367 := by decide +kernel
theorem child_envelope_sub_367 : ∀ j, childrenD_367 j ⊆ envelope_367 := by decide +kernel
theorem pivot_mem_367 : (1, 5) ∈ envelope_367 := by decide +kernel
theorem children_work_367 : ∀ j, Template HasSnaky 5 (childrenC_367 j) (childrenD_367 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 6 (2, 6)).mono (by decide +kernel)
  · exact row_works_366.mono (by decide +kernel)
theorem row_works_367 : Template HasSnaky 6 required_367 envelope_367 := by
  refine compose HasSnaky 5 childrenC_367 childrenD_367 children_work_367 (1, 5)
    required_367 envelope_367 pivot_mem_367 child_required_sub_367 child_envelope_sub_367 ?_
  intro b hb
  exact common_sub_367 (mem_commonEnvelope childrenD_367 b hb)
def required_369_i0 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_369_i0 : Finset Cell := ⟨(([(0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 7), (2, 8), (2, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_369_i0 : Fin 3 → Finset Cell := ![(placed21 2 (1, 3) required_6), (placed21 1 (0, 4) required_8), (placed21 0 (0, 2) required_365)]
def childrenD_369_i0 : Fin 3 → Finset Cell := ![(placed21 2 (1, 3) envelope_6), (placed21 1 (0, 4) envelope_8), (placed21 0 (0, 2) envelope_365)]
theorem common_sub_369_i0 : commonEnvelope childrenD_369_i0 ⊆ insert (1, 7) required_369_i0 := by decide +kernel
theorem child_required_sub_369_i0 : ∀ j, childrenC_369_i0 j ⊆ insert (1, 7) required_369_i0 := by decide +kernel
theorem child_envelope_sub_369_i0 : ∀ j, childrenD_369_i0 j ⊆ envelope_369_i0 := by decide +kernel
theorem pivot_mem_369_i0 : (1, 7) ∈ envelope_369_i0 := by decide +kernel
theorem children_work_369_i0 : ∀ j, Template HasSnaky 4 (childrenC_369_i0 j) (childrenD_369_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 2 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 1 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_365 0 (0, 2)).mono (by decide +kernel)
theorem row_works_369_i0 : Template HasSnaky 5 required_369_i0 envelope_369_i0 := by
  refine compose HasSnaky 4 childrenC_369_i0 childrenD_369_i0 children_work_369_i0 (1, 7)
    required_369_i0 envelope_369_i0 pivot_mem_369_i0 child_required_sub_369_i0 child_envelope_sub_369_i0 ?_
  intro b hb
  exact common_sub_369_i0 (mem_commonEnvelope childrenD_369_i0 b hb)
def required_369 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_369 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 7), (2, 8), (2, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_369 : Fin 4 → Finset Cell := ![(placed21 6 (1, 7) required_7), (placed21 0 (0, 2) required_19), (placed21 6 (1, 8) required_187), required_369_i0]
def childrenD_369 : Fin 4 → Finset Cell := ![(placed21 6 (1, 7) envelope_7), (placed21 0 (0, 2) envelope_19), (placed21 6 (1, 8) envelope_187), envelope_369_i0]
theorem common_sub_369 : commonEnvelope childrenD_369 ⊆ insert (1, 6) required_369 := by decide +kernel
theorem child_required_sub_369 : ∀ j, childrenC_369 j ⊆ insert (1, 6) required_369 := by decide +kernel
theorem child_envelope_sub_369 : ∀ j, childrenD_369 j ⊆ envelope_369 := by decide +kernel
theorem pivot_mem_369 : (1, 6) ∈ envelope_369 := by decide +kernel
theorem children_work_369 : ∀ j, Template HasSnaky 5 (childrenC_369 j) (childrenD_369 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 6 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_19 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_187 6 (1, 8)).mono (by decide +kernel)
  · exact row_works_369_i0.mono (by decide +kernel)
theorem row_works_369 : Template HasSnaky 6 required_369 envelope_369 := by
  refine compose HasSnaky 5 childrenC_369 childrenD_369 children_work_369 (1, 6)
    required_369 envelope_369 pivot_mem_369 child_required_sub_369 child_envelope_sub_369 ?_
  intro b hb
  exact common_sub_369 (mem_commonEnvelope childrenD_369 b hb)
def required_371_i2 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 2), (3, 1), (4, 1), (5, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_371_i2 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 2), (3, 1), (3, 2), (4, 1), (4, 2), (5, 1), (6, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_371_i2 : Fin 2 → Finset Cell := ![(placed21 2 (6, 1) required_0), (placed21 0 (0, 1) required_5)]
def childrenD_371_i2 : Fin 2 → Finset Cell := ![(placed21 2 (6, 1) envelope_0), (placed21 0 (0, 1) envelope_5)]
theorem common_sub_371_i2 : commonEnvelope childrenD_371_i2 ⊆ insert (3, 2) required_371_i2 := by decide +kernel
theorem child_required_sub_371_i2 : ∀ j, childrenC_371_i2 j ⊆ insert (3, 2) required_371_i2 := by decide +kernel
theorem child_envelope_sub_371_i2 : ∀ j, childrenD_371_i2 j ⊆ envelope_371_i2 := by decide +kernel
theorem pivot_mem_371_i2 : (3, 2) ∈ envelope_371_i2 := by decide +kernel
theorem children_work_371_i2 : ∀ j, Template HasSnaky 1 (childrenC_371_i2 j) (childrenD_371_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 2 (6, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 0 (0, 1)).mono (by decide +kernel)
theorem row_works_371_i2 : Template HasSnaky 2 required_371_i2 envelope_371_i2 := by
  refine compose HasSnaky 1 childrenC_371_i2 childrenD_371_i2 children_work_371_i2 (3, 2)
    required_371_i2 envelope_371_i2 pivot_mem_371_i2 child_required_sub_371_i2 child_envelope_sub_371_i2 ?_
  intro b hb
  exact common_sub_371_i2 (mem_commonEnvelope childrenD_371_i2 b hb)
def required_371_i1 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 4), (3, 1), (4, 1), (5, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_371_i1 : Finset Cell := ⟨(([(0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 1), (3, 2), (4, 1), (4, 2), (5, 1), (6, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_371_i1 : Fin 2 → Finset Cell := ![(placed21 0 (1, 0) required_210), required_371_i2]
def childrenD_371_i1 : Fin 2 → Finset Cell := ![(placed21 0 (1, 0) envelope_210), envelope_371_i2]
theorem common_sub_371_i1 : commonEnvelope childrenD_371_i1 ⊆ insert (2, 2) required_371_i1 := by decide +kernel
theorem child_required_sub_371_i1 : ∀ j, childrenC_371_i1 j ⊆ insert (2, 2) required_371_i1 := by decide +kernel
theorem child_envelope_sub_371_i1 : ∀ j, childrenD_371_i1 j ⊆ envelope_371_i1 := by decide +kernel
theorem pivot_mem_371_i1 : (2, 2) ∈ envelope_371_i1 := by decide +kernel
theorem children_work_371_i1 : ∀ j, Template HasSnaky 2 (childrenC_371_i1 j) (childrenD_371_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_210 0 (1, 0)).mono (by decide +kernel)
  · exact row_works_371_i2.mono (by decide +kernel)
theorem row_works_371_i1 : Template HasSnaky 3 required_371_i1 envelope_371_i1 := by
  refine compose HasSnaky 2 childrenC_371_i1 childrenD_371_i1 children_work_371_i1 (2, 2)
    required_371_i1 envelope_371_i1 pivot_mem_371_i1 child_required_sub_371_i1 child_envelope_sub_371_i1 ?_
  intro b hb
  exact common_sub_371_i1 (mem_commonEnvelope childrenD_371_i1 b hb)
def required_371_i0 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 4), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_371_i0 : Finset Cell := ⟨(([(0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (6, 0), (6, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_371_i0 : Fin 2 → Finset Cell := ![(placed21 3 (1, 1) required_6), required_371_i1]
def childrenD_371_i0 : Fin 2 → Finset Cell := ![(placed21 3 (1, 1) envelope_6), envelope_371_i1]
theorem common_sub_371_i0 : commonEnvelope childrenD_371_i0 ⊆ insert (5, 1) required_371_i0 := by decide +kernel
theorem child_required_sub_371_i0 : ∀ j, childrenC_371_i0 j ⊆ insert (5, 1) required_371_i0 := by decide +kernel
theorem child_envelope_sub_371_i0 : ∀ j, childrenD_371_i0 j ⊆ envelope_371_i0 := by decide +kernel
theorem pivot_mem_371_i0 : (5, 1) ∈ envelope_371_i0 := by decide +kernel
theorem children_work_371_i0 : ∀ j, Template HasSnaky 3 (childrenC_371_i0 j) (childrenD_371_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 3 (1, 1)).mono (by decide +kernel)
  · exact row_works_371_i1.mono (by decide +kernel)
theorem row_works_371_i0 : Template HasSnaky 4 required_371_i0 envelope_371_i0 := by
  refine compose HasSnaky 3 childrenC_371_i0 childrenD_371_i0 children_work_371_i0 (5, 1)
    required_371_i0 envelope_371_i0 pivot_mem_371_i0 child_required_sub_371_i0 child_envelope_sub_371_i0 ?_
  intro b hb
  exact common_sub_371_i0 (mem_commonEnvelope childrenD_371_i0 b hb)
def required_371 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 4), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_371 : Finset Cell := ⟨(([(0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1), (6, 2), (7, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_371 : Fin 4 → Finset Cell := ![(placed21 1 (0, 1) required_6), (placed21 0 (1, 0) required_8), (placed21 0 (1, 0) required_370), required_371_i0]
def childrenD_371 : Fin 4 → Finset Cell := ![(placed21 1 (0, 1) envelope_6), (placed21 0 (1, 0) envelope_8), (placed21 0 (1, 0) envelope_370), envelope_371_i0]
theorem common_sub_371 : commonEnvelope childrenD_371 ⊆ insert (4, 1) required_371 := by decide +kernel
theorem child_required_sub_371 : ∀ j, childrenC_371 j ⊆ insert (4, 1) required_371 := by decide +kernel
theorem child_envelope_sub_371 : ∀ j, childrenD_371 j ⊆ envelope_371 := by decide +kernel
theorem pivot_mem_371 : (4, 1) ∈ envelope_371 := by decide +kernel
theorem children_work_371 : ∀ j, Template HasSnaky 5 (childrenC_371 j) (childrenD_371 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_370 0 (1, 0)).mono (by decide +kernel)
  · exact row_works_371_i0.mono (by decide +kernel)
theorem row_works_371 : Template HasSnaky 6 required_371 envelope_371 := by
  refine compose HasSnaky 5 childrenC_371 childrenD_371 children_work_371 (4, 1)
    required_371 envelope_371 pivot_mem_371 child_required_sub_371 child_envelope_sub_371 ?_
  intro b hb
  exact common_sub_371 (mem_commonEnvelope childrenD_371 b hb)
def height_336_i1 : ℕ := 4
def childrenH_336_i1 : Fin 2 → ℕ := ![height_4, height_37]
theorem height_exact_336_i1 : height_336_i1 = 1 + Finset.univ.sup childrenH_336_i1 := by decide +kernel
theorem required_origin_336_i1 : ∀ x ∈ required_336_i1,
    (∃ j, x ∈ childrenC_336_i1 j) ∨ ∀ j, x ∈ childrenD_336_i1 j := by decide +kernel
theorem required_exact_336_i1 : required_336_i1 =
    ((Finset.univ.biUnion childrenC_336_i1) ∪ commonEnvelope childrenD_336_i1).erase (1, 5) := by
  exact required_eq_combination childrenC_336_i1 childrenD_336_i1 (1, 5) required_336_i1
    (by decide +kernel) child_required_sub_336_i1 common_sub_336_i1 required_origin_336_i1
theorem envelope_origin_336_i1 : ∀ x ∈ envelope_336_i1,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_336_i1 j := by decide +kernel
theorem envelope_exact_336_i1 : envelope_336_i1 =
    insert (1, 5) (Finset.univ.biUnion childrenD_336_i1) := by
  exact envelope_eq_combination childrenD_336_i1 (1, 5) envelope_336_i1
    pivot_mem_336_i1 child_envelope_sub_336_i1 envelope_origin_336_i1
def checked_336_i1 : CheckedCard where
  required := required_336_i1
  envelope := envelope_336_i1
  height := height_336_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_336_i1
def height_336_i0 : ℕ := 5
def childrenH_336_i0 : Fin 2 → ℕ := ![height_5, height_336_i1]
theorem height_exact_336_i0 : height_336_i0 = 1 + Finset.univ.sup childrenH_336_i0 := by decide +kernel
theorem required_origin_336_i0 : ∀ x ∈ required_336_i0,
    (∃ j, x ∈ childrenC_336_i0 j) ∨ ∀ j, x ∈ childrenD_336_i0 j := by decide +kernel
theorem required_exact_336_i0 : required_336_i0 =
    ((Finset.univ.biUnion childrenC_336_i0) ∪ commonEnvelope childrenD_336_i0).erase (2, 3) := by
  exact required_eq_combination childrenC_336_i0 childrenD_336_i0 (2, 3) required_336_i0
    (by decide +kernel) child_required_sub_336_i0 common_sub_336_i0 required_origin_336_i0
theorem envelope_origin_336_i0 : ∀ x ∈ envelope_336_i0,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_336_i0 j := by decide +kernel
theorem envelope_exact_336_i0 : envelope_336_i0 =
    insert (2, 3) (Finset.univ.biUnion childrenD_336_i0) := by
  exact envelope_eq_combination childrenD_336_i0 (2, 3) envelope_336_i0
    pivot_mem_336_i0 child_envelope_sub_336_i0 envelope_origin_336_i0
def checked_336_i0 : CheckedCard where
  required := required_336_i0
  envelope := envelope_336_i0
  height := height_336_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_336_i0
def height_336 : ℕ := 6
def childrenH_336 : Fin 3 → ℕ := ![height_6, height_18, height_336_i0]
theorem height_exact_336 : height_336 = 1 + Finset.univ.sup childrenH_336 := by decide +kernel
theorem required_origin_336 : ∀ x ∈ required_336,
    (∃ j, x ∈ childrenC_336 j) ∨ ∀ j, x ∈ childrenD_336 j := by decide +kernel
theorem required_exact_336 : required_336 =
    ((Finset.univ.biUnion childrenC_336) ∪ commonEnvelope childrenD_336).erase (1, 4) := by
  exact required_eq_combination childrenC_336 childrenD_336 (1, 4) required_336
    (by decide +kernel) child_required_sub_336 common_sub_336 required_origin_336
theorem envelope_origin_336 : ∀ x ∈ envelope_336,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_336 j := by decide +kernel
theorem envelope_exact_336 : envelope_336 =
    insert (1, 4) (Finset.univ.biUnion childrenD_336) := by
  exact envelope_eq_combination childrenD_336 (1, 4) envelope_336
    pivot_mem_336 child_envelope_sub_336 envelope_origin_336
def checked_336 : CheckedCard where
  required := required_336
  envelope := envelope_336
  height := height_336
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_336
def height_340_i0 : ℕ := 5
def childrenH_340_i0 : Fin 2 → ℕ := ![height_5, height_91]
theorem height_exact_340_i0 : height_340_i0 = 1 + Finset.univ.sup childrenH_340_i0 := by decide +kernel
theorem required_origin_340_i0 : ∀ x ∈ required_340_i0,
    (∃ j, x ∈ childrenC_340_i0 j) ∨ ∀ j, x ∈ childrenD_340_i0 j := by decide +kernel
theorem required_exact_340_i0 : required_340_i0 =
    ((Finset.univ.biUnion childrenC_340_i0) ∪ commonEnvelope childrenD_340_i0).erase (1, 6) := by
  exact required_eq_combination childrenC_340_i0 childrenD_340_i0 (1, 6) required_340_i0
    (by decide +kernel) child_required_sub_340_i0 common_sub_340_i0 required_origin_340_i0
theorem envelope_origin_340_i0 : ∀ x ∈ envelope_340_i0,
    x = (1, 6) ∨ ∃ j, x ∈ childrenD_340_i0 j := by decide +kernel
theorem envelope_exact_340_i0 : envelope_340_i0 =
    insert (1, 6) (Finset.univ.biUnion childrenD_340_i0) := by
  exact envelope_eq_combination childrenD_340_i0 (1, 6) envelope_340_i0
    pivot_mem_340_i0 child_envelope_sub_340_i0 envelope_origin_340_i0
def checked_340_i0 : CheckedCard where
  required := required_340_i0
  envelope := envelope_340_i0
  height := height_340_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_340_i0
def height_340 : ℕ := 6
def childrenH_340 : Fin 3 → ℕ := ![height_139, height_148, height_340_i0]
theorem height_exact_340 : height_340 = 1 + Finset.univ.sup childrenH_340 := by decide +kernel
theorem required_origin_340 : ∀ x ∈ required_340,
    (∃ j, x ∈ childrenC_340 j) ∨ ∀ j, x ∈ childrenD_340 j := by decide +kernel
theorem required_exact_340 : required_340 =
    ((Finset.univ.biUnion childrenC_340) ∪ commonEnvelope childrenD_340).erase (0, 6) := by
  exact required_eq_combination childrenC_340 childrenD_340 (0, 6) required_340
    (by decide +kernel) child_required_sub_340 common_sub_340 required_origin_340
theorem envelope_origin_340 : ∀ x ∈ envelope_340,
    x = (0, 6) ∨ ∃ j, x ∈ childrenD_340 j := by decide +kernel
theorem envelope_exact_340 : envelope_340 =
    insert (0, 6) (Finset.univ.biUnion childrenD_340) := by
  exact envelope_eq_combination childrenD_340 (0, 6) envelope_340
    pivot_mem_340 child_envelope_sub_340 envelope_origin_340
def checked_340 : CheckedCard where
  required := required_340
  envelope := envelope_340
  height := height_340
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_340
def height_343 : ℕ := 6
def childrenH_343 : Fin 2 → ℕ := ![height_5, height_342]
theorem height_exact_343 : height_343 = 1 + Finset.univ.sup childrenH_343 := by decide +kernel
theorem required_origin_343 : ∀ x ∈ required_343,
    (∃ j, x ∈ childrenC_343 j) ∨ ∀ j, x ∈ childrenD_343 j := by decide +kernel
theorem required_exact_343 : required_343 =
    ((Finset.univ.biUnion childrenC_343) ∪ commonEnvelope childrenD_343).erase (3, 3) := by
  exact required_eq_combination childrenC_343 childrenD_343 (3, 3) required_343
    (by decide +kernel) child_required_sub_343 common_sub_343 required_origin_343
theorem envelope_origin_343 : ∀ x ∈ envelope_343,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_343 j := by decide +kernel
theorem envelope_exact_343 : envelope_343 =
    insert (3, 3) (Finset.univ.biUnion childrenD_343) := by
  exact envelope_eq_combination childrenD_343 (3, 3) envelope_343
    pivot_mem_343 child_envelope_sub_343 envelope_origin_343
def checked_343 : CheckedCard where
  required := required_343
  envelope := envelope_343
  height := height_343
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_343
def height_346 : ℕ := 6
def childrenH_346 : Fin 2 → ℕ := ![height_0, height_342]
theorem height_exact_346 : height_346 = 1 + Finset.univ.sup childrenH_346 := by decide +kernel
theorem required_origin_346 : ∀ x ∈ required_346,
    (∃ j, x ∈ childrenC_346 j) ∨ ∀ j, x ∈ childrenD_346 j := by decide +kernel
theorem required_exact_346 : required_346 =
    ((Finset.univ.biUnion childrenC_346) ∪ commonEnvelope childrenD_346).erase (2, 3) := by
  exact required_eq_combination childrenC_346 childrenD_346 (2, 3) required_346
    (by decide +kernel) child_required_sub_346 common_sub_346 required_origin_346
theorem envelope_origin_346 : ∀ x ∈ envelope_346,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_346 j := by decide +kernel
theorem envelope_exact_346 : envelope_346 =
    insert (2, 3) (Finset.univ.biUnion childrenD_346) := by
  exact envelope_eq_combination childrenD_346 (2, 3) envelope_346
    pivot_mem_346 child_envelope_sub_346 envelope_origin_346
def checked_346 : CheckedCard where
  required := required_346
  envelope := envelope_346
  height := height_346
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_346
def height_348_i0 : ℕ := 5
def childrenH_348_i0 : Fin 2 → ℕ := ![height_5, height_311]
theorem height_exact_348_i0 : height_348_i0 = 1 + Finset.univ.sup childrenH_348_i0 := by decide +kernel
theorem required_origin_348_i0 : ∀ x ∈ required_348_i0,
    (∃ j, x ∈ childrenC_348_i0 j) ∨ ∀ j, x ∈ childrenD_348_i0 j := by decide +kernel
theorem required_exact_348_i0 : required_348_i0 =
    ((Finset.univ.biUnion childrenC_348_i0) ∪ commonEnvelope childrenD_348_i0).erase (3, 0) := by
  exact required_eq_combination childrenC_348_i0 childrenD_348_i0 (3, 0) required_348_i0
    (by decide +kernel) child_required_sub_348_i0 common_sub_348_i0 required_origin_348_i0
theorem envelope_origin_348_i0 : ∀ x ∈ envelope_348_i0,
    x = (3, 0) ∨ ∃ j, x ∈ childrenD_348_i0 j := by decide +kernel
theorem envelope_exact_348_i0 : envelope_348_i0 =
    insert (3, 0) (Finset.univ.biUnion childrenD_348_i0) := by
  exact envelope_eq_combination childrenD_348_i0 (3, 0) envelope_348_i0
    pivot_mem_348_i0 child_envelope_sub_348_i0 envelope_origin_348_i0
def checked_348_i0 : CheckedCard where
  required := required_348_i0
  envelope := envelope_348_i0
  height := height_348_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_348_i0
def height_348 : ℕ := 6
def childrenH_348 : Fin 2 → ℕ := ![height_5, height_348_i0]
theorem height_exact_348 : height_348 = 1 + Finset.univ.sup childrenH_348 := by decide +kernel
theorem required_origin_348 : ∀ x ∈ required_348,
    (∃ j, x ∈ childrenC_348 j) ∨ ∀ j, x ∈ childrenD_348 j := by decide +kernel
theorem required_exact_348 : required_348 =
    ((Finset.univ.biUnion childrenC_348) ∪ commonEnvelope childrenD_348).erase (3, 1) := by
  exact required_eq_combination childrenC_348 childrenD_348 (3, 1) required_348
    (by decide +kernel) child_required_sub_348 common_sub_348 required_origin_348
theorem envelope_origin_348 : ∀ x ∈ envelope_348,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_348 j := by decide +kernel
theorem envelope_exact_348 : envelope_348 =
    insert (3, 1) (Finset.univ.biUnion childrenD_348) := by
  exact envelope_eq_combination childrenD_348 (3, 1) envelope_348
    pivot_mem_348 child_envelope_sub_348 envelope_origin_348
def checked_348 : CheckedCard where
  required := required_348
  envelope := envelope_348
  height := height_348
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_348
def height_349_i0 : ℕ := 5
def childrenH_349_i0 : Fin 2 → ℕ := ![height_10, height_54]
theorem height_exact_349_i0 : height_349_i0 = 1 + Finset.univ.sup childrenH_349_i0 := by decide +kernel
theorem required_origin_349_i0 : ∀ x ∈ required_349_i0,
    (∃ j, x ∈ childrenC_349_i0 j) ∨ ∀ j, x ∈ childrenD_349_i0 j := by decide +kernel
theorem required_exact_349_i0 : required_349_i0 =
    ((Finset.univ.biUnion childrenC_349_i0) ∪ commonEnvelope childrenD_349_i0).erase (4, 3) := by
  exact required_eq_combination childrenC_349_i0 childrenD_349_i0 (4, 3) required_349_i0
    (by decide +kernel) child_required_sub_349_i0 common_sub_349_i0 required_origin_349_i0
theorem envelope_origin_349_i0 : ∀ x ∈ envelope_349_i0,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_349_i0 j := by decide +kernel
theorem envelope_exact_349_i0 : envelope_349_i0 =
    insert (4, 3) (Finset.univ.biUnion childrenD_349_i0) := by
  exact envelope_eq_combination childrenD_349_i0 (4, 3) envelope_349_i0
    pivot_mem_349_i0 child_envelope_sub_349_i0 envelope_origin_349_i0
def checked_349_i0 : CheckedCard where
  required := required_349_i0
  envelope := envelope_349_i0
  height := height_349_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_349_i0
def height_349 : ℕ := 6
def childrenH_349 : Fin 4 → ℕ := ![height_12, height_165, height_216, height_349_i0]
theorem height_exact_349 : height_349 = 1 + Finset.univ.sup childrenH_349 := by decide +kernel
theorem required_origin_349 : ∀ x ∈ required_349,
    (∃ j, x ∈ childrenC_349 j) ∨ ∀ j, x ∈ childrenD_349 j := by decide +kernel
theorem required_exact_349 : required_349 =
    ((Finset.univ.biUnion childrenC_349) ∪ commonEnvelope childrenD_349).erase (3, 5) := by
  exact required_eq_combination childrenC_349 childrenD_349 (3, 5) required_349
    (by decide +kernel) child_required_sub_349 common_sub_349 required_origin_349
theorem envelope_origin_349 : ∀ x ∈ envelope_349,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_349 j := by decide +kernel
theorem envelope_exact_349 : envelope_349 =
    insert (3, 5) (Finset.univ.biUnion childrenD_349) := by
  exact envelope_eq_combination childrenD_349 (3, 5) envelope_349
    pivot_mem_349 child_envelope_sub_349 envelope_origin_349
def checked_349 : CheckedCard where
  required := required_349
  envelope := envelope_349
  height := height_349
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_349
def height_358 : ℕ := 6
def childrenH_358 : Fin 2 → ℕ := ![height_5, height_357]
theorem height_exact_358 : height_358 = 1 + Finset.univ.sup childrenH_358 := by decide +kernel
theorem required_origin_358 : ∀ x ∈ required_358,
    (∃ j, x ∈ childrenC_358 j) ∨ ∀ j, x ∈ childrenD_358 j := by decide +kernel
theorem required_exact_358 : required_358 =
    ((Finset.univ.biUnion childrenC_358) ∪ commonEnvelope childrenD_358).erase (2, 4) := by
  exact required_eq_combination childrenC_358 childrenD_358 (2, 4) required_358
    (by decide +kernel) child_required_sub_358 common_sub_358 required_origin_358
theorem envelope_origin_358 : ∀ x ∈ envelope_358,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_358 j := by decide +kernel
theorem envelope_exact_358 : envelope_358 =
    insert (2, 4) (Finset.univ.biUnion childrenD_358) := by
  exact envelope_eq_combination childrenD_358 (2, 4) envelope_358
    pivot_mem_358 child_envelope_sub_358 envelope_origin_358
def checked_358 : CheckedCard where
  required := required_358
  envelope := envelope_358
  height := height_358
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_358
def height_360_i0 : ℕ := 4
def childrenH_360_i0 : Fin 2 → ℕ := ![height_5, height_45]
theorem height_exact_360_i0 : height_360_i0 = 1 + Finset.univ.sup childrenH_360_i0 := by decide +kernel
theorem required_origin_360_i0 : ∀ x ∈ required_360_i0,
    (∃ j, x ∈ childrenC_360_i0 j) ∨ ∀ j, x ∈ childrenD_360_i0 j := by decide +kernel
theorem required_exact_360_i0 : required_360_i0 =
    ((Finset.univ.biUnion childrenC_360_i0) ∪ commonEnvelope childrenD_360_i0).erase (2, 3) := by
  exact required_eq_combination childrenC_360_i0 childrenD_360_i0 (2, 3) required_360_i0
    (by decide +kernel) child_required_sub_360_i0 common_sub_360_i0 required_origin_360_i0
theorem envelope_origin_360_i0 : ∀ x ∈ envelope_360_i0,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_360_i0 j := by decide +kernel
theorem envelope_exact_360_i0 : envelope_360_i0 =
    insert (2, 3) (Finset.univ.biUnion childrenD_360_i0) := by
  exact envelope_eq_combination childrenD_360_i0 (2, 3) envelope_360_i0
    pivot_mem_360_i0 child_envelope_sub_360_i0 envelope_origin_360_i0
def checked_360_i0 : CheckedCard where
  required := required_360_i0
  envelope := envelope_360_i0
  height := height_360_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_360_i0
def height_360 : ℕ := 6
def childrenH_360 : Fin 3 → ℕ := ![height_22, height_347, height_360_i0]
theorem height_exact_360 : height_360 = 1 + Finset.univ.sup childrenH_360 := by decide +kernel
theorem required_origin_360 : ∀ x ∈ required_360,
    (∃ j, x ∈ childrenC_360 j) ∨ ∀ j, x ∈ childrenD_360 j := by decide +kernel
theorem required_exact_360 : required_360 =
    ((Finset.univ.biUnion childrenC_360) ∪ commonEnvelope childrenD_360).erase (2, 4) := by
  exact required_eq_combination childrenC_360 childrenD_360 (2, 4) required_360
    (by decide +kernel) child_required_sub_360 common_sub_360 required_origin_360
theorem envelope_origin_360 : ∀ x ∈ envelope_360,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_360 j := by decide +kernel
theorem envelope_exact_360 : envelope_360 =
    insert (2, 4) (Finset.univ.biUnion childrenD_360) := by
  exact envelope_eq_combination childrenD_360 (2, 4) envelope_360
    pivot_mem_360 child_envelope_sub_360 envelope_origin_360
def checked_360 : CheckedCard where
  required := required_360
  envelope := envelope_360
  height := height_360
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_360
def height_363 : ℕ := 6
def childrenH_363 : Fin 2 → ℕ := ![height_44, height_362]
theorem height_exact_363 : height_363 = 1 + Finset.univ.sup childrenH_363 := by decide +kernel
theorem required_origin_363 : ∀ x ∈ required_363,
    (∃ j, x ∈ childrenC_363 j) ∨ ∀ j, x ∈ childrenD_363 j := by decide +kernel
theorem required_exact_363 : required_363 =
    ((Finset.univ.biUnion childrenC_363) ∪ commonEnvelope childrenD_363).erase (4, 4) := by
  exact required_eq_combination childrenC_363 childrenD_363 (4, 4) required_363
    (by decide +kernel) child_required_sub_363 common_sub_363 required_origin_363
theorem envelope_origin_363 : ∀ x ∈ envelope_363,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_363 j := by decide +kernel
theorem envelope_exact_363 : envelope_363 =
    insert (4, 4) (Finset.univ.biUnion childrenD_363) := by
  exact envelope_eq_combination childrenD_363 (4, 4) envelope_363
    pivot_mem_363 child_envelope_sub_363 envelope_origin_363
def checked_363 : CheckedCard where
  required := required_363
  envelope := envelope_363
  height := height_363
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_363
def height_364 : ℕ := 6
def childrenH_364 : Fin 2 → ℕ := ![height_52, height_362]
theorem height_exact_364 : height_364 = 1 + Finset.univ.sup childrenH_364 := by decide +kernel
theorem required_origin_364 : ∀ x ∈ required_364,
    (∃ j, x ∈ childrenC_364 j) ∨ ∀ j, x ∈ childrenD_364 j := by decide +kernel
theorem required_exact_364 : required_364 =
    ((Finset.univ.biUnion childrenC_364) ∪ commonEnvelope childrenD_364).erase (4, 4) := by
  exact required_eq_combination childrenC_364 childrenD_364 (4, 4) required_364
    (by decide +kernel) child_required_sub_364 common_sub_364 required_origin_364
theorem envelope_origin_364 : ∀ x ∈ envelope_364,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_364 j := by decide +kernel
theorem envelope_exact_364 : envelope_364 =
    insert (4, 4) (Finset.univ.biUnion childrenD_364) := by
  exact envelope_eq_combination childrenD_364 (4, 4) envelope_364
    pivot_mem_364 child_envelope_sub_364 envelope_origin_364
def checked_364 : CheckedCard where
  required := required_364
  envelope := envelope_364
  height := height_364
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_364
def height_367 : ℕ := 6
def childrenH_367 : Fin 3 → ℕ := ![height_8, height_9, height_366]
theorem height_exact_367 : height_367 = 1 + Finset.univ.sup childrenH_367 := by decide +kernel
theorem required_origin_367 : ∀ x ∈ required_367,
    (∃ j, x ∈ childrenC_367 j) ∨ ∀ j, x ∈ childrenD_367 j := by decide +kernel
theorem required_exact_367 : required_367 =
    ((Finset.univ.biUnion childrenC_367) ∪ commonEnvelope childrenD_367).erase (1, 5) := by
  exact required_eq_combination childrenC_367 childrenD_367 (1, 5) required_367
    (by decide +kernel) child_required_sub_367 common_sub_367 required_origin_367
theorem envelope_origin_367 : ∀ x ∈ envelope_367,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_367 j := by decide +kernel
theorem envelope_exact_367 : envelope_367 =
    insert (1, 5) (Finset.univ.biUnion childrenD_367) := by
  exact envelope_eq_combination childrenD_367 (1, 5) envelope_367
    pivot_mem_367 child_envelope_sub_367 envelope_origin_367
def checked_367 : CheckedCard where
  required := required_367
  envelope := envelope_367
  height := height_367
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_367
def height_369_i0 : ℕ := 5
def childrenH_369_i0 : Fin 3 → ℕ := ![height_6, height_8, height_365]
theorem height_exact_369_i0 : height_369_i0 = 1 + Finset.univ.sup childrenH_369_i0 := by decide +kernel
theorem required_origin_369_i0 : ∀ x ∈ required_369_i0,
    (∃ j, x ∈ childrenC_369_i0 j) ∨ ∀ j, x ∈ childrenD_369_i0 j := by decide +kernel
theorem required_exact_369_i0 : required_369_i0 =
    ((Finset.univ.biUnion childrenC_369_i0) ∪ commonEnvelope childrenD_369_i0).erase (1, 7) := by
  exact required_eq_combination childrenC_369_i0 childrenD_369_i0 (1, 7) required_369_i0
    (by decide +kernel) child_required_sub_369_i0 common_sub_369_i0 required_origin_369_i0
theorem envelope_origin_369_i0 : ∀ x ∈ envelope_369_i0,
    x = (1, 7) ∨ ∃ j, x ∈ childrenD_369_i0 j := by decide +kernel
theorem envelope_exact_369_i0 : envelope_369_i0 =
    insert (1, 7) (Finset.univ.biUnion childrenD_369_i0) := by
  exact envelope_eq_combination childrenD_369_i0 (1, 7) envelope_369_i0
    pivot_mem_369_i0 child_envelope_sub_369_i0 envelope_origin_369_i0
def checked_369_i0 : CheckedCard where
  required := required_369_i0
  envelope := envelope_369_i0
  height := height_369_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_369_i0
def height_369 : ℕ := 6
def childrenH_369 : Fin 4 → ℕ := ![height_7, height_19, height_187, height_369_i0]
theorem height_exact_369 : height_369 = 1 + Finset.univ.sup childrenH_369 := by decide +kernel
theorem required_origin_369 : ∀ x ∈ required_369,
    (∃ j, x ∈ childrenC_369 j) ∨ ∀ j, x ∈ childrenD_369 j := by decide +kernel
theorem required_exact_369 : required_369 =
    ((Finset.univ.biUnion childrenC_369) ∪ commonEnvelope childrenD_369).erase (1, 6) := by
  exact required_eq_combination childrenC_369 childrenD_369 (1, 6) required_369
    (by decide +kernel) child_required_sub_369 common_sub_369 required_origin_369
theorem envelope_origin_369 : ∀ x ∈ envelope_369,
    x = (1, 6) ∨ ∃ j, x ∈ childrenD_369 j := by decide +kernel
theorem envelope_exact_369 : envelope_369 =
    insert (1, 6) (Finset.univ.biUnion childrenD_369) := by
  exact envelope_eq_combination childrenD_369 (1, 6) envelope_369
    pivot_mem_369 child_envelope_sub_369 envelope_origin_369
def checked_369 : CheckedCard where
  required := required_369
  envelope := envelope_369
  height := height_369
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_369
def height_371_i2 : ℕ := 2
def childrenH_371_i2 : Fin 2 → ℕ := ![height_0, height_5]
theorem height_exact_371_i2 : height_371_i2 = 1 + Finset.univ.sup childrenH_371_i2 := by decide +kernel
theorem required_origin_371_i2 : ∀ x ∈ required_371_i2,
    (∃ j, x ∈ childrenC_371_i2 j) ∨ ∀ j, x ∈ childrenD_371_i2 j := by decide +kernel
theorem required_exact_371_i2 : required_371_i2 =
    ((Finset.univ.biUnion childrenC_371_i2) ∪ commonEnvelope childrenD_371_i2).erase (3, 2) := by
  exact required_eq_combination childrenC_371_i2 childrenD_371_i2 (3, 2) required_371_i2
    (by decide +kernel) child_required_sub_371_i2 common_sub_371_i2 required_origin_371_i2
theorem envelope_origin_371_i2 : ∀ x ∈ envelope_371_i2,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_371_i2 j := by decide +kernel
theorem envelope_exact_371_i2 : envelope_371_i2 =
    insert (3, 2) (Finset.univ.biUnion childrenD_371_i2) := by
  exact envelope_eq_combination childrenD_371_i2 (3, 2) envelope_371_i2
    pivot_mem_371_i2 child_envelope_sub_371_i2 envelope_origin_371_i2
def checked_371_i2 : CheckedCard where
  required := required_371_i2
  envelope := envelope_371_i2
  height := height_371_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_371_i2
def height_371_i1 : ℕ := 3
def childrenH_371_i1 : Fin 2 → ℕ := ![height_210, height_371_i2]
theorem height_exact_371_i1 : height_371_i1 = 1 + Finset.univ.sup childrenH_371_i1 := by decide +kernel
theorem required_origin_371_i1 : ∀ x ∈ required_371_i1,
    (∃ j, x ∈ childrenC_371_i1 j) ∨ ∀ j, x ∈ childrenD_371_i1 j := by decide +kernel
theorem required_exact_371_i1 : required_371_i1 =
    ((Finset.univ.biUnion childrenC_371_i1) ∪ commonEnvelope childrenD_371_i1).erase (2, 2) := by
  exact required_eq_combination childrenC_371_i1 childrenD_371_i1 (2, 2) required_371_i1
    (by decide +kernel) child_required_sub_371_i1 common_sub_371_i1 required_origin_371_i1
theorem envelope_origin_371_i1 : ∀ x ∈ envelope_371_i1,
    x = (2, 2) ∨ ∃ j, x ∈ childrenD_371_i1 j := by decide +kernel
theorem envelope_exact_371_i1 : envelope_371_i1 =
    insert (2, 2) (Finset.univ.biUnion childrenD_371_i1) := by
  exact envelope_eq_combination childrenD_371_i1 (2, 2) envelope_371_i1
    pivot_mem_371_i1 child_envelope_sub_371_i1 envelope_origin_371_i1
def checked_371_i1 : CheckedCard where
  required := required_371_i1
  envelope := envelope_371_i1
  height := height_371_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_371_i1
def height_371_i0 : ℕ := 4
def childrenH_371_i0 : Fin 2 → ℕ := ![height_6, height_371_i1]
theorem height_exact_371_i0 : height_371_i0 = 1 + Finset.univ.sup childrenH_371_i0 := by decide +kernel
theorem required_origin_371_i0 : ∀ x ∈ required_371_i0,
    (∃ j, x ∈ childrenC_371_i0 j) ∨ ∀ j, x ∈ childrenD_371_i0 j := by decide +kernel
theorem required_exact_371_i0 : required_371_i0 =
    ((Finset.univ.biUnion childrenC_371_i0) ∪ commonEnvelope childrenD_371_i0).erase (5, 1) := by
  exact required_eq_combination childrenC_371_i0 childrenD_371_i0 (5, 1) required_371_i0
    (by decide +kernel) child_required_sub_371_i0 common_sub_371_i0 required_origin_371_i0
theorem envelope_origin_371_i0 : ∀ x ∈ envelope_371_i0,
    x = (5, 1) ∨ ∃ j, x ∈ childrenD_371_i0 j := by decide +kernel
theorem envelope_exact_371_i0 : envelope_371_i0 =
    insert (5, 1) (Finset.univ.biUnion childrenD_371_i0) := by
  exact envelope_eq_combination childrenD_371_i0 (5, 1) envelope_371_i0
    pivot_mem_371_i0 child_envelope_sub_371_i0 envelope_origin_371_i0
def checked_371_i0 : CheckedCard where
  required := required_371_i0
  envelope := envelope_371_i0
  height := height_371_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_371_i0
def height_371 : ℕ := 6
def childrenH_371 : Fin 4 → ℕ := ![height_6, height_8, height_370, height_371_i0]
theorem height_exact_371 : height_371 = 1 + Finset.univ.sup childrenH_371 := by decide +kernel
theorem required_origin_371 : ∀ x ∈ required_371,
    (∃ j, x ∈ childrenC_371 j) ∨ ∀ j, x ∈ childrenD_371 j := by decide +kernel
theorem required_exact_371 : required_371 =
    ((Finset.univ.biUnion childrenC_371) ∪ commonEnvelope childrenD_371).erase (4, 1) := by
  exact required_eq_combination childrenC_371 childrenD_371 (4, 1) required_371
    (by decide +kernel) child_required_sub_371 common_sub_371 required_origin_371
theorem envelope_origin_371 : ∀ x ∈ envelope_371,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_371 j := by decide +kernel
theorem envelope_exact_371 : envelope_371 =
    insert (4, 1) (Finset.univ.biUnion childrenD_371) := by
  exact envelope_eq_combination childrenD_371 (4, 1) envelope_371
    pivot_mem_371 child_envelope_sub_371 envelope_origin_371
def checked_371 : CheckedCard where
  required := required_371
  envelope := envelope_371
  height := height_371
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_371
end SnakyPrototype.Certificate21

end OAI
