import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part03
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_673_i0 : Finset Cell := ⟨(([(1, 3), (1, 6), (2, 3), (2, 4), (2, 6), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_673_i0 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 6), (2, 7), (3, 3), (3, 4), (4, 3), (4, 4), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_673_i0 : Fin 2 → Finset Cell := ![(placed21 0 (1, 3) required_30), (placed21 3 (1, 4) required_74)]
def childrenD_673_i0 : Fin 2 → Finset Cell := ![(placed21 0 (1, 3) envelope_30), (placed21 3 (1, 4) envelope_74)]
theorem common_sub_673_i0 : commonEnvelope childrenD_673_i0 ⊆ insert (1, 4) required_673_i0 := by decide +kernel
theorem child_required_sub_673_i0 : ∀ j, childrenC_673_i0 j ⊆ insert (1, 4) required_673_i0 := by decide +kernel
theorem child_envelope_sub_673_i0 : ∀ j, childrenD_673_i0 j ⊆ envelope_673_i0 := by decide +kernel
theorem pivot_mem_673_i0 : (1, 4) ∈ envelope_673_i0 := by decide +kernel
theorem children_work_673_i0 : ∀ j, Template HasSnaky 3 (childrenC_673_i0 j) (childrenD_673_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_30 0 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_74 3 (1, 4)).mono (by decide +kernel)
theorem row_works_673_i0 : Template HasSnaky 4 required_673_i0 envelope_673_i0 := by
  refine compose HasSnaky 3 childrenC_673_i0 childrenD_673_i0 children_work_673_i0 (1, 4)
    required_673_i0 envelope_673_i0 pivot_mem_673_i0 child_required_sub_673_i0 child_envelope_sub_673_i0 ?_
  intro b hb
  exact common_sub_673_i0 (mem_commonEnvelope childrenD_673_i0 b hb)
def required_673_i3 : Finset Cell := ⟨(([(1, 4), (1, 6), (2, 4), (2, 6), (3, 4), (4, 4), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_673_i3 : Finset Cell := ⟨(([(1, 4), (1, 6), (2, 4), (2, 6), (2, 7), (3, 4), (3, 7), (3, 8), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 3), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_673_i3 : Fin 2 → Finset Cell := ![(placed21 0 (1, 4) required_5), (placed21 0 (1, 3) required_260)]
def childrenD_673_i3 : Fin 2 → Finset Cell := ![(placed21 0 (1, 4) envelope_5), (placed21 0 (1, 3) envelope_260)]
theorem common_sub_673_i3 : commonEnvelope childrenD_673_i3 ⊆ insert (4, 5) required_673_i3 := by decide +kernel
theorem child_required_sub_673_i3 : ∀ j, childrenC_673_i3 j ⊆ insert (4, 5) required_673_i3 := by decide +kernel
theorem child_envelope_sub_673_i3 : ∀ j, childrenD_673_i3 j ⊆ envelope_673_i3 := by decide +kernel
theorem pivot_mem_673_i3 : (4, 5) ∈ envelope_673_i3 := by decide +kernel
theorem children_work_673_i3 : ∀ j, Template HasSnaky 5 (childrenC_673_i3 j) (childrenD_673_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_260 0 (1, 3)).mono (by decide +kernel)
theorem row_works_673_i3 : Template HasSnaky 6 required_673_i3 envelope_673_i3 := by
  refine compose HasSnaky 5 childrenC_673_i3 childrenD_673_i3 children_work_673_i3 (4, 5)
    required_673_i3 envelope_673_i3 pivot_mem_673_i3 child_required_sub_673_i3 child_envelope_sub_673_i3 ?_
  intro b hb
  exact common_sub_673_i3 (mem_commonEnvelope childrenD_673_i3 b hb)
def required_673_i2 : Finset Cell := ⟨(([(1, 6), (2, 3), (2, 4), (2, 6), (3, 4), (4, 4), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_673_i2 : Finset Cell := ⟨(([(0, 5), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 6), (2, 7), (3, 4), (3, 7), (3, 8), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 3), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_673_i2 : Fin 2 → Finset Cell := ![(placed21 2 (4, 3) required_38), required_673_i3]
def childrenD_673_i2 : Fin 2 → Finset Cell := ![(placed21 2 (4, 3) envelope_38), envelope_673_i3]
theorem common_sub_673_i2 : commonEnvelope childrenD_673_i2 ⊆ insert (1, 4) required_673_i2 := by decide +kernel
theorem child_required_sub_673_i2 : ∀ j, childrenC_673_i2 j ⊆ insert (1, 4) required_673_i2 := by decide +kernel
theorem child_envelope_sub_673_i2 : ∀ j, childrenD_673_i2 j ⊆ envelope_673_i2 := by decide +kernel
theorem pivot_mem_673_i2 : (1, 4) ∈ envelope_673_i2 := by decide +kernel
theorem children_work_673_i2 : ∀ j, Template HasSnaky 6 (childrenC_673_i2 j) (childrenD_673_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_38 2 (4, 3)).mono (by decide +kernel)
  · exact row_works_673_i3.mono (by decide +kernel)
theorem row_works_673_i2 : Template HasSnaky 7 required_673_i2 envelope_673_i2 := by
  refine compose HasSnaky 6 childrenC_673_i2 childrenD_673_i2 children_work_673_i2 (1, 4)
    required_673_i2 envelope_673_i2 pivot_mem_673_i2 child_required_sub_673_i2 child_envelope_sub_673_i2 ?_
  intro b hb
  exact common_sub_673_i2 (mem_commonEnvelope childrenD_673_i2 b hb)
def required_673_i1 : Finset Cell := ⟨(([(1, 3), (1, 6), (2, 3), (2, 4), (2, 6), (4, 4), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_673_i1 : Finset Cell := ⟨(([(0, 5), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 6), (2, 7), (3, 4), (3, 7), (3, 8), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_673_i1 : Fin 2 → Finset Cell := ![(placed21 6 (5, 4) required_0), required_673_i2]
def childrenD_673_i1 : Fin 2 → Finset Cell := ![(placed21 6 (5, 4) envelope_0), envelope_673_i2]
theorem common_sub_673_i1 : commonEnvelope childrenD_673_i1 ⊆ insert (3, 4) required_673_i1 := by decide +kernel
theorem child_required_sub_673_i1 : ∀ j, childrenC_673_i1 j ⊆ insert (3, 4) required_673_i1 := by decide +kernel
theorem child_envelope_sub_673_i1 : ∀ j, childrenD_673_i1 j ⊆ envelope_673_i1 := by decide +kernel
theorem pivot_mem_673_i1 : (3, 4) ∈ envelope_673_i1 := by decide +kernel
theorem children_work_673_i1 : ∀ j, Template HasSnaky 7 (childrenC_673_i1 j) (childrenD_673_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (5, 4)).mono (by decide +kernel)
  · exact row_works_673_i2.mono (by decide +kernel)
theorem row_works_673_i1 : Template HasSnaky 8 required_673_i1 envelope_673_i1 := by
  refine compose HasSnaky 7 childrenC_673_i1 childrenD_673_i1 children_work_673_i1 (3, 4)
    required_673_i1 envelope_673_i1 pivot_mem_673_i1 child_required_sub_673_i1 child_envelope_sub_673_i1 ?_
  intro b hb
  exact common_sub_673_i1 (mem_commonEnvelope childrenD_673_i1 b hb)
def required_673_i4 : Finset Cell := ⟨(([(1, 6), (2, 3), (2, 6), (4, 4), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_673_i4 : Finset Cell := ⟨(([(1, 3), (1, 6), (2, 3), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 4), (6, 6), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_673_i4 : Fin 5 → Finset Cell := ![(placed21 0 (2, 2) required_188), (placed21 6 (6, 8) required_190), (placed21 7 (6, 7) required_230), (placed21 0 (1, 3) required_263), (placed21 4 (1, 8) required_306)]
def childrenD_673_i4 : Fin 5 → Finset Cell := ![(placed21 0 (2, 2) envelope_188), (placed21 6 (6, 8) envelope_190), (placed21 7 (6, 7) envelope_230), (placed21 0 (1, 3) envelope_263), (placed21 4 (1, 8) envelope_306)]
theorem common_sub_673_i4 : commonEnvelope childrenD_673_i4 ⊆ insert (4, 5) required_673_i4 := by decide +kernel
theorem child_required_sub_673_i4 : ∀ j, childrenC_673_i4 j ⊆ insert (4, 5) required_673_i4 := by decide +kernel
theorem child_envelope_sub_673_i4 : ∀ j, childrenD_673_i4 j ⊆ envelope_673_i4 := by decide +kernel
theorem pivot_mem_673_i4 : (4, 5) ∈ envelope_673_i4 := by decide +kernel
theorem children_work_673_i4 : ∀ j, Template HasSnaky 6 (childrenC_673_i4 j) (childrenD_673_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_188 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_190 6 (6, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_230 7 (6, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_263 0 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_306 4 (1, 8)).mono (by decide +kernel)
theorem row_works_673_i4 : Template HasSnaky 7 required_673_i4 envelope_673_i4 := by
  refine compose HasSnaky 6 childrenC_673_i4 childrenD_673_i4 children_work_673_i4 (4, 5)
    required_673_i4 envelope_673_i4 pivot_mem_673_i4 child_required_sub_673_i4 child_envelope_sub_673_i4 ?_
  intro b hb
  exact common_sub_673_i4 (mem_commonEnvelope childrenD_673_i4 b hb)
def required_673_i6 : Finset Cell := ⟨(([(1, 6), (2, 3), (2, 4), (3, 4), (4, 4), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_673_i6 : Finset Cell := ⟨(([(0, 5), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (3, 3), (3, 4), (3, 7), (3, 8), (3, 9), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 5), (5, 7), (5, 8), (5, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_673_i6 : Fin 2 → Finset Cell := ![(placed21 2 (4, 3) required_38), (placed21 0 (1, 3) required_145)]
def childrenD_673_i6 : Fin 2 → Finset Cell := ![(placed21 2 (4, 3) envelope_38), (placed21 0 (1, 3) envelope_145)]
theorem common_sub_673_i6 : commonEnvelope childrenD_673_i6 ⊆ insert (1, 4) required_673_i6 := by decide +kernel
theorem child_required_sub_673_i6 : ∀ j, childrenC_673_i6 j ⊆ insert (1, 4) required_673_i6 := by decide +kernel
theorem child_envelope_sub_673_i6 : ∀ j, childrenD_673_i6 j ⊆ envelope_673_i6 := by decide +kernel
theorem pivot_mem_673_i6 : (1, 4) ∈ envelope_673_i6 := by decide +kernel
theorem children_work_673_i6 : ∀ j, Template HasSnaky 5 (childrenC_673_i6 j) (childrenD_673_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_38 2 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_145 0 (1, 3)).mono (by decide +kernel)
theorem row_works_673_i6 : Template HasSnaky 6 required_673_i6 envelope_673_i6 := by
  refine compose HasSnaky 5 childrenC_673_i6 childrenD_673_i6 children_work_673_i6 (1, 4)
    required_673_i6 envelope_673_i6 pivot_mem_673_i6 child_required_sub_673_i6 child_envelope_sub_673_i6 ?_
  intro b hb
  exact common_sub_673_i6 (mem_commonEnvelope childrenD_673_i6 b hb)
def required_673_i5 : Finset Cell := ⟨(([(1, 3), (1, 6), (2, 3), (2, 4), (4, 4), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_673_i5 : Finset Cell := ⟨(([(0, 5), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (3, 3), (3, 4), (3, 7), (3, 8), (3, 9), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 4), (5, 5), (5, 7), (5, 8), (5, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_673_i5 : Fin 2 → Finset Cell := ![(placed21 6 (5, 4) required_0), required_673_i6]
def childrenD_673_i5 : Fin 2 → Finset Cell := ![(placed21 6 (5, 4) envelope_0), envelope_673_i6]
theorem common_sub_673_i5 : commonEnvelope childrenD_673_i5 ⊆ insert (3, 4) required_673_i5 := by decide +kernel
theorem child_required_sub_673_i5 : ∀ j, childrenC_673_i5 j ⊆ insert (3, 4) required_673_i5 := by decide +kernel
theorem child_envelope_sub_673_i5 : ∀ j, childrenD_673_i5 j ⊆ envelope_673_i5 := by decide +kernel
theorem pivot_mem_673_i5 : (3, 4) ∈ envelope_673_i5 := by decide +kernel
theorem children_work_673_i5 : ∀ j, Template HasSnaky 6 (childrenC_673_i5 j) (childrenD_673_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (5, 4)).mono (by decide +kernel)
  · exact row_works_673_i6.mono (by decide +kernel)
theorem row_works_673_i5 : Template HasSnaky 7 required_673_i5 envelope_673_i5 := by
  refine compose HasSnaky 6 childrenC_673_i5 childrenD_673_i5 children_work_673_i5 (3, 4)
    required_673_i5 envelope_673_i5 pivot_mem_673_i5 child_required_sub_673_i5 child_envelope_sub_673_i5 ?_
  intro b hb
  exact common_sub_673_i5 (mem_commonEnvelope childrenD_673_i5 b hb)
def required_673_i9 : Finset Cell := ⟨(([(1, 4), (2, 4), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_673_i9 : Finset Cell := ⟨(([(1, 4), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (3, 7), (3, 8), (3, 9), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 1), (5, 2), (5, 3), (5, 7), (5, 8), (5, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_673_i9 : Fin 3 → Finset Cell := ![(placed21 3 (3, 6) required_8), (placed21 0 (3, 2) required_19), (placed21 7 (5, 6) required_25)]
def childrenD_673_i9 : Fin 3 → Finset Cell := ![(placed21 3 (3, 6) envelope_8), (placed21 0 (3, 2) envelope_19), (placed21 7 (5, 6) envelope_25)]
theorem common_sub_673_i9 : commonEnvelope childrenD_673_i9 ⊆ insert (4, 3) required_673_i9 := by decide +kernel
theorem child_required_sub_673_i9 : ∀ j, childrenC_673_i9 j ⊆ insert (4, 3) required_673_i9 := by decide +kernel
theorem child_envelope_sub_673_i9 : ∀ j, childrenD_673_i9 j ⊆ envelope_673_i9 := by decide +kernel
theorem pivot_mem_673_i9 : (4, 3) ∈ envelope_673_i9 := by decide +kernel
theorem children_work_673_i9 : ∀ j, Template HasSnaky 5 (childrenC_673_i9 j) (childrenD_673_i9 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 3 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_19 0 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_25 7 (5, 6)).mono (by decide +kernel)
theorem row_works_673_i9 : Template HasSnaky 6 required_673_i9 envelope_673_i9 := by
  refine compose HasSnaky 5 childrenC_673_i9 childrenD_673_i9 children_work_673_i9 (4, 3)
    required_673_i9 envelope_673_i9 pivot_mem_673_i9 child_required_sub_673_i9 child_envelope_sub_673_i9 ?_
  intro b hb
  exact common_sub_673_i9 (mem_commonEnvelope childrenD_673_i9 b hb)
def required_673_i10 : Finset Cell := ⟨(([(1, 4), (2, 4), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_673_i10 : Finset Cell := ⟨(([(1, 4), (2, 4), (3, 3), (3, 4), (3, 7), (3, 8), (3, 9), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 5), (5, 7), (5, 8), (5, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_673_i10 : Fin 2 → Finset Cell := ![(placed21 0 (1, 4) required_5), (placed21 0 (3, 3) required_10)]
def childrenD_673_i10 : Fin 2 → Finset Cell := ![(placed21 0 (1, 4) envelope_5), (placed21 0 (3, 3) envelope_10)]
theorem common_sub_673_i10 : commonEnvelope childrenD_673_i10 ⊆ insert (3, 4) required_673_i10 := by decide +kernel
theorem child_required_sub_673_i10 : ∀ j, childrenC_673_i10 j ⊆ insert (3, 4) required_673_i10 := by decide +kernel
theorem child_envelope_sub_673_i10 : ∀ j, childrenD_673_i10 j ⊆ envelope_673_i10 := by decide +kernel
theorem pivot_mem_673_i10 : (3, 4) ∈ envelope_673_i10 := by decide +kernel
theorem children_work_673_i10 : ∀ j, Template HasSnaky 4 (childrenC_673_i10 j) (childrenD_673_i10 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_10 0 (3, 3)).mono (by decide +kernel)
theorem row_works_673_i10 : Template HasSnaky 5 required_673_i10 envelope_673_i10 := by
  refine compose HasSnaky 4 childrenC_673_i10 childrenD_673_i10 children_work_673_i10 (3, 4)
    required_673_i10 envelope_673_i10 pivot_mem_673_i10 child_required_sub_673_i10 child_envelope_sub_673_i10 ?_
  intro b hb
  exact common_sub_673_i10 (mem_commonEnvelope childrenD_673_i10 b hb)
def required_673_i8 : Finset Cell := ⟨(([(1, 4), (2, 4), (4, 4), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_673_i8 : Finset Cell := ⟨(([(1, 4), (2, 3), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (3, 7), (3, 8), (3, 9), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_673_i8 : Fin 5 → Finset Cell := ![(placed21 4 (1, 7) required_263), (placed21 4 (1, 7) required_271), (placed21 4 (1, 7) required_424), required_673_i9, required_673_i10]
def childrenD_673_i8 : Fin 5 → Finset Cell := ![(placed21 4 (1, 7) envelope_263), (placed21 4 (1, 7) envelope_271), (placed21 4 (1, 7) envelope_424), envelope_673_i9, envelope_673_i10]
theorem common_sub_673_i8 : commonEnvelope childrenD_673_i8 ⊆ insert (4, 5) required_673_i8 := by decide +kernel
theorem child_required_sub_673_i8 : ∀ j, childrenC_673_i8 j ⊆ insert (4, 5) required_673_i8 := by decide +kernel
theorem child_envelope_sub_673_i8 : ∀ j, childrenD_673_i8 j ⊆ envelope_673_i8 := by decide +kernel
theorem pivot_mem_673_i8 : (4, 5) ∈ envelope_673_i8 := by decide +kernel
theorem children_work_673_i8 : ∀ j, Template HasSnaky 6 (childrenC_673_i8 j) (childrenD_673_i8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_263 4 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_271 4 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_424 4 (1, 7)).mono (by decide +kernel)
  · exact row_works_673_i9.mono (by decide +kernel)
  · exact row_works_673_i10.mono (by decide +kernel)
theorem row_works_673_i8 : Template HasSnaky 7 required_673_i8 envelope_673_i8 := by
  refine compose HasSnaky 6 childrenC_673_i8 childrenD_673_i8 children_work_673_i8 (4, 5)
    required_673_i8 envelope_673_i8 pivot_mem_673_i8 child_required_sub_673_i8 child_envelope_sub_673_i8 ?_
  intro b hb
  exact common_sub_673_i8 (mem_commonEnvelope childrenD_673_i8 b hb)
def required_673_i7 : Finset Cell := ⟨(([(1, 3), (1, 6), (2, 3), (2, 4), (2, 6), (4, 4), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_673_i7 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 7), (3, 8), (3, 9), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_673_i7 : Fin 2 → Finset Cell := ![(placed21 0 (1, 3) required_30), required_673_i8]
def childrenD_673_i7 : Fin 2 → Finset Cell := ![(placed21 0 (1, 3) envelope_30), envelope_673_i8]
theorem common_sub_673_i7 : commonEnvelope childrenD_673_i7 ⊆ insert (1, 4) required_673_i7 := by decide +kernel
theorem child_required_sub_673_i7 : ∀ j, childrenC_673_i7 j ⊆ insert (1, 4) required_673_i7 := by decide +kernel
theorem child_envelope_sub_673_i7 : ∀ j, childrenD_673_i7 j ⊆ envelope_673_i7 := by decide +kernel
theorem pivot_mem_673_i7 : (1, 4) ∈ envelope_673_i7 := by decide +kernel
theorem children_work_673_i7 : ∀ j, Template HasSnaky 7 (childrenC_673_i7 j) (childrenD_673_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_30 0 (1, 3)).mono (by decide +kernel)
  · exact row_works_673_i8.mono (by decide +kernel)
theorem row_works_673_i7 : Template HasSnaky 8 required_673_i7 envelope_673_i7 := by
  refine compose HasSnaky 7 childrenC_673_i7 childrenD_673_i7 children_work_673_i7 (1, 4)
    required_673_i7 envelope_673_i7 pivot_mem_673_i7 child_required_sub_673_i7 child_envelope_sub_673_i7 ?_
  intro b hb
  exact common_sub_673_i7 (mem_commonEnvelope childrenD_673_i7 b hb)
def required_673 : Finset Cell := ⟨(([(1, 3), (1, 6), (2, 3), (2, 4), (2, 6), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_673 : Finset Cell := ⟨(([(0, 5), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 4), (6, 6), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_673 : Fin 5 → Finset Cell := ![required_673_i0, required_673_i1, required_673_i4, required_673_i5, required_673_i7]
def childrenD_673 : Fin 5 → Finset Cell := ![envelope_673_i0, envelope_673_i1, envelope_673_i4, envelope_673_i5, envelope_673_i7]
theorem common_sub_673 : commonEnvelope childrenD_673 ⊆ insert (4, 4) required_673 := by decide +kernel
theorem child_required_sub_673 : ∀ j, childrenC_673 j ⊆ insert (4, 4) required_673 := by decide +kernel
theorem child_envelope_sub_673 : ∀ j, childrenD_673 j ⊆ envelope_673 := by decide +kernel
theorem pivot_mem_673 : (4, 4) ∈ envelope_673 := by decide +kernel
theorem children_work_673 : ∀ j, Template HasSnaky 8 (childrenC_673 j) (childrenD_673 j) := by
  intro j
  fin_cases j
  · exact row_works_673_i0.mono (by decide +kernel)
  · exact row_works_673_i1.mono (by decide +kernel)
  · exact row_works_673_i4.mono (by decide +kernel)
  · exact row_works_673_i5.mono (by decide +kernel)
  · exact row_works_673_i7.mono (by decide +kernel)
theorem row_works_673 : Template HasSnaky 9 required_673 envelope_673 := by
  refine compose HasSnaky 8 childrenC_673 childrenD_673 children_work_673 (4, 4)
    required_673 envelope_673 pivot_mem_673 child_required_sub_673 child_envelope_sub_673 ?_
  intro b hb
  exact common_sub_673 (mem_commonEnvelope childrenD_673 b hb)
def required_686_i0 : Finset Cell := ⟨(([(2, 3), (3, 3), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_686_i0 : Finset Cell := ⟨(([(1, 5), (2, 3), (2, 5), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 4), (5, 5), (5, 7), (5, 8), (5, 9), (6, 4), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_686_i0 : Fin 3 → Finset Cell := ![(placed21 1 (2, 3) required_43), (placed21 5 (7, 2) required_57), (placed21 0 (3, 0) required_340)]
def childrenD_686_i0 : Fin 3 → Finset Cell := ![(placed21 1 (2, 3) envelope_43), (placed21 5 (7, 2) envelope_57), (placed21 0 (3, 0) envelope_340)]
theorem common_sub_686_i0 : commonEnvelope childrenD_686_i0 ⊆ insert (5, 4) required_686_i0 := by decide +kernel
theorem child_required_sub_686_i0 : ∀ j, childrenC_686_i0 j ⊆ insert (5, 4) required_686_i0 := by decide +kernel
theorem child_envelope_sub_686_i0 : ∀ j, childrenD_686_i0 j ⊆ envelope_686_i0 := by decide +kernel
theorem pivot_mem_686_i0 : (5, 4) ∈ envelope_686_i0 := by decide +kernel
theorem children_work_686_i0 : ∀ j, Template HasSnaky 6 (childrenC_686_i0 j) (childrenD_686_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_43 1 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_57 5 (7, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_340 0 (3, 0)).mono (by decide +kernel)
theorem row_works_686_i0 : Template HasSnaky 7 required_686_i0 envelope_686_i0 := by
  refine compose HasSnaky 6 childrenC_686_i0 childrenD_686_i0 children_work_686_i0 (5, 4)
    required_686_i0 envelope_686_i0 pivot_mem_686_i0 child_required_sub_686_i0 child_envelope_sub_686_i0 ?_
  intro b hb
  exact common_sub_686_i0 (mem_commonEnvelope childrenD_686_i0 b hb)
def required_686_i1 : Finset Cell := ⟨(([(4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_686_i1 : Finset Cell := ⟨(([(0, 5), (0, 6), (1, 5), (1, 6), (2, 4), (2, 5), (2, 6), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 0), (5, 1), (5, 2), (5, 4), (5, 5), (5, 6), (6, 4), (6, 5), (7, 4), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_686_i1 : Fin 3 → Finset Cell := ![(placed21 4 (4, 6) required_7), (placed21 4 (3, 6) required_9), (placed21 5 (7, 2) required_256)]
def childrenD_686_i1 : Fin 3 → Finset Cell := ![(placed21 4 (4, 6) envelope_7), (placed21 4 (3, 6) envelope_9), (placed21 5 (7, 2) envelope_256)]
theorem common_sub_686_i1 : commonEnvelope childrenD_686_i1 ⊆ insert (4, 2) required_686_i1 := by decide +kernel
theorem child_required_sub_686_i1 : ∀ j, childrenC_686_i1 j ⊆ insert (4, 2) required_686_i1 := by decide +kernel
theorem child_envelope_sub_686_i1 : ∀ j, childrenD_686_i1 j ⊆ envelope_686_i1 := by decide +kernel
theorem pivot_mem_686_i1 : (4, 2) ∈ envelope_686_i1 := by decide +kernel
theorem children_work_686_i1 : ∀ j, Template HasSnaky 7 (childrenC_686_i1 j) (childrenD_686_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 4 (4, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 4 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_256 5 (7, 2)).mono (by decide +kernel)
theorem row_works_686_i1 : Template HasSnaky 8 required_686_i1 envelope_686_i1 := by
  refine compose HasSnaky 7 childrenC_686_i1 childrenD_686_i1 children_work_686_i1 (4, 2)
    required_686_i1 envelope_686_i1 pivot_mem_686_i1 child_required_sub_686_i1 child_envelope_sub_686_i1 ?_
  intro b hb
  exact common_sub_686_i1 (mem_commonEnvelope childrenD_686_i1 b hb)
def required_686 : Finset Cell := ⟨(([(2, 3), (3, 3), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_686 : Finset Cell := ⟨(([(0, 5), (0, 6), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 4), (6, 5), (6, 6), (7, 4), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_686 : Fin 7 → Finset Cell := ![(placed21 5 (6, 2) required_134), (placed21 5 (6, 2) required_180), (placed21 0 (3, 0) required_337), (placed21 5 (7, 2) required_435), (placed21 5 (6, 3) required_558), required_686_i0, required_686_i1]
def childrenD_686 : Fin 7 → Finset Cell := ![(placed21 5 (6, 2) envelope_134), (placed21 5 (6, 2) envelope_180), (placed21 0 (3, 0) envelope_337), (placed21 5 (7, 2) envelope_435), (placed21 5 (6, 3) envelope_558), envelope_686_i0, envelope_686_i1]
theorem common_sub_686 : commonEnvelope childrenD_686 ⊆ insert (4, 5) required_686 := by decide +kernel
theorem child_required_sub_686 : ∀ j, childrenC_686 j ⊆ insert (4, 5) required_686 := by decide +kernel
theorem child_envelope_sub_686 : ∀ j, childrenD_686 j ⊆ envelope_686 := by decide +kernel
theorem pivot_mem_686 : (4, 5) ∈ envelope_686 := by decide +kernel
theorem children_work_686 : ∀ j, Template HasSnaky 8 (childrenC_686 j) (childrenD_686 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_134 5 (6, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_180 5 (6, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_337 0 (3, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 5 (7, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_558 5 (6, 3)).mono (by decide +kernel)
  · exact row_works_686_i0.mono (by decide +kernel)
  · exact row_works_686_i1.mono (by decide +kernel)
theorem row_works_686 : Template HasSnaky 9 required_686 envelope_686 := by
  refine compose HasSnaky 8 childrenC_686 childrenD_686 children_work_686 (4, 5)
    required_686 envelope_686 pivot_mem_686 child_required_sub_686 child_envelope_sub_686 ?_
  intro b hb
  exact common_sub_686 (mem_commonEnvelope childrenD_686 b hb)
def required_688_i0 : Finset Cell := ⟨(([(0, 4), (1, 4), (1, 5), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_688_i0 : Finset Cell := ⟨(([(0, 4), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 3), (5, 4), (5, 5), (6, 3), (6, 4), (6, 5), (7, 3), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_688_i0 : Fin 5 → Finset Cell := ![(placed21 4 (0, 5) required_8), (placed21 3 (0, 5) required_41), (placed21 4 (0, 7) required_253), (placed21 4 (0, 7) required_256), (placed21 3 (0, 5) required_336)]
def childrenD_688_i0 : Fin 5 → Finset Cell := ![(placed21 4 (0, 5) envelope_8), (placed21 3 (0, 5) envelope_41), (placed21 4 (0, 7) envelope_253), (placed21 4 (0, 7) envelope_256), (placed21 3 (0, 5) envelope_336)]
theorem common_sub_688_i0 : commonEnvelope childrenD_688_i0 ⊆ insert (3, 4) required_688_i0 := by decide +kernel
theorem child_required_sub_688_i0 : ∀ j, childrenC_688_i0 j ⊆ insert (3, 4) required_688_i0 := by decide +kernel
theorem child_envelope_sub_688_i0 : ∀ j, childrenD_688_i0 j ⊆ envelope_688_i0 := by decide +kernel
theorem pivot_mem_688_i0 : (3, 4) ∈ envelope_688_i0 := by decide +kernel
theorem children_work_688_i0 : ∀ j, Template HasSnaky 7 (childrenC_688_i0 j) (childrenD_688_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 4 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_41 3 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_253 4 (0, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_256 4 (0, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_336 3 (0, 5)).mono (by decide +kernel)
theorem row_works_688_i0 : Template HasSnaky 8 required_688_i0 envelope_688_i0 := by
  refine compose HasSnaky 7 childrenC_688_i0 childrenD_688_i0 children_work_688_i0 (3, 4)
    required_688_i0 envelope_688_i0 pivot_mem_688_i0 child_required_sub_688_i0 child_envelope_sub_688_i0 ?_
  intro b hb
  exact common_sub_688_i0 (mem_commonEnvelope childrenD_688_i0 b hb)
def required_688 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (1, 4), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_688 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 3), (5, 4), (5, 5), (6, 3), (6, 4), (6, 5), (7, 3), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_688 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) required_0), required_688_i0]
def childrenD_688 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) envelope_0), envelope_688_i0]
theorem common_sub_688 : commonEnvelope childrenD_688 ⊆ insert (1, 5) required_688 := by decide +kernel
theorem child_required_sub_688 : ∀ j, childrenC_688 j ⊆ insert (1, 5) required_688 := by decide +kernel
theorem child_envelope_sub_688 : ∀ j, childrenD_688 j ⊆ envelope_688 := by decide +kernel
theorem pivot_mem_688 : (1, 5) ∈ envelope_688 := by decide +kernel
theorem children_work_688 : ∀ j, Template HasSnaky 8 (childrenC_688 j) (childrenD_688 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 1 (0, 1)).mono (by decide +kernel)
  · exact row_works_688_i0.mono (by decide +kernel)
theorem row_works_688 : Template HasSnaky 9 required_688 envelope_688 := by
  refine compose HasSnaky 8 childrenC_688 childrenD_688 children_work_688 (1, 5)
    required_688 envelope_688 pivot_mem_688 child_required_sub_688 child_envelope_sub_688 ?_
  intro b hb
  exact common_sub_688 (mem_commonEnvelope childrenD_688 b hb)
def height_673_i0 : ℕ := 4
def childrenH_673_i0 : Fin 2 → ℕ := ![height_30, height_74]
theorem height_exact_673_i0 : height_673_i0 = 1 + Finset.univ.sup childrenH_673_i0 := by decide +kernel
theorem required_origin_673_i0 : ∀ x ∈ required_673_i0,
    (∃ j, x ∈ childrenC_673_i0 j) ∨ ∀ j, x ∈ childrenD_673_i0 j := by decide +kernel
theorem required_exact_673_i0 : required_673_i0 =
    ((Finset.univ.biUnion childrenC_673_i0) ∪ commonEnvelope childrenD_673_i0).erase (1, 4) := by
  exact required_eq_combination childrenC_673_i0 childrenD_673_i0 (1, 4) required_673_i0
    (by decide +kernel) child_required_sub_673_i0 common_sub_673_i0 required_origin_673_i0
theorem envelope_origin_673_i0 : ∀ x ∈ envelope_673_i0,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_673_i0 j := by decide +kernel
theorem envelope_exact_673_i0 : envelope_673_i0 =
    insert (1, 4) (Finset.univ.biUnion childrenD_673_i0) := by
  exact envelope_eq_combination childrenD_673_i0 (1, 4) envelope_673_i0
    pivot_mem_673_i0 child_envelope_sub_673_i0 envelope_origin_673_i0
def checked_673_i0 : CheckedCard where
  required := required_673_i0
  envelope := envelope_673_i0
  height := height_673_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_673_i0
def height_673_i3 : ℕ := 6
def childrenH_673_i3 : Fin 2 → ℕ := ![height_5, height_260]
theorem height_exact_673_i3 : height_673_i3 = 1 + Finset.univ.sup childrenH_673_i3 := by decide +kernel
theorem required_origin_673_i3 : ∀ x ∈ required_673_i3,
    (∃ j, x ∈ childrenC_673_i3 j) ∨ ∀ j, x ∈ childrenD_673_i3 j := by decide +kernel
theorem required_exact_673_i3 : required_673_i3 =
    ((Finset.univ.biUnion childrenC_673_i3) ∪ commonEnvelope childrenD_673_i3).erase (4, 5) := by
  exact required_eq_combination childrenC_673_i3 childrenD_673_i3 (4, 5) required_673_i3
    (by decide +kernel) child_required_sub_673_i3 common_sub_673_i3 required_origin_673_i3
theorem envelope_origin_673_i3 : ∀ x ∈ envelope_673_i3,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_673_i3 j := by decide +kernel
theorem envelope_exact_673_i3 : envelope_673_i3 =
    insert (4, 5) (Finset.univ.biUnion childrenD_673_i3) := by
  exact envelope_eq_combination childrenD_673_i3 (4, 5) envelope_673_i3
    pivot_mem_673_i3 child_envelope_sub_673_i3 envelope_origin_673_i3
def checked_673_i3 : CheckedCard where
  required := required_673_i3
  envelope := envelope_673_i3
  height := height_673_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_673_i3
def height_673_i2 : ℕ := 7
def childrenH_673_i2 : Fin 2 → ℕ := ![height_38, height_673_i3]
theorem height_exact_673_i2 : height_673_i2 = 1 + Finset.univ.sup childrenH_673_i2 := by decide +kernel
theorem required_origin_673_i2 : ∀ x ∈ required_673_i2,
    (∃ j, x ∈ childrenC_673_i2 j) ∨ ∀ j, x ∈ childrenD_673_i2 j := by decide +kernel
theorem required_exact_673_i2 : required_673_i2 =
    ((Finset.univ.biUnion childrenC_673_i2) ∪ commonEnvelope childrenD_673_i2).erase (1, 4) := by
  exact required_eq_combination childrenC_673_i2 childrenD_673_i2 (1, 4) required_673_i2
    (by decide +kernel) child_required_sub_673_i2 common_sub_673_i2 required_origin_673_i2
theorem envelope_origin_673_i2 : ∀ x ∈ envelope_673_i2,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_673_i2 j := by decide +kernel
theorem envelope_exact_673_i2 : envelope_673_i2 =
    insert (1, 4) (Finset.univ.biUnion childrenD_673_i2) := by
  exact envelope_eq_combination childrenD_673_i2 (1, 4) envelope_673_i2
    pivot_mem_673_i2 child_envelope_sub_673_i2 envelope_origin_673_i2
def checked_673_i2 : CheckedCard where
  required := required_673_i2
  envelope := envelope_673_i2
  height := height_673_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_673_i2
def height_673_i1 : ℕ := 8
def childrenH_673_i1 : Fin 2 → ℕ := ![height_0, height_673_i2]
theorem height_exact_673_i1 : height_673_i1 = 1 + Finset.univ.sup childrenH_673_i1 := by decide +kernel
theorem required_origin_673_i1 : ∀ x ∈ required_673_i1,
    (∃ j, x ∈ childrenC_673_i1 j) ∨ ∀ j, x ∈ childrenD_673_i1 j := by decide +kernel
theorem required_exact_673_i1 : required_673_i1 =
    ((Finset.univ.biUnion childrenC_673_i1) ∪ commonEnvelope childrenD_673_i1).erase (3, 4) := by
  exact required_eq_combination childrenC_673_i1 childrenD_673_i1 (3, 4) required_673_i1
    (by decide +kernel) child_required_sub_673_i1 common_sub_673_i1 required_origin_673_i1
theorem envelope_origin_673_i1 : ∀ x ∈ envelope_673_i1,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_673_i1 j := by decide +kernel
theorem envelope_exact_673_i1 : envelope_673_i1 =
    insert (3, 4) (Finset.univ.biUnion childrenD_673_i1) := by
  exact envelope_eq_combination childrenD_673_i1 (3, 4) envelope_673_i1
    pivot_mem_673_i1 child_envelope_sub_673_i1 envelope_origin_673_i1
def checked_673_i1 : CheckedCard where
  required := required_673_i1
  envelope := envelope_673_i1
  height := height_673_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_673_i1
def height_673_i4 : ℕ := 7
def childrenH_673_i4 : Fin 5 → ℕ := ![height_188, height_190, height_230, height_263, height_306]
theorem height_exact_673_i4 : height_673_i4 = 1 + Finset.univ.sup childrenH_673_i4 := by decide +kernel
theorem required_origin_673_i4 : ∀ x ∈ required_673_i4,
    (∃ j, x ∈ childrenC_673_i4 j) ∨ ∀ j, x ∈ childrenD_673_i4 j := by decide +kernel
theorem required_exact_673_i4 : required_673_i4 =
    ((Finset.univ.biUnion childrenC_673_i4) ∪ commonEnvelope childrenD_673_i4).erase (4, 5) := by
  exact required_eq_combination childrenC_673_i4 childrenD_673_i4 (4, 5) required_673_i4
    (by decide +kernel) child_required_sub_673_i4 common_sub_673_i4 required_origin_673_i4
theorem envelope_origin_673_i4 : ∀ x ∈ envelope_673_i4,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_673_i4 j := by decide +kernel
theorem envelope_exact_673_i4 : envelope_673_i4 =
    insert (4, 5) (Finset.univ.biUnion childrenD_673_i4) := by
  exact envelope_eq_combination childrenD_673_i4 (4, 5) envelope_673_i4
    pivot_mem_673_i4 child_envelope_sub_673_i4 envelope_origin_673_i4
def checked_673_i4 : CheckedCard where
  required := required_673_i4
  envelope := envelope_673_i4
  height := height_673_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_673_i4
def height_673_i6 : ℕ := 6
def childrenH_673_i6 : Fin 2 → ℕ := ![height_38, height_145]
theorem height_exact_673_i6 : height_673_i6 = 1 + Finset.univ.sup childrenH_673_i6 := by decide +kernel
theorem required_origin_673_i6 : ∀ x ∈ required_673_i6,
    (∃ j, x ∈ childrenC_673_i6 j) ∨ ∀ j, x ∈ childrenD_673_i6 j := by decide +kernel
theorem required_exact_673_i6 : required_673_i6 =
    ((Finset.univ.biUnion childrenC_673_i6) ∪ commonEnvelope childrenD_673_i6).erase (1, 4) := by
  exact required_eq_combination childrenC_673_i6 childrenD_673_i6 (1, 4) required_673_i6
    (by decide +kernel) child_required_sub_673_i6 common_sub_673_i6 required_origin_673_i6
theorem envelope_origin_673_i6 : ∀ x ∈ envelope_673_i6,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_673_i6 j := by decide +kernel
theorem envelope_exact_673_i6 : envelope_673_i6 =
    insert (1, 4) (Finset.univ.biUnion childrenD_673_i6) := by
  exact envelope_eq_combination childrenD_673_i6 (1, 4) envelope_673_i6
    pivot_mem_673_i6 child_envelope_sub_673_i6 envelope_origin_673_i6
def checked_673_i6 : CheckedCard where
  required := required_673_i6
  envelope := envelope_673_i6
  height := height_673_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_673_i6
def height_673_i5 : ℕ := 7
def childrenH_673_i5 : Fin 2 → ℕ := ![height_0, height_673_i6]
theorem height_exact_673_i5 : height_673_i5 = 1 + Finset.univ.sup childrenH_673_i5 := by decide +kernel
theorem required_origin_673_i5 : ∀ x ∈ required_673_i5,
    (∃ j, x ∈ childrenC_673_i5 j) ∨ ∀ j, x ∈ childrenD_673_i5 j := by decide +kernel
theorem required_exact_673_i5 : required_673_i5 =
    ((Finset.univ.biUnion childrenC_673_i5) ∪ commonEnvelope childrenD_673_i5).erase (3, 4) := by
  exact required_eq_combination childrenC_673_i5 childrenD_673_i5 (3, 4) required_673_i5
    (by decide +kernel) child_required_sub_673_i5 common_sub_673_i5 required_origin_673_i5
theorem envelope_origin_673_i5 : ∀ x ∈ envelope_673_i5,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_673_i5 j := by decide +kernel
theorem envelope_exact_673_i5 : envelope_673_i5 =
    insert (3, 4) (Finset.univ.biUnion childrenD_673_i5) := by
  exact envelope_eq_combination childrenD_673_i5 (3, 4) envelope_673_i5
    pivot_mem_673_i5 child_envelope_sub_673_i5 envelope_origin_673_i5
def checked_673_i5 : CheckedCard where
  required := required_673_i5
  envelope := envelope_673_i5
  height := height_673_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_673_i5
def height_673_i9 : ℕ := 6
def childrenH_673_i9 : Fin 3 → ℕ := ![height_8, height_19, height_25]
theorem height_exact_673_i9 : height_673_i9 = 1 + Finset.univ.sup childrenH_673_i9 := by decide +kernel
theorem required_origin_673_i9 : ∀ x ∈ required_673_i9,
    (∃ j, x ∈ childrenC_673_i9 j) ∨ ∀ j, x ∈ childrenD_673_i9 j := by decide +kernel
theorem required_exact_673_i9 : required_673_i9 =
    ((Finset.univ.biUnion childrenC_673_i9) ∪ commonEnvelope childrenD_673_i9).erase (4, 3) := by
  exact required_eq_combination childrenC_673_i9 childrenD_673_i9 (4, 3) required_673_i9
    (by decide +kernel) child_required_sub_673_i9 common_sub_673_i9 required_origin_673_i9
theorem envelope_origin_673_i9 : ∀ x ∈ envelope_673_i9,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_673_i9 j := by decide +kernel
theorem envelope_exact_673_i9 : envelope_673_i9 =
    insert (4, 3) (Finset.univ.biUnion childrenD_673_i9) := by
  exact envelope_eq_combination childrenD_673_i9 (4, 3) envelope_673_i9
    pivot_mem_673_i9 child_envelope_sub_673_i9 envelope_origin_673_i9
def checked_673_i9 : CheckedCard where
  required := required_673_i9
  envelope := envelope_673_i9
  height := height_673_i9
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_673_i9
def height_673_i10 : ℕ := 5
def childrenH_673_i10 : Fin 2 → ℕ := ![height_5, height_10]
theorem height_exact_673_i10 : height_673_i10 = 1 + Finset.univ.sup childrenH_673_i10 := by decide +kernel
theorem required_origin_673_i10 : ∀ x ∈ required_673_i10,
    (∃ j, x ∈ childrenC_673_i10 j) ∨ ∀ j, x ∈ childrenD_673_i10 j := by decide +kernel
theorem required_exact_673_i10 : required_673_i10 =
    ((Finset.univ.biUnion childrenC_673_i10) ∪ commonEnvelope childrenD_673_i10).erase (3, 4) := by
  exact required_eq_combination childrenC_673_i10 childrenD_673_i10 (3, 4) required_673_i10
    (by decide +kernel) child_required_sub_673_i10 common_sub_673_i10 required_origin_673_i10
theorem envelope_origin_673_i10 : ∀ x ∈ envelope_673_i10,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_673_i10 j := by decide +kernel
theorem envelope_exact_673_i10 : envelope_673_i10 =
    insert (3, 4) (Finset.univ.biUnion childrenD_673_i10) := by
  exact envelope_eq_combination childrenD_673_i10 (3, 4) envelope_673_i10
    pivot_mem_673_i10 child_envelope_sub_673_i10 envelope_origin_673_i10
def checked_673_i10 : CheckedCard where
  required := required_673_i10
  envelope := envelope_673_i10
  height := height_673_i10
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_673_i10
def height_673_i8 : ℕ := 7
def childrenH_673_i8 : Fin 5 → ℕ := ![height_263, height_271, height_424, height_673_i9, height_673_i10]
theorem height_exact_673_i8 : height_673_i8 = 1 + Finset.univ.sup childrenH_673_i8 := by decide +kernel
theorem required_origin_673_i8 : ∀ x ∈ required_673_i8,
    (∃ j, x ∈ childrenC_673_i8 j) ∨ ∀ j, x ∈ childrenD_673_i8 j := by decide +kernel
theorem required_exact_673_i8 : required_673_i8 =
    ((Finset.univ.biUnion childrenC_673_i8) ∪ commonEnvelope childrenD_673_i8).erase (4, 5) := by
  exact required_eq_combination childrenC_673_i8 childrenD_673_i8 (4, 5) required_673_i8
    (by decide +kernel) child_required_sub_673_i8 common_sub_673_i8 required_origin_673_i8
theorem envelope_origin_673_i8 : ∀ x ∈ envelope_673_i8,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_673_i8 j := by decide +kernel
theorem envelope_exact_673_i8 : envelope_673_i8 =
    insert (4, 5) (Finset.univ.biUnion childrenD_673_i8) := by
  exact envelope_eq_combination childrenD_673_i8 (4, 5) envelope_673_i8
    pivot_mem_673_i8 child_envelope_sub_673_i8 envelope_origin_673_i8
def checked_673_i8 : CheckedCard where
  required := required_673_i8
  envelope := envelope_673_i8
  height := height_673_i8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_673_i8
def height_673_i7 : ℕ := 8
def childrenH_673_i7 : Fin 2 → ℕ := ![height_30, height_673_i8]
theorem height_exact_673_i7 : height_673_i7 = 1 + Finset.univ.sup childrenH_673_i7 := by decide +kernel
theorem required_origin_673_i7 : ∀ x ∈ required_673_i7,
    (∃ j, x ∈ childrenC_673_i7 j) ∨ ∀ j, x ∈ childrenD_673_i7 j := by decide +kernel
theorem required_exact_673_i7 : required_673_i7 =
    ((Finset.univ.biUnion childrenC_673_i7) ∪ commonEnvelope childrenD_673_i7).erase (1, 4) := by
  exact required_eq_combination childrenC_673_i7 childrenD_673_i7 (1, 4) required_673_i7
    (by decide +kernel) child_required_sub_673_i7 common_sub_673_i7 required_origin_673_i7
theorem envelope_origin_673_i7 : ∀ x ∈ envelope_673_i7,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_673_i7 j := by decide +kernel
theorem envelope_exact_673_i7 : envelope_673_i7 =
    insert (1, 4) (Finset.univ.biUnion childrenD_673_i7) := by
  exact envelope_eq_combination childrenD_673_i7 (1, 4) envelope_673_i7
    pivot_mem_673_i7 child_envelope_sub_673_i7 envelope_origin_673_i7
def checked_673_i7 : CheckedCard where
  required := required_673_i7
  envelope := envelope_673_i7
  height := height_673_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_673_i7
def height_673 : ℕ := 9
def childrenH_673 : Fin 5 → ℕ := ![height_673_i0, height_673_i1, height_673_i4, height_673_i5, height_673_i7]
theorem height_exact_673 : height_673 = 1 + Finset.univ.sup childrenH_673 := by decide +kernel
theorem required_origin_673 : ∀ x ∈ required_673,
    (∃ j, x ∈ childrenC_673 j) ∨ ∀ j, x ∈ childrenD_673 j := by decide +kernel
theorem required_exact_673 : required_673 =
    ((Finset.univ.biUnion childrenC_673) ∪ commonEnvelope childrenD_673).erase (4, 4) := by
  exact required_eq_combination childrenC_673 childrenD_673 (4, 4) required_673
    (by decide +kernel) child_required_sub_673 common_sub_673 required_origin_673
theorem envelope_origin_673 : ∀ x ∈ envelope_673,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_673 j := by decide +kernel
theorem envelope_exact_673 : envelope_673 =
    insert (4, 4) (Finset.univ.biUnion childrenD_673) := by
  exact envelope_eq_combination childrenD_673 (4, 4) envelope_673
    pivot_mem_673 child_envelope_sub_673 envelope_origin_673
def checked_673 : CheckedCard where
  required := required_673
  envelope := envelope_673
  height := height_673
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_673
def height_686_i0 : ℕ := 7
def childrenH_686_i0 : Fin 3 → ℕ := ![height_43, height_57, height_340]
theorem height_exact_686_i0 : height_686_i0 = 1 + Finset.univ.sup childrenH_686_i0 := by decide +kernel
theorem required_origin_686_i0 : ∀ x ∈ required_686_i0,
    (∃ j, x ∈ childrenC_686_i0 j) ∨ ∀ j, x ∈ childrenD_686_i0 j := by decide +kernel
theorem required_exact_686_i0 : required_686_i0 =
    ((Finset.univ.biUnion childrenC_686_i0) ∪ commonEnvelope childrenD_686_i0).erase (5, 4) := by
  exact required_eq_combination childrenC_686_i0 childrenD_686_i0 (5, 4) required_686_i0
    (by decide +kernel) child_required_sub_686_i0 common_sub_686_i0 required_origin_686_i0
theorem envelope_origin_686_i0 : ∀ x ∈ envelope_686_i0,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_686_i0 j := by decide +kernel
theorem envelope_exact_686_i0 : envelope_686_i0 =
    insert (5, 4) (Finset.univ.biUnion childrenD_686_i0) := by
  exact envelope_eq_combination childrenD_686_i0 (5, 4) envelope_686_i0
    pivot_mem_686_i0 child_envelope_sub_686_i0 envelope_origin_686_i0
def checked_686_i0 : CheckedCard where
  required := required_686_i0
  envelope := envelope_686_i0
  height := height_686_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_686_i0
def height_686_i1 : ℕ := 8
def childrenH_686_i1 : Fin 3 → ℕ := ![height_7, height_9, height_256]
theorem height_exact_686_i1 : height_686_i1 = 1 + Finset.univ.sup childrenH_686_i1 := by decide +kernel
theorem required_origin_686_i1 : ∀ x ∈ required_686_i1,
    (∃ j, x ∈ childrenC_686_i1 j) ∨ ∀ j, x ∈ childrenD_686_i1 j := by decide +kernel
theorem required_exact_686_i1 : required_686_i1 =
    ((Finset.univ.biUnion childrenC_686_i1) ∪ commonEnvelope childrenD_686_i1).erase (4, 2) := by
  exact required_eq_combination childrenC_686_i1 childrenD_686_i1 (4, 2) required_686_i1
    (by decide +kernel) child_required_sub_686_i1 common_sub_686_i1 required_origin_686_i1
theorem envelope_origin_686_i1 : ∀ x ∈ envelope_686_i1,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_686_i1 j := by decide +kernel
theorem envelope_exact_686_i1 : envelope_686_i1 =
    insert (4, 2) (Finset.univ.biUnion childrenD_686_i1) := by
  exact envelope_eq_combination childrenD_686_i1 (4, 2) envelope_686_i1
    pivot_mem_686_i1 child_envelope_sub_686_i1 envelope_origin_686_i1
def checked_686_i1 : CheckedCard where
  required := required_686_i1
  envelope := envelope_686_i1
  height := height_686_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_686_i1
def height_686 : ℕ := 9
def childrenH_686 : Fin 7 → ℕ := ![height_134, height_180, height_337, height_435, height_558, height_686_i0, height_686_i1]
theorem height_exact_686 : height_686 = 1 + Finset.univ.sup childrenH_686 := by decide +kernel
theorem required_origin_686 : ∀ x ∈ required_686,
    (∃ j, x ∈ childrenC_686 j) ∨ ∀ j, x ∈ childrenD_686 j := by decide +kernel
theorem required_exact_686 : required_686 =
    ((Finset.univ.biUnion childrenC_686) ∪ commonEnvelope childrenD_686).erase (4, 5) := by
  exact required_eq_combination childrenC_686 childrenD_686 (4, 5) required_686
    (by decide +kernel) child_required_sub_686 common_sub_686 required_origin_686
theorem envelope_origin_686 : ∀ x ∈ envelope_686,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_686 j := by decide +kernel
theorem envelope_exact_686 : envelope_686 =
    insert (4, 5) (Finset.univ.biUnion childrenD_686) := by
  exact envelope_eq_combination childrenD_686 (4, 5) envelope_686
    pivot_mem_686 child_envelope_sub_686 envelope_origin_686
def checked_686 : CheckedCard where
  required := required_686
  envelope := envelope_686
  height := height_686
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_686
def height_688_i0 : ℕ := 8
def childrenH_688_i0 : Fin 5 → ℕ := ![height_8, height_41, height_253, height_256, height_336]
theorem height_exact_688_i0 : height_688_i0 = 1 + Finset.univ.sup childrenH_688_i0 := by decide +kernel
theorem required_origin_688_i0 : ∀ x ∈ required_688_i0,
    (∃ j, x ∈ childrenC_688_i0 j) ∨ ∀ j, x ∈ childrenD_688_i0 j := by decide +kernel
theorem required_exact_688_i0 : required_688_i0 =
    ((Finset.univ.biUnion childrenC_688_i0) ∪ commonEnvelope childrenD_688_i0).erase (3, 4) := by
  exact required_eq_combination childrenC_688_i0 childrenD_688_i0 (3, 4) required_688_i0
    (by decide +kernel) child_required_sub_688_i0 common_sub_688_i0 required_origin_688_i0
theorem envelope_origin_688_i0 : ∀ x ∈ envelope_688_i0,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_688_i0 j := by decide +kernel
theorem envelope_exact_688_i0 : envelope_688_i0 =
    insert (3, 4) (Finset.univ.biUnion childrenD_688_i0) := by
  exact envelope_eq_combination childrenD_688_i0 (3, 4) envelope_688_i0
    pivot_mem_688_i0 child_envelope_sub_688_i0 envelope_origin_688_i0
def checked_688_i0 : CheckedCard where
  required := required_688_i0
  envelope := envelope_688_i0
  height := height_688_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_688_i0
def height_688 : ℕ := 9
def childrenH_688 : Fin 2 → ℕ := ![height_0, height_688_i0]
theorem height_exact_688 : height_688 = 1 + Finset.univ.sup childrenH_688 := by decide +kernel
theorem required_origin_688 : ∀ x ∈ required_688,
    (∃ j, x ∈ childrenC_688 j) ∨ ∀ j, x ∈ childrenD_688 j := by decide +kernel
theorem required_exact_688 : required_688 =
    ((Finset.univ.biUnion childrenC_688) ∪ commonEnvelope childrenD_688).erase (1, 5) := by
  exact required_eq_combination childrenC_688 childrenD_688 (1, 5) required_688
    (by decide +kernel) child_required_sub_688 common_sub_688 required_origin_688
theorem envelope_origin_688 : ∀ x ∈ envelope_688,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_688 j := by decide +kernel
theorem envelope_exact_688 : envelope_688 =
    insert (1, 5) (Finset.univ.biUnion childrenD_688) := by
  exact envelope_eq_combination childrenD_688 (1, 5) envelope_688
    pivot_mem_688 child_envelope_sub_688 envelope_origin_688
def checked_688 : CheckedCard where
  required := required_688
  envelope := envelope_688
  height := height_688
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_688
end SnakyPrototype.Certificate21

end OAI
