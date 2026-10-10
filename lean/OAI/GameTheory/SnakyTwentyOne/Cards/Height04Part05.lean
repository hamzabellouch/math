import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_381_i1 : Finset Cell := ⟨(([(1, 1), (2, 1), (3, 1), (3, 2), (3, 3), (4, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_381_i1 : Finset Cell := ⟨(([(1, 1), (2, 1), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (5, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_381_i1 : Fin 2 → Finset Cell := ![(placed21 3 (3, 4) required_0), (placed21 4 (1, 1) required_5)]
def childrenD_381_i1 : Fin 2 → Finset Cell := ![(placed21 3 (3, 4) envelope_0), (placed21 4 (1, 1) envelope_5)]
theorem common_sub_381_i1 : commonEnvelope childrenD_381_i1 ⊆ insert (4, 1) required_381_i1 := by decide +kernel
theorem child_required_sub_381_i1 : ∀ j, childrenC_381_i1 j ⊆ insert (4, 1) required_381_i1 := by decide +kernel
theorem child_envelope_sub_381_i1 : ∀ j, childrenD_381_i1 j ⊆ envelope_381_i1 := by decide +kernel
theorem pivot_mem_381_i1 : (4, 1) ∈ envelope_381_i1 := by decide +kernel
theorem children_work_381_i1 : ∀ j, Template HasSnaky 1 (childrenC_381_i1 j) (childrenD_381_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 3 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 4 (1, 1)).mono (by decide +kernel)
theorem row_works_381_i1 : Template HasSnaky 2 required_381_i1 envelope_381_i1 := by
  refine compose HasSnaky 1 childrenC_381_i1 childrenD_381_i1 children_work_381_i1 (4, 1)
    required_381_i1 envelope_381_i1 pivot_mem_381_i1 child_required_sub_381_i1 child_envelope_sub_381_i1 ?_
  intro b hb
  exact common_sub_381_i1 (mem_commonEnvelope childrenD_381_i1 b hb)
def required_381_i0 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_381_i0 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (5, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_381_i0 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) required_4), required_381_i1]
def childrenD_381_i0 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) envelope_4), envelope_381_i1]
theorem common_sub_381_i0 : commonEnvelope childrenD_381_i0 ⊆ insert (4, 0) required_381_i0 := by decide +kernel
theorem child_required_sub_381_i0 : ∀ j, childrenC_381_i0 j ⊆ insert (4, 0) required_381_i0 := by decide +kernel
theorem child_envelope_sub_381_i0 : ∀ j, childrenD_381_i0 j ⊆ envelope_381_i0 := by decide +kernel
theorem pivot_mem_381_i0 : (4, 0) ∈ envelope_381_i0 := by decide +kernel
theorem children_work_381_i0 : ∀ j, Template HasSnaky 2 (childrenC_381_i0 j) (childrenD_381_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 4 (0, 1)).mono (by decide +kernel)
  · exact row_works_381_i1.mono (by decide +kernel)
theorem row_works_381_i0 : Template HasSnaky 3 required_381_i0 envelope_381_i0 := by
  refine compose HasSnaky 2 childrenC_381_i0 childrenD_381_i0 children_work_381_i0 (4, 0)
    required_381_i0 envelope_381_i0 pivot_mem_381_i0 child_required_sub_381_i0 child_envelope_sub_381_i0 ?_
  intro b hb
  exact common_sub_381_i0 (mem_commonEnvelope childrenD_381_i0 b hb)
def required_381 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_381 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (5, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_381 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_5), required_381_i0]
def childrenD_381 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_5), envelope_381_i0]
theorem common_sub_381 : commonEnvelope childrenD_381 ⊆ insert (3, 1) required_381 := by decide +kernel
theorem child_required_sub_381 : ∀ j, childrenC_381 j ⊆ insert (3, 1) required_381 := by decide +kernel
theorem child_envelope_sub_381 : ∀ j, childrenD_381 j ⊆ envelope_381 := by decide +kernel
theorem pivot_mem_381 : (3, 1) ∈ envelope_381 := by decide +kernel
theorem children_work_381 : ∀ j, Template HasSnaky 3 (childrenC_381 j) (childrenD_381 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_381_i0.mono (by decide +kernel)
theorem row_works_381 : Template HasSnaky 4 required_381 envelope_381 := by
  refine compose HasSnaky 3 childrenC_381 childrenD_381 children_work_381 (3, 1)
    required_381 envelope_381 pivot_mem_381 child_required_sub_381 child_envelope_sub_381 ?_
  intro b hb
  exact common_sub_381 (mem_commonEnvelope childrenD_381 b hb)
def required_424_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_424_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_424_i0 : Fin 2 → Finset Cell := ![(placed21 4 (0, 3) required_2), (placed21 0 (3, 0) required_11)]
def childrenD_424_i0 : Fin 2 → Finset Cell := ![(placed21 4 (0, 3) envelope_2), (placed21 0 (3, 0) envelope_11)]
theorem common_sub_424_i0 : commonEnvelope childrenD_424_i0 ⊆ insert (4, 2) required_424_i0 := by decide +kernel
theorem child_required_sub_424_i0 : ∀ j, childrenC_424_i0 j ⊆ insert (4, 2) required_424_i0 := by decide +kernel
theorem child_envelope_sub_424_i0 : ∀ j, childrenD_424_i0 j ⊆ envelope_424_i0 := by decide +kernel
theorem pivot_mem_424_i0 : (4, 2) ∈ envelope_424_i0 := by decide +kernel
theorem children_work_424_i0 : ∀ j, Template HasSnaky 2 (childrenC_424_i0 j) (childrenD_424_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 4 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_11 0 (3, 0)).mono (by decide +kernel)
theorem row_works_424_i0 : Template HasSnaky 3 required_424_i0 envelope_424_i0 := by
  refine compose HasSnaky 2 childrenC_424_i0 childrenD_424_i0 children_work_424_i0 (4, 2)
    required_424_i0 envelope_424_i0 pivot_mem_424_i0 child_required_sub_424_i0 child_envelope_sub_424_i0 ?_
  intro b hb
  exact common_sub_424_i0 (mem_commonEnvelope childrenD_424_i0 b hb)
def required_424 : Finset Cell := ⟨(([(0, 3), (1, 3), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_424 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_424 : Fin 3 → Finset Cell := ![(placed21 0 (3, 0) required_7), (placed21 5 (4, 1) required_25), required_424_i0]
def childrenD_424 : Fin 3 → Finset Cell := ![(placed21 0 (3, 0) envelope_7), (placed21 5 (4, 1) envelope_25), envelope_424_i0]
theorem common_sub_424 : commonEnvelope childrenD_424 ⊆ insert (3, 4) required_424 := by decide +kernel
theorem child_required_sub_424 : ∀ j, childrenC_424 j ⊆ insert (3, 4) required_424 := by decide +kernel
theorem child_envelope_sub_424 : ∀ j, childrenD_424 j ⊆ envelope_424 := by decide +kernel
theorem pivot_mem_424 : (3, 4) ∈ envelope_424 := by decide +kernel
theorem children_work_424 : ∀ j, Template HasSnaky 3 (childrenC_424 j) (childrenD_424 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 0 (3, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_25 5 (4, 1)).mono (by decide +kernel)
  · exact row_works_424_i0.mono (by decide +kernel)
theorem row_works_424 : Template HasSnaky 4 required_424 envelope_424 := by
  refine compose HasSnaky 3 childrenC_424 childrenD_424 children_work_424 (3, 4)
    required_424 envelope_424 pivot_mem_424 child_required_sub_424 child_envelope_sub_424 ?_
  intro b hb
  exact common_sub_424 (mem_commonEnvelope childrenD_424 b hb)
def required_432_i0 : Finset Cell := ⟨(([(1, 1), (2, 1), (3, 1), (3, 3), (4, 0), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_432_i0 : Finset Cell := ⟨(([(1, 1), (2, 1), (3, 1), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_432_i0 : Fin 2 → Finset Cell := ![(placed21 4 (1, 1) required_5), (placed21 5 (5, 0) required_146)]
def childrenD_432_i0 : Fin 2 → Finset Cell := ![(placed21 4 (1, 1) envelope_5), (placed21 5 (5, 0) envelope_146)]
theorem common_sub_432_i0 : commonEnvelope childrenD_432_i0 ⊆ insert (4, 1) required_432_i0 := by decide +kernel
theorem child_required_sub_432_i0 : ∀ j, childrenC_432_i0 j ⊆ insert (4, 1) required_432_i0 := by decide +kernel
theorem child_envelope_sub_432_i0 : ∀ j, childrenD_432_i0 j ⊆ envelope_432_i0 := by decide +kernel
theorem pivot_mem_432_i0 : (4, 1) ∈ envelope_432_i0 := by decide +kernel
theorem children_work_432_i0 : ∀ j, Template HasSnaky 2 (childrenC_432_i0 j) (childrenD_432_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_146 5 (5, 0)).mono (by decide +kernel)
theorem row_works_432_i0 : Template HasSnaky 3 required_432_i0 envelope_432_i0 := by
  refine compose HasSnaky 2 childrenC_432_i0 childrenD_432_i0 children_work_432_i0 (4, 1)
    required_432_i0 envelope_432_i0 pivot_mem_432_i0 child_required_sub_432_i0 child_envelope_sub_432_i0 ?_
  intro b hb
  exact common_sub_432_i0 (mem_commonEnvelope childrenD_432_i0 b hb)
def required_432 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_432 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 0), (3, 1), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_432 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) required_4), required_432_i0]
def childrenD_432 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) envelope_4), envelope_432_i0]
theorem common_sub_432 : commonEnvelope childrenD_432 ⊆ insert (4, 0) required_432 := by decide +kernel
theorem child_required_sub_432 : ∀ j, childrenC_432 j ⊆ insert (4, 0) required_432 := by decide +kernel
theorem child_envelope_sub_432 : ∀ j, childrenD_432 j ⊆ envelope_432 := by decide +kernel
theorem pivot_mem_432 : (4, 0) ∈ envelope_432 := by decide +kernel
theorem children_work_432 : ∀ j, Template HasSnaky 3 (childrenC_432 j) (childrenD_432 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 4 (0, 1)).mono (by decide +kernel)
  · exact row_works_432_i0.mono (by decide +kernel)
theorem row_works_432 : Template HasSnaky 4 required_432 envelope_432 := by
  refine compose HasSnaky 3 childrenC_432 childrenD_432 children_work_432 (4, 0)
    required_432 envelope_432 pivot_mem_432 child_required_sub_432 child_envelope_sub_432 ?_
  intro b hb
  exact common_sub_432 (mem_commonEnvelope childrenD_432 b hb)
def required_496_i0 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (1, 1), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_496_i0 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (2, 1), (3, 1), (3, 2), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_496_i0 : Fin 2 → Finset Cell := ![(placed21 3 (0, 5) required_0), (placed21 1 (0, 1) required_30)]
def childrenD_496_i0 : Fin 2 → Finset Cell := ![(placed21 3 (0, 5) envelope_0), (placed21 1 (0, 1) envelope_30)]
theorem common_sub_496_i0 : commonEnvelope childrenD_496_i0 ⊆ insert (1, 2) required_496_i0 := by decide +kernel
theorem child_required_sub_496_i0 : ∀ j, childrenC_496_i0 j ⊆ insert (1, 2) required_496_i0 := by decide +kernel
theorem child_envelope_sub_496_i0 : ∀ j, childrenD_496_i0 j ⊆ envelope_496_i0 := by decide +kernel
theorem pivot_mem_496_i0 : (1, 2) ∈ envelope_496_i0 := by decide +kernel
theorem children_work_496_i0 : ∀ j, Template HasSnaky 2 (childrenC_496_i0 j) (childrenD_496_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 3 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_30 1 (0, 1)).mono (by decide +kernel)
theorem row_works_496_i0 : Template HasSnaky 3 required_496_i0 envelope_496_i0 := by
  refine compose HasSnaky 2 childrenC_496_i0 childrenD_496_i0 children_work_496_i0 (1, 2)
    required_496_i0 envelope_496_i0 pivot_mem_496_i0 child_required_sub_496_i0 child_envelope_sub_496_i0 ?_
  intro b hb
  exact common_sub_496_i0 (mem_commonEnvelope childrenD_496_i0 b hb)
def required_496 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_496 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (2, 1), (3, 1), (3, 2), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_496 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) required_5), required_496_i0]
def childrenD_496 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) envelope_5), envelope_496_i0]
theorem common_sub_496 : commonEnvelope childrenD_496 ⊆ insert (1, 1) required_496 := by decide +kernel
theorem child_required_sub_496 : ∀ j, childrenC_496 j ⊆ insert (1, 1) required_496 := by decide +kernel
theorem child_envelope_sub_496 : ∀ j, childrenD_496 j ⊆ envelope_496 := by decide +kernel
theorem pivot_mem_496 : (1, 1) ∈ envelope_496 := by decide +kernel
theorem children_work_496 : ∀ j, Template HasSnaky 3 (childrenC_496 j) (childrenD_496 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (0, 4)).mono (by decide +kernel)
  · exact row_works_496_i0.mono (by decide +kernel)
theorem row_works_496 : Template HasSnaky 4 required_496 envelope_496 := by
  refine compose HasSnaky 3 childrenC_496 childrenD_496 children_work_496 (1, 1)
    required_496 envelope_496 pivot_mem_496 child_required_sub_496 child_envelope_sub_496 ?_
  intro b hb
  exact common_sub_496 (mem_commonEnvelope childrenD_496 b hb)
def required_500_i0 : Finset Cell := ⟨(([(0, 1), (0, 4), (1, 2), (1, 3), (1, 4), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_500_i0 : Finset Cell := ⟨(([(0, 1), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (3, 1), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_500_i0 : Fin 2 → Finset Cell := ![(placed21 5 (1, 1) required_5), required_146]
def childrenD_500_i0 : Fin 2 → Finset Cell := ![(placed21 5 (1, 1) envelope_5), envelope_146]
theorem common_sub_500_i0 : commonEnvelope childrenD_500_i0 ⊆ insert (1, 1) required_500_i0 := by decide +kernel
theorem child_required_sub_500_i0 : ∀ j, childrenC_500_i0 j ⊆ insert (1, 1) required_500_i0 := by decide +kernel
theorem child_envelope_sub_500_i0 : ∀ j, childrenD_500_i0 j ⊆ envelope_500_i0 := by decide +kernel
theorem pivot_mem_500_i0 : (1, 1) ∈ envelope_500_i0 := by decide +kernel
theorem children_work_500_i0 : ∀ j, Template HasSnaky 2 (childrenC_500_i0 j) (childrenD_500_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (1, 1)).mono (by decide +kernel)
  · exact row_works_146.mono (by decide +kernel)
theorem row_works_500_i0 : Template HasSnaky 3 required_500_i0 envelope_500_i0 := by
  refine compose HasSnaky 2 childrenC_500_i0 childrenD_500_i0 children_work_500_i0 (1, 1)
    required_500_i0 envelope_500_i0 pivot_mem_500_i0 child_required_sub_500_i0 child_envelope_sub_500_i0 ?_
  intro b hb
  exact common_sub_500_i0 (mem_commonEnvelope childrenD_500_i0 b hb)
def required_500 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (1, 3), (1, 4), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_500 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (3, 1), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_500 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) required_0), required_500_i0]
def childrenD_500 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) envelope_0), envelope_500_i0]
theorem common_sub_500 : commonEnvelope childrenD_500 ⊆ insert (1, 2) required_500 := by decide +kernel
theorem child_required_sub_500 : ∀ j, childrenC_500 j ⊆ insert (1, 2) required_500 := by decide +kernel
theorem child_envelope_sub_500 : ∀ j, childrenD_500 j ⊆ envelope_500 := by decide +kernel
theorem pivot_mem_500 : (1, 2) ∈ envelope_500 := by decide +kernel
theorem children_work_500 : ∀ j, Template HasSnaky 3 (childrenC_500 j) (childrenD_500 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (1, 5)).mono (by decide +kernel)
  · exact row_works_500_i0.mono (by decide +kernel)
theorem row_works_500 : Template HasSnaky 4 required_500 envelope_500 := by
  refine compose HasSnaky 3 childrenC_500 childrenD_500 children_work_500 (1, 2)
    required_500 envelope_500 pivot_mem_500 child_required_sub_500 child_envelope_sub_500 ?_
  intro b hb
  exact common_sub_500 (mem_commonEnvelope childrenD_500 b hb)
def height_381_i1 : ℕ := 2
def childrenH_381_i1 : Fin 2 → ℕ := ![height_0, height_5]
theorem height_exact_381_i1 : height_381_i1 = 1 + Finset.univ.sup childrenH_381_i1 := by decide +kernel
theorem required_origin_381_i1 : ∀ x ∈ required_381_i1,
    (∃ j, x ∈ childrenC_381_i1 j) ∨ ∀ j, x ∈ childrenD_381_i1 j := by decide +kernel
theorem required_exact_381_i1 : required_381_i1 =
    ((Finset.univ.biUnion childrenC_381_i1) ∪ commonEnvelope childrenD_381_i1).erase (4, 1) := by
  exact required_eq_combination childrenC_381_i1 childrenD_381_i1 (4, 1) required_381_i1
    (by decide +kernel) child_required_sub_381_i1 common_sub_381_i1 required_origin_381_i1
theorem envelope_origin_381_i1 : ∀ x ∈ envelope_381_i1,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_381_i1 j := by decide +kernel
theorem envelope_exact_381_i1 : envelope_381_i1 =
    insert (4, 1) (Finset.univ.biUnion childrenD_381_i1) := by
  exact envelope_eq_combination childrenD_381_i1 (4, 1) envelope_381_i1
    pivot_mem_381_i1 child_envelope_sub_381_i1 envelope_origin_381_i1
def checked_381_i1 : CheckedCard where
  required := required_381_i1
  envelope := envelope_381_i1
  height := height_381_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_381_i1
def height_381_i0 : ℕ := 3
def childrenH_381_i0 : Fin 2 → ℕ := ![height_4, height_381_i1]
theorem height_exact_381_i0 : height_381_i0 = 1 + Finset.univ.sup childrenH_381_i0 := by decide +kernel
theorem required_origin_381_i0 : ∀ x ∈ required_381_i0,
    (∃ j, x ∈ childrenC_381_i0 j) ∨ ∀ j, x ∈ childrenD_381_i0 j := by decide +kernel
theorem required_exact_381_i0 : required_381_i0 =
    ((Finset.univ.biUnion childrenC_381_i0) ∪ commonEnvelope childrenD_381_i0).erase (4, 0) := by
  exact required_eq_combination childrenC_381_i0 childrenD_381_i0 (4, 0) required_381_i0
    (by decide +kernel) child_required_sub_381_i0 common_sub_381_i0 required_origin_381_i0
theorem envelope_origin_381_i0 : ∀ x ∈ envelope_381_i0,
    x = (4, 0) ∨ ∃ j, x ∈ childrenD_381_i0 j := by decide +kernel
theorem envelope_exact_381_i0 : envelope_381_i0 =
    insert (4, 0) (Finset.univ.biUnion childrenD_381_i0) := by
  exact envelope_eq_combination childrenD_381_i0 (4, 0) envelope_381_i0
    pivot_mem_381_i0 child_envelope_sub_381_i0 envelope_origin_381_i0
def checked_381_i0 : CheckedCard where
  required := required_381_i0
  envelope := envelope_381_i0
  height := height_381_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_381_i0
def height_381 : ℕ := 4
def childrenH_381 : Fin 2 → ℕ := ![height_5, height_381_i0]
theorem height_exact_381 : height_381 = 1 + Finset.univ.sup childrenH_381 := by decide +kernel
theorem required_origin_381 : ∀ x ∈ required_381,
    (∃ j, x ∈ childrenC_381 j) ∨ ∀ j, x ∈ childrenD_381 j := by decide +kernel
theorem required_exact_381 : required_381 =
    ((Finset.univ.biUnion childrenC_381) ∪ commonEnvelope childrenD_381).erase (3, 1) := by
  exact required_eq_combination childrenC_381 childrenD_381 (3, 1) required_381
    (by decide +kernel) child_required_sub_381 common_sub_381 required_origin_381
theorem envelope_origin_381 : ∀ x ∈ envelope_381,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_381 j := by decide +kernel
theorem envelope_exact_381 : envelope_381 =
    insert (3, 1) (Finset.univ.biUnion childrenD_381) := by
  exact envelope_eq_combination childrenD_381 (3, 1) envelope_381
    pivot_mem_381 child_envelope_sub_381 envelope_origin_381
def checked_381 : CheckedCard where
  required := required_381
  envelope := envelope_381
  height := height_381
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_381
def height_424_i0 : ℕ := 3
def childrenH_424_i0 : Fin 2 → ℕ := ![height_2, height_11]
theorem height_exact_424_i0 : height_424_i0 = 1 + Finset.univ.sup childrenH_424_i0 := by decide +kernel
theorem required_origin_424_i0 : ∀ x ∈ required_424_i0,
    (∃ j, x ∈ childrenC_424_i0 j) ∨ ∀ j, x ∈ childrenD_424_i0 j := by decide +kernel
theorem required_exact_424_i0 : required_424_i0 =
    ((Finset.univ.biUnion childrenC_424_i0) ∪ commonEnvelope childrenD_424_i0).erase (4, 2) := by
  exact required_eq_combination childrenC_424_i0 childrenD_424_i0 (4, 2) required_424_i0
    (by decide +kernel) child_required_sub_424_i0 common_sub_424_i0 required_origin_424_i0
theorem envelope_origin_424_i0 : ∀ x ∈ envelope_424_i0,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_424_i0 j := by decide +kernel
theorem envelope_exact_424_i0 : envelope_424_i0 =
    insert (4, 2) (Finset.univ.biUnion childrenD_424_i0) := by
  exact envelope_eq_combination childrenD_424_i0 (4, 2) envelope_424_i0
    pivot_mem_424_i0 child_envelope_sub_424_i0 envelope_origin_424_i0
def checked_424_i0 : CheckedCard where
  required := required_424_i0
  envelope := envelope_424_i0
  height := height_424_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_424_i0
def height_424 : ℕ := 4
def childrenH_424 : Fin 3 → ℕ := ![height_7, height_25, height_424_i0]
theorem height_exact_424 : height_424 = 1 + Finset.univ.sup childrenH_424 := by decide +kernel
theorem required_origin_424 : ∀ x ∈ required_424,
    (∃ j, x ∈ childrenC_424 j) ∨ ∀ j, x ∈ childrenD_424 j := by decide +kernel
theorem required_exact_424 : required_424 =
    ((Finset.univ.biUnion childrenC_424) ∪ commonEnvelope childrenD_424).erase (3, 4) := by
  exact required_eq_combination childrenC_424 childrenD_424 (3, 4) required_424
    (by decide +kernel) child_required_sub_424 common_sub_424 required_origin_424
theorem envelope_origin_424 : ∀ x ∈ envelope_424,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_424 j := by decide +kernel
theorem envelope_exact_424 : envelope_424 =
    insert (3, 4) (Finset.univ.biUnion childrenD_424) := by
  exact envelope_eq_combination childrenD_424 (3, 4) envelope_424
    pivot_mem_424 child_envelope_sub_424 envelope_origin_424
def checked_424 : CheckedCard where
  required := required_424
  envelope := envelope_424
  height := height_424
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_424
def height_432_i0 : ℕ := 3
def childrenH_432_i0 : Fin 2 → ℕ := ![height_5, height_146]
theorem height_exact_432_i0 : height_432_i0 = 1 + Finset.univ.sup childrenH_432_i0 := by decide +kernel
theorem required_origin_432_i0 : ∀ x ∈ required_432_i0,
    (∃ j, x ∈ childrenC_432_i0 j) ∨ ∀ j, x ∈ childrenD_432_i0 j := by decide +kernel
theorem required_exact_432_i0 : required_432_i0 =
    ((Finset.univ.biUnion childrenC_432_i0) ∪ commonEnvelope childrenD_432_i0).erase (4, 1) := by
  exact required_eq_combination childrenC_432_i0 childrenD_432_i0 (4, 1) required_432_i0
    (by decide +kernel) child_required_sub_432_i0 common_sub_432_i0 required_origin_432_i0
theorem envelope_origin_432_i0 : ∀ x ∈ envelope_432_i0,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_432_i0 j := by decide +kernel
theorem envelope_exact_432_i0 : envelope_432_i0 =
    insert (4, 1) (Finset.univ.biUnion childrenD_432_i0) := by
  exact envelope_eq_combination childrenD_432_i0 (4, 1) envelope_432_i0
    pivot_mem_432_i0 child_envelope_sub_432_i0 envelope_origin_432_i0
def checked_432_i0 : CheckedCard where
  required := required_432_i0
  envelope := envelope_432_i0
  height := height_432_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_432_i0
def height_432 : ℕ := 4
def childrenH_432 : Fin 2 → ℕ := ![height_4, height_432_i0]
theorem height_exact_432 : height_432 = 1 + Finset.univ.sup childrenH_432 := by decide +kernel
theorem required_origin_432 : ∀ x ∈ required_432,
    (∃ j, x ∈ childrenC_432 j) ∨ ∀ j, x ∈ childrenD_432 j := by decide +kernel
theorem required_exact_432 : required_432 =
    ((Finset.univ.biUnion childrenC_432) ∪ commonEnvelope childrenD_432).erase (4, 0) := by
  exact required_eq_combination childrenC_432 childrenD_432 (4, 0) required_432
    (by decide +kernel) child_required_sub_432 common_sub_432 required_origin_432
theorem envelope_origin_432 : ∀ x ∈ envelope_432,
    x = (4, 0) ∨ ∃ j, x ∈ childrenD_432 j := by decide +kernel
theorem envelope_exact_432 : envelope_432 =
    insert (4, 0) (Finset.univ.biUnion childrenD_432) := by
  exact envelope_eq_combination childrenD_432 (4, 0) envelope_432
    pivot_mem_432 child_envelope_sub_432 envelope_origin_432
def checked_432 : CheckedCard where
  required := required_432
  envelope := envelope_432
  height := height_432
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_432
def height_496_i0 : ℕ := 3
def childrenH_496_i0 : Fin 2 → ℕ := ![height_0, height_30]
theorem height_exact_496_i0 : height_496_i0 = 1 + Finset.univ.sup childrenH_496_i0 := by decide +kernel
theorem required_origin_496_i0 : ∀ x ∈ required_496_i0,
    (∃ j, x ∈ childrenC_496_i0 j) ∨ ∀ j, x ∈ childrenD_496_i0 j := by decide +kernel
theorem required_exact_496_i0 : required_496_i0 =
    ((Finset.univ.biUnion childrenC_496_i0) ∪ commonEnvelope childrenD_496_i0).erase (1, 2) := by
  exact required_eq_combination childrenC_496_i0 childrenD_496_i0 (1, 2) required_496_i0
    (by decide +kernel) child_required_sub_496_i0 common_sub_496_i0 required_origin_496_i0
theorem envelope_origin_496_i0 : ∀ x ∈ envelope_496_i0,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_496_i0 j := by decide +kernel
theorem envelope_exact_496_i0 : envelope_496_i0 =
    insert (1, 2) (Finset.univ.biUnion childrenD_496_i0) := by
  exact envelope_eq_combination childrenD_496_i0 (1, 2) envelope_496_i0
    pivot_mem_496_i0 child_envelope_sub_496_i0 envelope_origin_496_i0
def checked_496_i0 : CheckedCard where
  required := required_496_i0
  envelope := envelope_496_i0
  height := height_496_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_496_i0
def height_496 : ℕ := 4
def childrenH_496 : Fin 2 → ℕ := ![height_5, height_496_i0]
theorem height_exact_496 : height_496 = 1 + Finset.univ.sup childrenH_496 := by decide +kernel
theorem required_origin_496 : ∀ x ∈ required_496,
    (∃ j, x ∈ childrenC_496 j) ∨ ∀ j, x ∈ childrenD_496 j := by decide +kernel
theorem required_exact_496 : required_496 =
    ((Finset.univ.biUnion childrenC_496) ∪ commonEnvelope childrenD_496).erase (1, 1) := by
  exact required_eq_combination childrenC_496 childrenD_496 (1, 1) required_496
    (by decide +kernel) child_required_sub_496 common_sub_496 required_origin_496
theorem envelope_origin_496 : ∀ x ∈ envelope_496,
    x = (1, 1) ∨ ∃ j, x ∈ childrenD_496 j := by decide +kernel
theorem envelope_exact_496 : envelope_496 =
    insert (1, 1) (Finset.univ.biUnion childrenD_496) := by
  exact envelope_eq_combination childrenD_496 (1, 1) envelope_496
    pivot_mem_496 child_envelope_sub_496 envelope_origin_496
def checked_496 : CheckedCard where
  required := required_496
  envelope := envelope_496
  height := height_496
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_496
def height_500_i0 : ℕ := 3
def childrenH_500_i0 : Fin 2 → ℕ := ![height_5, height_146]
theorem height_exact_500_i0 : height_500_i0 = 1 + Finset.univ.sup childrenH_500_i0 := by decide +kernel
theorem required_origin_500_i0 : ∀ x ∈ required_500_i0,
    (∃ j, x ∈ childrenC_500_i0 j) ∨ ∀ j, x ∈ childrenD_500_i0 j := by decide +kernel
theorem required_exact_500_i0 : required_500_i0 =
    ((Finset.univ.biUnion childrenC_500_i0) ∪ commonEnvelope childrenD_500_i0).erase (1, 1) := by
  exact required_eq_combination childrenC_500_i0 childrenD_500_i0 (1, 1) required_500_i0
    (by decide +kernel) child_required_sub_500_i0 common_sub_500_i0 required_origin_500_i0
theorem envelope_origin_500_i0 : ∀ x ∈ envelope_500_i0,
    x = (1, 1) ∨ ∃ j, x ∈ childrenD_500_i0 j := by decide +kernel
theorem envelope_exact_500_i0 : envelope_500_i0 =
    insert (1, 1) (Finset.univ.biUnion childrenD_500_i0) := by
  exact envelope_eq_combination childrenD_500_i0 (1, 1) envelope_500_i0
    pivot_mem_500_i0 child_envelope_sub_500_i0 envelope_origin_500_i0
def checked_500_i0 : CheckedCard where
  required := required_500_i0
  envelope := envelope_500_i0
  height := height_500_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_500_i0
def height_500 : ℕ := 4
def childrenH_500 : Fin 2 → ℕ := ![height_0, height_500_i0]
theorem height_exact_500 : height_500 = 1 + Finset.univ.sup childrenH_500 := by decide +kernel
theorem required_origin_500 : ∀ x ∈ required_500,
    (∃ j, x ∈ childrenC_500 j) ∨ ∀ j, x ∈ childrenD_500 j := by decide +kernel
theorem required_exact_500 : required_500 =
    ((Finset.univ.biUnion childrenC_500) ∪ commonEnvelope childrenD_500).erase (1, 2) := by
  exact required_eq_combination childrenC_500 childrenD_500 (1, 2) required_500
    (by decide +kernel) child_required_sub_500 common_sub_500 required_origin_500
theorem envelope_origin_500 : ∀ x ∈ envelope_500,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_500 j := by decide +kernel
theorem envelope_exact_500 : envelope_500 =
    insert (1, 2) (Finset.univ.biUnion childrenD_500) := by
  exact envelope_eq_combination childrenD_500 (1, 2) envelope_500
    pivot_mem_500 child_envelope_sub_500 envelope_origin_500
def checked_500 : CheckedCard where
  required := required_500
  envelope := envelope_500
  height := height_500
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_500
end SnakyPrototype.Certificate21

end OAI
