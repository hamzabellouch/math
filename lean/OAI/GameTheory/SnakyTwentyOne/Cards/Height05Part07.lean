import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_679_i0 : Finset Cell := ⟨(([(1, 2), (1, 3), (2, 3), (3, 1), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_679_i0 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (3, 1), (3, 2), (3, 3), (4, 2), (4, 3), (4, 4), (4, 5), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_679_i0 : Fin 2 → Finset Cell := ![(placed21 4 (0, 3) required_0), (placed21 5 (5, 1) required_222)]
def childrenD_679_i0 : Fin 2 → Finset Cell := ![(placed21 4 (0, 3) envelope_0), (placed21 5 (5, 1) envelope_222)]
theorem common_sub_679_i0 : commonEnvelope childrenD_679_i0 ⊆ insert (3, 3) required_679_i0 := by decide +kernel
theorem child_required_sub_679_i0 : ∀ j, childrenC_679_i0 j ⊆ insert (3, 3) required_679_i0 := by decide +kernel
theorem child_envelope_sub_679_i0 : ∀ j, childrenD_679_i0 j ⊆ envelope_679_i0 := by decide +kernel
theorem pivot_mem_679_i0 : (3, 3) ∈ envelope_679_i0 := by decide +kernel
theorem children_work_679_i0 : ∀ j, Template HasSnaky 3 (childrenC_679_i0 j) (childrenD_679_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 4 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_222 5 (5, 1)).mono (by decide +kernel)
theorem row_works_679_i0 : Template HasSnaky 4 required_679_i0 envelope_679_i0 := by
  refine compose HasSnaky 3 childrenC_679_i0 childrenD_679_i0 children_work_679_i0 (3, 3)
    required_679_i0 envelope_679_i0 pivot_mem_679_i0 child_required_sub_679_i0 child_envelope_sub_679_i0 ?_
  intro b hb
  exact common_sub_679_i0 (mem_commonEnvelope childrenD_679_i0 b hb)
def required_679 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (3, 1), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_679 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (4, 2), (4, 3), (4, 4), (4, 5), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_679 : Fin 2 → Finset Cell := ![(placed21 0 (1, 0) required_52), required_679_i0]
def childrenD_679 : Fin 2 → Finset Cell := ![(placed21 0 (1, 0) envelope_52), envelope_679_i0]
theorem common_sub_679 : commonEnvelope childrenD_679 ⊆ insert (2, 3) required_679 := by decide +kernel
theorem child_required_sub_679 : ∀ j, childrenC_679 j ⊆ insert (2, 3) required_679 := by decide +kernel
theorem child_envelope_sub_679 : ∀ j, childrenD_679 j ⊆ envelope_679 := by decide +kernel
theorem pivot_mem_679 : (2, 3) ∈ envelope_679 := by decide +kernel
theorem children_work_679 : ∀ j, Template HasSnaky 4 (childrenC_679 j) (childrenD_679 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 0 (1, 0)).mono (by decide +kernel)
  · exact row_works_679_i0.mono (by decide +kernel)
theorem row_works_679 : Template HasSnaky 5 required_679 envelope_679 := by
  refine compose HasSnaky 4 childrenC_679 childrenD_679 children_work_679 (2, 3)
    required_679 envelope_679 pivot_mem_679 child_required_sub_679 child_envelope_sub_679 ?_
  intro b hb
  exact common_sub_679 (mem_commonEnvelope childrenD_679 b hb)
def height_679_i0 : ℕ := 4
def childrenH_679_i0 : Fin 2 → ℕ := ![height_0, height_222]
theorem height_exact_679_i0 : height_679_i0 = 1 + Finset.univ.sup childrenH_679_i0 := by decide +kernel
theorem required_origin_679_i0 : ∀ x ∈ required_679_i0,
    (∃ j, x ∈ childrenC_679_i0 j) ∨ ∀ j, x ∈ childrenD_679_i0 j := by decide +kernel
theorem required_exact_679_i0 : required_679_i0 =
    ((Finset.univ.biUnion childrenC_679_i0) ∪ commonEnvelope childrenD_679_i0).erase (3, 3) := by
  exact required_eq_combination childrenC_679_i0 childrenD_679_i0 (3, 3) required_679_i0
    (by decide +kernel) child_required_sub_679_i0 common_sub_679_i0 required_origin_679_i0
theorem envelope_origin_679_i0 : ∀ x ∈ envelope_679_i0,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_679_i0 j := by decide +kernel
theorem envelope_exact_679_i0 : envelope_679_i0 =
    insert (3, 3) (Finset.univ.biUnion childrenD_679_i0) := by
  exact envelope_eq_combination childrenD_679_i0 (3, 3) envelope_679_i0
    pivot_mem_679_i0 child_envelope_sub_679_i0 envelope_origin_679_i0
def checked_679_i0 : CheckedCard where
  required := required_679_i0
  envelope := envelope_679_i0
  height := height_679_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_679_i0
def height_679 : ℕ := 5
def childrenH_679 : Fin 2 → ℕ := ![height_52, height_679_i0]
theorem height_exact_679 : height_679 = 1 + Finset.univ.sup childrenH_679 := by decide +kernel
theorem required_origin_679 : ∀ x ∈ required_679,
    (∃ j, x ∈ childrenC_679 j) ∨ ∀ j, x ∈ childrenD_679 j := by decide +kernel
theorem required_exact_679 : required_679 =
    ((Finset.univ.biUnion childrenC_679) ∪ commonEnvelope childrenD_679).erase (2, 3) := by
  exact required_eq_combination childrenC_679 childrenD_679 (2, 3) required_679
    (by decide +kernel) child_required_sub_679 common_sub_679 required_origin_679
theorem envelope_origin_679 : ∀ x ∈ envelope_679,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_679 j := by decide +kernel
theorem envelope_exact_679 : envelope_679 =
    insert (2, 3) (Finset.univ.biUnion childrenD_679) := by
  exact envelope_eq_combination childrenD_679 (2, 3) envelope_679
    pivot_mem_679 child_envelope_sub_679 envelope_origin_679
def checked_679 : CheckedCard where
  required := required_679
  envelope := envelope_679
  height := height_679
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_679
end SnakyPrototype.Certificate21

end OAI
