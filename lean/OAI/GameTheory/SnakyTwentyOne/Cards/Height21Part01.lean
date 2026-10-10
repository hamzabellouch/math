import OAI.GameTheory.SnakyTwentyOne.Cards.Height15Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height15Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height20Part01
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_727 : Finset Cell := ∅
def envelope_727 : Finset Cell := ⟨(([(0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (2, 15), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (3, 15), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (4, 15), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (5, 15), (5, 16), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 15), (6, 16), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (7, 15), (7, 16), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14), (8, 15), (8, 16), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (9, 15), (9, 16), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (10, 13), (10, 14), (10, 15), (10, 16), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 10), (11, 11), (11, 12), (11, 13), (11, 14), (11, 15), (11, 16), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 9), (12, 10), (12, 11), (12, 12), (12, 13), (12, 14), (12, 15), (12, 16), (13, 1), (13, 2), (13, 3), (13, 4), (13, 5), (13, 6), (13, 7), (13, 8), (13, 9), (13, 10), (13, 11), (13, 12), (13, 13), (13, 14), (13, 15), (14, 1), (14, 2), (14, 3), (14, 4), (14, 5), (14, 6), (14, 7), (14, 8), (14, 9), (14, 10), (14, 11), (14, 12), (14, 13), (14, 14), (15, 3), (15, 4), (15, 5), (15, 6), (15, 7), (15, 8), (15, 9), (15, 10), (15, 11), (15, 12), (15, 13), (15, 14), (16, 4), (16, 5), (16, 6), (16, 7), (16, 8), (16, 9), (16, 10), (16, 11)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_727 : Fin 32 → Finset Cell := ![(placed21 0 (4, 3) required_648), (placed21 1 (3, 4) required_648), (placed21 3 (3, 12) required_648), (placed21 4 (4, 13) required_648), (placed21 1 (0, 0) required_708), (placed21 2 (16, 0) required_708), (placed21 4 (0, 16) required_708), (placed21 7 (16, 16) required_708), (placed21 0 (3, 3) required_712), (placed21 1 (3, 3) required_712), (placed21 2 (13, 3) required_712), (placed21 3 (3, 13) required_712), (placed21 4 (3, 13) required_712), (placed21 5 (13, 3) required_712), (placed21 6 (13, 13) required_712), (placed21 7 (13, 13) required_712), (placed21 2 (13, 3) required_713), (placed21 3 (3, 13) required_713), (placed21 4 (3, 13) required_713), (placed21 5 (13, 3) required_713), (placed21 0 (1, 1) required_725), (placed21 1 (1, 1) required_725), (placed21 2 (15, 1) required_725), (placed21 3 (1, 15) required_725), (placed21 4 (1, 15) required_725), (placed21 5 (15, 1) required_725), (placed21 6 (15, 15) required_725), (placed21 7 (15, 15) required_725), (placed21 1 (1, 1) required_726), (placed21 2 (15, 1) required_726), (placed21 4 (1, 15) required_726), (placed21 6 (15, 15) required_726)]
def childrenD_727 : Fin 32 → Finset Cell := ![(placed21 0 (4, 3) envelope_648), (placed21 1 (3, 4) envelope_648), (placed21 3 (3, 12) envelope_648), (placed21 4 (4, 13) envelope_648), (placed21 1 (0, 0) envelope_708), (placed21 2 (16, 0) envelope_708), (placed21 4 (0, 16) envelope_708), (placed21 7 (16, 16) envelope_708), (placed21 0 (3, 3) envelope_712), (placed21 1 (3, 3) envelope_712), (placed21 2 (13, 3) envelope_712), (placed21 3 (3, 13) envelope_712), (placed21 4 (3, 13) envelope_712), (placed21 5 (13, 3) envelope_712), (placed21 6 (13, 13) envelope_712), (placed21 7 (13, 13) envelope_712), (placed21 2 (13, 3) envelope_713), (placed21 3 (3, 13) envelope_713), (placed21 4 (3, 13) envelope_713), (placed21 5 (13, 3) envelope_713), (placed21 0 (1, 1) envelope_725), (placed21 1 (1, 1) envelope_725), (placed21 2 (15, 1) envelope_725), (placed21 3 (1, 15) envelope_725), (placed21 4 (1, 15) envelope_725), (placed21 5 (15, 1) envelope_725), (placed21 6 (15, 15) envelope_725), (placed21 7 (15, 15) envelope_725), (placed21 1 (1, 1) envelope_726), (placed21 2 (15, 1) envelope_726), (placed21 4 (1, 15) envelope_726), (placed21 6 (15, 15) envelope_726)]
theorem common_sub_727 : commonEnvelope childrenD_727 ⊆ insert (8, 8) required_727 := by decide +kernel
theorem child_required_sub_727 : ∀ j, childrenC_727 j ⊆ insert (8, 8) required_727 := by decide +kernel
theorem child_envelope_sub_727 : ∀ j, childrenD_727 j ⊆ envelope_727 := by decide +kernel
theorem pivot_mem_727 : (8, 8) ∈ envelope_727 := by decide +kernel
theorem children_work_727 : ∀ j, Template HasSnaky 20 (childrenC_727 j) (childrenD_727 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_648 0 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_648 1 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_648 3 (3, 12)).mono (by decide +kernel)
  · exact (placed21_template row_works_648 4 (4, 13)).mono (by decide +kernel)
  · exact (placed21_template row_works_708 1 (0, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_708 2 (16, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_708 4 (0, 16)).mono (by decide +kernel)
  · exact (placed21_template row_works_708 7 (16, 16)).mono (by decide +kernel)
  · exact (placed21_template row_works_712 0 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_712 1 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_712 2 (13, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_712 3 (3, 13)).mono (by decide +kernel)
  · exact (placed21_template row_works_712 4 (3, 13)).mono (by decide +kernel)
  · exact (placed21_template row_works_712 5 (13, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_712 6 (13, 13)).mono (by decide +kernel)
  · exact (placed21_template row_works_712 7 (13, 13)).mono (by decide +kernel)
  · exact (placed21_template row_works_713 2 (13, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_713 3 (3, 13)).mono (by decide +kernel)
  · exact (placed21_template row_works_713 4 (3, 13)).mono (by decide +kernel)
  · exact (placed21_template row_works_713 5 (13, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_725 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_725 1 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_725 2 (15, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_725 3 (1, 15)).mono (by decide +kernel)
  · exact (placed21_template row_works_725 4 (1, 15)).mono (by decide +kernel)
  · exact (placed21_template row_works_725 5 (15, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_725 6 (15, 15)).mono (by decide +kernel)
  · exact (placed21_template row_works_725 7 (15, 15)).mono (by decide +kernel)
  · exact (placed21_template row_works_726 1 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_726 2 (15, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_726 4 (1, 15)).mono (by decide +kernel)
  · exact (placed21_template row_works_726 6 (15, 15)).mono (by decide +kernel)
theorem row_works_727 : Template HasSnaky 21 required_727 envelope_727 := by
  refine compose HasSnaky 20 childrenC_727 childrenD_727 children_work_727 (8, 8)
    required_727 envelope_727 pivot_mem_727 child_required_sub_727 child_envelope_sub_727 ?_
  intro b hb
  exact common_sub_727 (mem_commonEnvelope childrenD_727 b hb)
def height_727 : ℕ := 21
def childrenH_727 : Fin 32 → ℕ := ![height_648, height_648, height_648, height_648, height_708, height_708, height_708, height_708, height_712, height_712, height_712, height_712, height_712, height_712, height_712, height_712, height_713, height_713, height_713, height_713, height_725, height_725, height_725, height_725, height_725, height_725, height_725, height_725, height_726, height_726, height_726, height_726]
theorem height_exact_727 : height_727 = 1 + Finset.univ.sup childrenH_727 := by decide +kernel
theorem required_origin_727 : ∀ x ∈ required_727,
    (∃ j, x ∈ childrenC_727 j) ∨ ∀ j, x ∈ childrenD_727 j := by decide +kernel
theorem required_exact_727 : required_727 =
    ((Finset.univ.biUnion childrenC_727) ∪ commonEnvelope childrenD_727).erase (8, 8) := by
  exact required_eq_combination childrenC_727 childrenD_727 (8, 8) required_727
    (by decide +kernel) child_required_sub_727 common_sub_727 required_origin_727
theorem envelope_origin_727 : ∀ x ∈ envelope_727,
    x = (8, 8) ∨ ∃ j, x ∈ childrenD_727 j := by decide +kernel
theorem envelope_exact_727 : envelope_727 =
    insert (8, 8) (Finset.univ.biUnion childrenD_727) := by
  exact envelope_eq_combination childrenD_727 (8, 8) envelope_727
    pivot_mem_727 child_envelope_sub_727 envelope_origin_727
def checked_727 : CheckedCard where
  required := required_727
  envelope := envelope_727
  height := height_727
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_727
end SnakyPrototype.Certificate21

end OAI
