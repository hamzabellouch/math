import OAI.GameTheory.SnakyConditional.Templates.Level29Part02

namespace OAI

namespace SnakyConditional
def required_592 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (-1, -1)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows010.named_envelope_592_4 : List Cell := ([(-7, 5), (-7, 6), (-7, 8), (-6, 3), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_592_4_chain : (named_envelope_592_4.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_592_4_head : (named_envelope_592_4.map Internal.SnakyRows010.namedCellKey).head? = some (-891 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_592_4_last : (named_envelope_592_4.map Internal.SnakyRows010.namedCellKey).getLast? = some (-635 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_592_5 : List Cell := ([(-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_592_5_chain : (named_envelope_592_5.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_592_5_head : (named_envelope_592_5.map Internal.SnakyRows010.namedCellKey).head? = some (-634 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_592_5_last : (named_envelope_592_5.map Internal.SnakyRows010.namedCellKey).getLast? = some (-505 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_592_3 : List Cell := Internal.SnakyRows010.named_envelope_592_4 ++ Internal.SnakyRows010.named_envelope_592_5
theorem Internal.SnakyRows010.named_envelope_592_3_chain : (named_envelope_592_3.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_592_4 Internal.SnakyRows010.named_envelope_592_5 (-635 : ℤ) (-634 : ℤ)
    Internal.SnakyRows010.named_envelope_592_4_chain Internal.SnakyRows010.named_envelope_592_5_chain Internal.SnakyRows010.named_envelope_592_4_last Internal.SnakyRows010.named_envelope_592_5_head (by decide)
theorem Internal.SnakyRows010.named_envelope_592_3_head : (named_envelope_592_3.map Internal.SnakyRows010.namedCellKey).head? = some (-891 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_592_4 Internal.SnakyRows010.named_envelope_592_5 (-891 : ℤ) Internal.SnakyRows010.named_envelope_592_4_head
theorem Internal.SnakyRows010.named_envelope_592_3_last : (named_envelope_592_3.map Internal.SnakyRows010.namedCellKey).getLast? = some (-505 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_592_4 Internal.SnakyRows010.named_envelope_592_5 (-505 : ℤ) Internal.SnakyRows010.named_envelope_592_5_last
def Internal.SnakyRows010.named_envelope_592_7 : List Cell := ([(-4, 8), (-4, 9), (-4, 10), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_592_7_chain : (named_envelope_592_7.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_592_7_head : (named_envelope_592_7.map Internal.SnakyRows010.namedCellKey).head? = some (-504 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_592_7_last : (named_envelope_592_7.map Internal.SnakyRows010.namedCellKey).getLast? = some (-374 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_592_8 : List Cell := ([(-3, 11), (-3, 12), (-3, 13), (-2, -6), (-2, -5), (-2, -4), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_592_8_chain : (named_envelope_592_8.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_592_8_head : (named_envelope_592_8.map Internal.SnakyRows010.namedCellKey).head? = some (-373 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_592_8_last : (named_envelope_592_8.map Internal.SnakyRows010.namedCellKey).getLast? = some (-250 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_592_6 : List Cell := Internal.SnakyRows010.named_envelope_592_7 ++ Internal.SnakyRows010.named_envelope_592_8
theorem Internal.SnakyRows010.named_envelope_592_6_chain : (named_envelope_592_6.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_592_7 Internal.SnakyRows010.named_envelope_592_8 (-374 : ℤ) (-373 : ℤ)
    Internal.SnakyRows010.named_envelope_592_7_chain Internal.SnakyRows010.named_envelope_592_8_chain Internal.SnakyRows010.named_envelope_592_7_last Internal.SnakyRows010.named_envelope_592_8_head (by decide)
theorem Internal.SnakyRows010.named_envelope_592_6_head : (named_envelope_592_6.map Internal.SnakyRows010.namedCellKey).head? = some (-504 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_592_7 Internal.SnakyRows010.named_envelope_592_8 (-504 : ℤ) Internal.SnakyRows010.named_envelope_592_7_head
theorem Internal.SnakyRows010.named_envelope_592_6_last : (named_envelope_592_6.map Internal.SnakyRows010.namedCellKey).getLast? = some (-250 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_592_7 Internal.SnakyRows010.named_envelope_592_8 (-250 : ℤ) Internal.SnakyRows010.named_envelope_592_8_last
def Internal.SnakyRows010.named_envelope_592_2 : List Cell := Internal.SnakyRows010.named_envelope_592_3 ++ Internal.SnakyRows010.named_envelope_592_6
theorem Internal.SnakyRows010.named_envelope_592_2_chain : (named_envelope_592_2.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_592_3 Internal.SnakyRows010.named_envelope_592_6 (-505 : ℤ) (-504 : ℤ)
    Internal.SnakyRows010.named_envelope_592_3_chain Internal.SnakyRows010.named_envelope_592_6_chain Internal.SnakyRows010.named_envelope_592_3_last Internal.SnakyRows010.named_envelope_592_6_head (by decide)
theorem Internal.SnakyRows010.named_envelope_592_2_head : (named_envelope_592_2.map Internal.SnakyRows010.namedCellKey).head? = some (-891 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_592_3 Internal.SnakyRows010.named_envelope_592_6 (-891 : ℤ) Internal.SnakyRows010.named_envelope_592_3_head
theorem Internal.SnakyRows010.named_envelope_592_2_last : (named_envelope_592_2.map Internal.SnakyRows010.namedCellKey).getLast? = some (-250 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_592_3 Internal.SnakyRows010.named_envelope_592_6 (-250 : ℤ) Internal.SnakyRows010.named_envelope_592_6_last
def Internal.SnakyRows010.named_envelope_592_11 : List Cell := ([(-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_592_11_chain : (named_envelope_592_11.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_592_11_head : (named_envelope_592_11.map Internal.SnakyRows010.namedCellKey).head? = some (-249 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_592_11_last : (named_envelope_592_11.map Internal.SnakyRows010.namedCellKey).getLast? = some (-127 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_592_12 : List Cell := ([(-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -6)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_592_12_chain : (named_envelope_592_12.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_592_12_head : (named_envelope_592_12.map Internal.SnakyRows010.namedCellKey).head? = some (-126 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_592_12_last : (named_envelope_592_12.map Internal.SnakyRows010.namedCellKey).getLast? = some (-6 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_592_10 : List Cell := Internal.SnakyRows010.named_envelope_592_11 ++ Internal.SnakyRows010.named_envelope_592_12
theorem Internal.SnakyRows010.named_envelope_592_10_chain : (named_envelope_592_10.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_592_11 Internal.SnakyRows010.named_envelope_592_12 (-127 : ℤ) (-126 : ℤ)
    Internal.SnakyRows010.named_envelope_592_11_chain Internal.SnakyRows010.named_envelope_592_12_chain Internal.SnakyRows010.named_envelope_592_11_last Internal.SnakyRows010.named_envelope_592_12_head (by decide)
theorem Internal.SnakyRows010.named_envelope_592_10_head : (named_envelope_592_10.map Internal.SnakyRows010.namedCellKey).head? = some (-249 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_592_11 Internal.SnakyRows010.named_envelope_592_12 (-249 : ℤ) Internal.SnakyRows010.named_envelope_592_11_head
theorem Internal.SnakyRows010.named_envelope_592_10_last : (named_envelope_592_10.map Internal.SnakyRows010.namedCellKey).getLast? = some (-6 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_592_11 Internal.SnakyRows010.named_envelope_592_12 (-6 : ℤ) Internal.SnakyRows010.named_envelope_592_12_last
def Internal.SnakyRows010.named_envelope_592_14 : List Cell := ([(0, -5), (0, -4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_592_14_chain : (named_envelope_592_14.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_592_14_head : (named_envelope_592_14.map Internal.SnakyRows010.namedCellKey).head? = some (-5 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_592_14_last : (named_envelope_592_14.map Internal.SnakyRows010.namedCellKey).getLast? = some (9 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_592_15 : List Cell := ([(0, 10), (0, 11), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_592_15_chain : (named_envelope_592_15.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_592_15_head : (named_envelope_592_15.map Internal.SnakyRows010.namedCellKey).head? = some (10 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_592_15_last : (named_envelope_592_15.map Internal.SnakyRows010.namedCellKey).getLast? = some (135 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_592_13 : List Cell := Internal.SnakyRows010.named_envelope_592_14 ++ Internal.SnakyRows010.named_envelope_592_15
theorem Internal.SnakyRows010.named_envelope_592_13_chain : (named_envelope_592_13.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_592_14 Internal.SnakyRows010.named_envelope_592_15 (9 : ℤ) (10 : ℤ)
    Internal.SnakyRows010.named_envelope_592_14_chain Internal.SnakyRows010.named_envelope_592_15_chain Internal.SnakyRows010.named_envelope_592_14_last Internal.SnakyRows010.named_envelope_592_15_head (by decide)
theorem Internal.SnakyRows010.named_envelope_592_13_head : (named_envelope_592_13.map Internal.SnakyRows010.namedCellKey).head? = some (-5 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_592_14 Internal.SnakyRows010.named_envelope_592_15 (-5 : ℤ) Internal.SnakyRows010.named_envelope_592_14_head
theorem Internal.SnakyRows010.named_envelope_592_13_last : (named_envelope_592_13.map Internal.SnakyRows010.namedCellKey).getLast? = some (135 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_592_14 Internal.SnakyRows010.named_envelope_592_15 (135 : ℤ) Internal.SnakyRows010.named_envelope_592_15_last
def Internal.SnakyRows010.named_envelope_592_9 : List Cell := Internal.SnakyRows010.named_envelope_592_10 ++ Internal.SnakyRows010.named_envelope_592_13
theorem Internal.SnakyRows010.named_envelope_592_9_chain : (named_envelope_592_9.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_592_10 Internal.SnakyRows010.named_envelope_592_13 (-6 : ℤ) (-5 : ℤ)
    Internal.SnakyRows010.named_envelope_592_10_chain Internal.SnakyRows010.named_envelope_592_13_chain Internal.SnakyRows010.named_envelope_592_10_last Internal.SnakyRows010.named_envelope_592_13_head (by decide)
theorem Internal.SnakyRows010.named_envelope_592_9_head : (named_envelope_592_9.map Internal.SnakyRows010.namedCellKey).head? = some (-249 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_592_10 Internal.SnakyRows010.named_envelope_592_13 (-249 : ℤ) Internal.SnakyRows010.named_envelope_592_10_head
theorem Internal.SnakyRows010.named_envelope_592_9_last : (named_envelope_592_9.map Internal.SnakyRows010.namedCellKey).getLast? = some (135 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_592_10 Internal.SnakyRows010.named_envelope_592_13 (135 : ℤ) Internal.SnakyRows010.named_envelope_592_13_last
def Internal.SnakyRows010.named_envelope_592_1 : List Cell := Internal.SnakyRows010.named_envelope_592_2 ++ Internal.SnakyRows010.named_envelope_592_9
theorem Internal.SnakyRows010.named_envelope_592_1_chain : (named_envelope_592_1.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_592_2 Internal.SnakyRows010.named_envelope_592_9 (-250 : ℤ) (-249 : ℤ)
    Internal.SnakyRows010.named_envelope_592_2_chain Internal.SnakyRows010.named_envelope_592_9_chain Internal.SnakyRows010.named_envelope_592_2_last Internal.SnakyRows010.named_envelope_592_9_head (by decide)
theorem Internal.SnakyRows010.named_envelope_592_1_head : (named_envelope_592_1.map Internal.SnakyRows010.namedCellKey).head? = some (-891 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_592_2 Internal.SnakyRows010.named_envelope_592_9 (-891 : ℤ) Internal.SnakyRows010.named_envelope_592_2_head
theorem Internal.SnakyRows010.named_envelope_592_1_last : (named_envelope_592_1.map Internal.SnakyRows010.namedCellKey).getLast? = some (135 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_592_2 Internal.SnakyRows010.named_envelope_592_9 (135 : ℤ) Internal.SnakyRows010.named_envelope_592_9_last
def Internal.SnakyRows010.named_envelope_592_19 : List Cell := ([(1, 8), (1, 9), (1, 10), (1, 11), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_592_19_chain : (named_envelope_592_19.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_592_19_head : (named_envelope_592_19.map Internal.SnakyRows010.namedCellKey).head? = some (136 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_592_19_last : (named_envelope_592_19.map Internal.SnakyRows010.namedCellKey).getLast? = some (259 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_592_20 : List Cell := ([(2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_592_20_chain : (named_envelope_592_20.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_592_20_head : (named_envelope_592_20.map Internal.SnakyRows010.namedCellKey).head? = some (260 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_592_20_last : (named_envelope_592_20.map Internal.SnakyRows010.namedCellKey).getLast? = some (384 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_592_18 : List Cell := Internal.SnakyRows010.named_envelope_592_19 ++ Internal.SnakyRows010.named_envelope_592_20
theorem Internal.SnakyRows010.named_envelope_592_18_chain : (named_envelope_592_18.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_592_19 Internal.SnakyRows010.named_envelope_592_20 (259 : ℤ) (260 : ℤ)
    Internal.SnakyRows010.named_envelope_592_19_chain Internal.SnakyRows010.named_envelope_592_20_chain Internal.SnakyRows010.named_envelope_592_19_last Internal.SnakyRows010.named_envelope_592_20_head (by decide)
theorem Internal.SnakyRows010.named_envelope_592_18_head : (named_envelope_592_18.map Internal.SnakyRows010.namedCellKey).head? = some (136 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_592_19 Internal.SnakyRows010.named_envelope_592_20 (136 : ℤ) Internal.SnakyRows010.named_envelope_592_19_head
theorem Internal.SnakyRows010.named_envelope_592_18_last : (named_envelope_592_18.map Internal.SnakyRows010.namedCellKey).getLast? = some (384 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_592_19 Internal.SnakyRows010.named_envelope_592_20 (384 : ℤ) Internal.SnakyRows010.named_envelope_592_20_last
def Internal.SnakyRows010.named_envelope_592_22 : List Cell := ([(3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, -5), (4, -4)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_592_22_chain : (named_envelope_592_22.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_592_22_head : (named_envelope_592_22.map Internal.SnakyRows010.namedCellKey).head? = some (385 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_592_22_last : (named_envelope_592_22.map Internal.SnakyRows010.namedCellKey).getLast? = some (508 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_592_23 : List Cell := ([(4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -3)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_592_23_chain : (named_envelope_592_23.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_592_23_head : (named_envelope_592_23.map Internal.SnakyRows010.namedCellKey).head? = some (509 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_592_23_last : (named_envelope_592_23.map Internal.SnakyRows010.namedCellKey).getLast? = some (637 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_592_21 : List Cell := Internal.SnakyRows010.named_envelope_592_22 ++ Internal.SnakyRows010.named_envelope_592_23
theorem Internal.SnakyRows010.named_envelope_592_21_chain : (named_envelope_592_21.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_592_22 Internal.SnakyRows010.named_envelope_592_23 (508 : ℤ) (509 : ℤ)
    Internal.SnakyRows010.named_envelope_592_22_chain Internal.SnakyRows010.named_envelope_592_23_chain Internal.SnakyRows010.named_envelope_592_22_last Internal.SnakyRows010.named_envelope_592_23_head (by decide)
theorem Internal.SnakyRows010.named_envelope_592_21_head : (named_envelope_592_21.map Internal.SnakyRows010.namedCellKey).head? = some (385 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_592_22 Internal.SnakyRows010.named_envelope_592_23 (385 : ℤ) Internal.SnakyRows010.named_envelope_592_22_head
theorem Internal.SnakyRows010.named_envelope_592_21_last : (named_envelope_592_21.map Internal.SnakyRows010.namedCellKey).getLast? = some (637 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_592_22 Internal.SnakyRows010.named_envelope_592_23 (637 : ℤ) Internal.SnakyRows010.named_envelope_592_23_last
def Internal.SnakyRows010.named_envelope_592_17 : List Cell := Internal.SnakyRows010.named_envelope_592_18 ++ Internal.SnakyRows010.named_envelope_592_21
theorem Internal.SnakyRows010.named_envelope_592_17_chain : (named_envelope_592_17.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_592_18 Internal.SnakyRows010.named_envelope_592_21 (384 : ℤ) (385 : ℤ)
    Internal.SnakyRows010.named_envelope_592_18_chain Internal.SnakyRows010.named_envelope_592_21_chain Internal.SnakyRows010.named_envelope_592_18_last Internal.SnakyRows010.named_envelope_592_21_head (by decide)
theorem Internal.SnakyRows010.named_envelope_592_17_head : (named_envelope_592_17.map Internal.SnakyRows010.namedCellKey).head? = some (136 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_592_18 Internal.SnakyRows010.named_envelope_592_21 (136 : ℤ) Internal.SnakyRows010.named_envelope_592_18_head
theorem Internal.SnakyRows010.named_envelope_592_17_last : (named_envelope_592_17.map Internal.SnakyRows010.namedCellKey).getLast? = some (637 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_592_18 Internal.SnakyRows010.named_envelope_592_21 (637 : ℤ) Internal.SnakyRows010.named_envelope_592_21_last
def Internal.SnakyRows010.named_envelope_592_26 : List Cell := ([(5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, -3), (6, -2)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_592_26_chain : (named_envelope_592_26.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_592_26_head : (named_envelope_592_26.map Internal.SnakyRows010.namedCellKey).head? = some (638 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_592_26_last : (named_envelope_592_26.map Internal.SnakyRows010.namedCellKey).getLast? = some (766 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_592_27 : List Cell := ([(6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, -3), (7, -2), (7, -1)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_592_27_chain : (named_envelope_592_27.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_592_27_head : (named_envelope_592_27.map Internal.SnakyRows010.namedCellKey).head? = some (767 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_592_27_last : (named_envelope_592_27.map Internal.SnakyRows010.namedCellKey).getLast? = some (895 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_592_25 : List Cell := Internal.SnakyRows010.named_envelope_592_26 ++ Internal.SnakyRows010.named_envelope_592_27
theorem Internal.SnakyRows010.named_envelope_592_25_chain : (named_envelope_592_25.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_592_26 Internal.SnakyRows010.named_envelope_592_27 (766 : ℤ) (767 : ℤ)
    Internal.SnakyRows010.named_envelope_592_26_chain Internal.SnakyRows010.named_envelope_592_27_chain Internal.SnakyRows010.named_envelope_592_26_last Internal.SnakyRows010.named_envelope_592_27_head (by decide)
theorem Internal.SnakyRows010.named_envelope_592_25_head : (named_envelope_592_25.map Internal.SnakyRows010.namedCellKey).head? = some (638 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_592_26 Internal.SnakyRows010.named_envelope_592_27 (638 : ℤ) Internal.SnakyRows010.named_envelope_592_26_head
theorem Internal.SnakyRows010.named_envelope_592_25_last : (named_envelope_592_25.map Internal.SnakyRows010.namedCellKey).getLast? = some (895 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_592_26 Internal.SnakyRows010.named_envelope_592_27 (895 : ℤ) Internal.SnakyRows010.named_envelope_592_27_last
def Internal.SnakyRows010.named_envelope_592_29 : List Cell := ([(7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_592_29_chain : (named_envelope_592_29.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_592_29_head : (named_envelope_592_29.map Internal.SnakyRows010.namedCellKey).head? = some (896 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_592_29_last : (named_envelope_592_29.map Internal.SnakyRows010.namedCellKey).getLast? = some (1028 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_592_30 : List Cell := ([(8, 5), (8, 6), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (10, 0), (10, 1), (10, 2), (11, 0), (11, 2)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_592_30_chain : (named_envelope_592_30.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_592_30_head : (named_envelope_592_30.map Internal.SnakyRows010.namedCellKey).head? = some (1029 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_592_30_last : (named_envelope_592_30.map Internal.SnakyRows010.namedCellKey).getLast? = some (1410 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_592_28 : List Cell := Internal.SnakyRows010.named_envelope_592_29 ++ Internal.SnakyRows010.named_envelope_592_30
theorem Internal.SnakyRows010.named_envelope_592_28_chain : (named_envelope_592_28.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_592_29 Internal.SnakyRows010.named_envelope_592_30 (1028 : ℤ) (1029 : ℤ)
    Internal.SnakyRows010.named_envelope_592_29_chain Internal.SnakyRows010.named_envelope_592_30_chain Internal.SnakyRows010.named_envelope_592_29_last Internal.SnakyRows010.named_envelope_592_30_head (by decide)
theorem Internal.SnakyRows010.named_envelope_592_28_head : (named_envelope_592_28.map Internal.SnakyRows010.namedCellKey).head? = some (896 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_592_29 Internal.SnakyRows010.named_envelope_592_30 (896 : ℤ) Internal.SnakyRows010.named_envelope_592_29_head
theorem Internal.SnakyRows010.named_envelope_592_28_last : (named_envelope_592_28.map Internal.SnakyRows010.namedCellKey).getLast? = some (1410 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_592_29 Internal.SnakyRows010.named_envelope_592_30 (1410 : ℤ) Internal.SnakyRows010.named_envelope_592_30_last
def Internal.SnakyRows010.named_envelope_592_24 : List Cell := Internal.SnakyRows010.named_envelope_592_25 ++ Internal.SnakyRows010.named_envelope_592_28
theorem Internal.SnakyRows010.named_envelope_592_24_chain : (named_envelope_592_24.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_592_25 Internal.SnakyRows010.named_envelope_592_28 (895 : ℤ) (896 : ℤ)
    Internal.SnakyRows010.named_envelope_592_25_chain Internal.SnakyRows010.named_envelope_592_28_chain Internal.SnakyRows010.named_envelope_592_25_last Internal.SnakyRows010.named_envelope_592_28_head (by decide)
theorem Internal.SnakyRows010.named_envelope_592_24_head : (named_envelope_592_24.map Internal.SnakyRows010.namedCellKey).head? = some (638 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_592_25 Internal.SnakyRows010.named_envelope_592_28 (638 : ℤ) Internal.SnakyRows010.named_envelope_592_25_head
theorem Internal.SnakyRows010.named_envelope_592_24_last : (named_envelope_592_24.map Internal.SnakyRows010.namedCellKey).getLast? = some (1410 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_592_25 Internal.SnakyRows010.named_envelope_592_28 (1410 : ℤ) Internal.SnakyRows010.named_envelope_592_28_last
def Internal.SnakyRows010.named_envelope_592_16 : List Cell := Internal.SnakyRows010.named_envelope_592_17 ++ Internal.SnakyRows010.named_envelope_592_24
theorem Internal.SnakyRows010.named_envelope_592_16_chain : (named_envelope_592_16.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_592_17 Internal.SnakyRows010.named_envelope_592_24 (637 : ℤ) (638 : ℤ)
    Internal.SnakyRows010.named_envelope_592_17_chain Internal.SnakyRows010.named_envelope_592_24_chain Internal.SnakyRows010.named_envelope_592_17_last Internal.SnakyRows010.named_envelope_592_24_head (by decide)
theorem Internal.SnakyRows010.named_envelope_592_16_head : (named_envelope_592_16.map Internal.SnakyRows010.namedCellKey).head? = some (136 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_592_17 Internal.SnakyRows010.named_envelope_592_24 (136 : ℤ) Internal.SnakyRows010.named_envelope_592_17_head
theorem Internal.SnakyRows010.named_envelope_592_16_last : (named_envelope_592_16.map Internal.SnakyRows010.namedCellKey).getLast? = some (1410 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_592_17 Internal.SnakyRows010.named_envelope_592_24 (1410 : ℤ) Internal.SnakyRows010.named_envelope_592_24_last
def Internal.SnakyRows010.named_envelope_592_0 : List Cell := Internal.SnakyRows010.named_envelope_592_1 ++ Internal.SnakyRows010.named_envelope_592_16
theorem Internal.SnakyRows010.named_envelope_592_0_chain : (named_envelope_592_0.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_592_1 Internal.SnakyRows010.named_envelope_592_16 (135 : ℤ) (136 : ℤ)
    Internal.SnakyRows010.named_envelope_592_1_chain Internal.SnakyRows010.named_envelope_592_16_chain Internal.SnakyRows010.named_envelope_592_1_last Internal.SnakyRows010.named_envelope_592_16_head (by decide)
theorem Internal.SnakyRows010.named_envelope_592_0_head : (named_envelope_592_0.map Internal.SnakyRows010.namedCellKey).head? = some (-891 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_592_1 Internal.SnakyRows010.named_envelope_592_16 (-891 : ℤ) Internal.SnakyRows010.named_envelope_592_1_head
theorem Internal.SnakyRows010.named_envelope_592_0_last : (named_envelope_592_0.map Internal.SnakyRows010.namedCellKey).getLast? = some (1410 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_592_1 Internal.SnakyRows010.named_envelope_592_16 (1410 : ℤ) Internal.SnakyRows010.named_envelope_592_16_last
theorem Internal.SnakyRows010.named_envelope_592_nodup : (Internal.SnakyRows010.named_envelope_592_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows010.named_nodup_of_chain Internal.SnakyRows010.named_envelope_592_0 Internal.SnakyRows010.named_envelope_592_0_chain
def envelope_592 : Finset Cell := ⟨(Internal.SnakyRows010.named_envelope_592_0 : Multiset Cell), Internal.SnakyRows010.named_envelope_592_nodup⟩
def childrenC_592 : Fin 2 → Finset Cell := ![(placedSet 0 (0, 1) required_588), (placedSet 7 (-1, -4) required_108)]
def childrenD_592 : Fin 2 → Finset Cell := ![(placedSet 0 (0, 1) envelope_588), (placedSet 7 (-1, -4) envelope_108)]
theorem common_sub_592 : commonEnvelope childrenD_592 ⊆ insert (0, 0) required_592 := by decide
theorem child_required_sub_592 : ∀ j, childrenC_592 j ⊆ insert (0, 0) required_592 := by decide
theorem Internal.SnakyRows010.containment_592_0 :
    placedSet 0 (0, 1) envelope_588 ⊆ envelope_592 := by decide +kernel
theorem Internal.SnakyRows010.containment_592_1 :
    placedSet 7 (-1, -4) envelope_108 ⊆ envelope_592 := by decide
theorem child_envelope_sub_592 : ∀ j, childrenD_592 j ⊆ envelope_592 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows010.containment_592_0
  · exact Internal.SnakyRows010.containment_592_1
theorem pivot_mem_592 : (0, 0) ∈ envelope_592 := by decide
theorem children_work_592 : ∀ j, Template HasSnaky 27 (childrenC_592 j) (childrenD_592 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_588 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_108 7 (-1, -4)).mono (by decide)
theorem row_works_592 : Template HasSnaky 28 required_592 envelope_592 := by
  refine compose HasSnaky 27 childrenC_592 childrenD_592 children_work_592 (0, 0)
    required_592 envelope_592 pivot_mem_592 child_required_sub_592 child_envelope_sub_592 ?_
  intro b hb; exact common_sub_592 (mem_commonEnvelope childrenD_592 b hb)
end SnakyConditional

end OAI
