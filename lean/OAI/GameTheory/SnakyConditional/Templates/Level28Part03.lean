import OAI.GameTheory.SnakyConditional.Templates.Level27Part03

namespace OAI

namespace SnakyConditional
def required_581 : Finset Cell := ⟨(([(0, -3), (0, -1), (1, -4), (1, -3)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows009.named_envelope_581_4 : List Cell := ([(-6, 2), (-6, 3), (-6, 4), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-4, 1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_581_4_chain : (named_envelope_581_4.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_581_4_head : (named_envelope_581_4.map Internal.SnakyRows009.namedCellKey).head? = some (-766 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_581_4_last : (named_envelope_581_4.map Internal.SnakyRows009.namedCellKey).getLast? = some (-511 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_581_5 : List Cell := ([(-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, -1), (-3, 0), (-3, 1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_581_5_chain : (named_envelope_581_5.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_581_5_head : (named_envelope_581_5.map Internal.SnakyRows009.namedCellKey).head? = some (-510 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_581_5_last : (named_envelope_581_5.map Internal.SnakyRows009.namedCellKey).getLast? = some (-383 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_581_3 : List Cell := Internal.SnakyRows009.named_envelope_581_4 ++ Internal.SnakyRows009.named_envelope_581_5
theorem Internal.SnakyRows009.named_envelope_581_3_chain : (named_envelope_581_3.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_581_4 Internal.SnakyRows009.named_envelope_581_5 (-511 : ℤ) (-510 : ℤ)
    Internal.SnakyRows009.named_envelope_581_4_chain Internal.SnakyRows009.named_envelope_581_5_chain Internal.SnakyRows009.named_envelope_581_4_last Internal.SnakyRows009.named_envelope_581_5_head (by decide)
theorem Internal.SnakyRows009.named_envelope_581_3_head : (named_envelope_581_3.map Internal.SnakyRows009.namedCellKey).head? = some (-766 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_581_4 Internal.SnakyRows009.named_envelope_581_5 (-766 : ℤ) Internal.SnakyRows009.named_envelope_581_4_head
theorem Internal.SnakyRows009.named_envelope_581_3_last : (named_envelope_581_3.map Internal.SnakyRows009.namedCellKey).getLast? = some (-383 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_581_4 Internal.SnakyRows009.named_envelope_581_5 (-383 : ℤ) Internal.SnakyRows009.named_envelope_581_5_last
def Internal.SnakyRows009.named_envelope_581_7 : List Cell := ([(-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, 0), (-2, 1), (-2, 2)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_581_7_chain : (named_envelope_581_7.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_581_7_head : (named_envelope_581_7.map Internal.SnakyRows009.namedCellKey).head? = some (-382 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_581_7_last : (named_envelope_581_7.map Internal.SnakyRows009.namedCellKey).getLast? = some (-254 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_581_8 : List Cell := ([(-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, 0), (-1, 1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_581_8_chain : (named_envelope_581_8.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_581_8_head : (named_envelope_581_8.map Internal.SnakyRows009.namedCellKey).head? = some (-253 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_581_8_last : (named_envelope_581_8.map Internal.SnakyRows009.namedCellKey).getLast? = some (-127 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_581_6 : List Cell := Internal.SnakyRows009.named_envelope_581_7 ++ Internal.SnakyRows009.named_envelope_581_8
theorem Internal.SnakyRows009.named_envelope_581_6_chain : (named_envelope_581_6.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_581_7 Internal.SnakyRows009.named_envelope_581_8 (-254 : ℤ) (-253 : ℤ)
    Internal.SnakyRows009.named_envelope_581_7_chain Internal.SnakyRows009.named_envelope_581_8_chain Internal.SnakyRows009.named_envelope_581_7_last Internal.SnakyRows009.named_envelope_581_8_head (by decide)
theorem Internal.SnakyRows009.named_envelope_581_6_head : (named_envelope_581_6.map Internal.SnakyRows009.namedCellKey).head? = some (-382 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_581_7 Internal.SnakyRows009.named_envelope_581_8 (-382 : ℤ) Internal.SnakyRows009.named_envelope_581_7_head
theorem Internal.SnakyRows009.named_envelope_581_6_last : (named_envelope_581_6.map Internal.SnakyRows009.namedCellKey).getLast? = some (-127 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_581_7 Internal.SnakyRows009.named_envelope_581_8 (-127 : ℤ) Internal.SnakyRows009.named_envelope_581_8_last
def Internal.SnakyRows009.named_envelope_581_2 : List Cell := Internal.SnakyRows009.named_envelope_581_3 ++ Internal.SnakyRows009.named_envelope_581_6
theorem Internal.SnakyRows009.named_envelope_581_2_chain : (named_envelope_581_2.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_581_3 Internal.SnakyRows009.named_envelope_581_6 (-383 : ℤ) (-382 : ℤ)
    Internal.SnakyRows009.named_envelope_581_3_chain Internal.SnakyRows009.named_envelope_581_6_chain Internal.SnakyRows009.named_envelope_581_3_last Internal.SnakyRows009.named_envelope_581_6_head (by decide)
theorem Internal.SnakyRows009.named_envelope_581_2_head : (named_envelope_581_2.map Internal.SnakyRows009.namedCellKey).head? = some (-766 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_581_3 Internal.SnakyRows009.named_envelope_581_6 (-766 : ℤ) Internal.SnakyRows009.named_envelope_581_3_head
theorem Internal.SnakyRows009.named_envelope_581_2_last : (named_envelope_581_2.map Internal.SnakyRows009.namedCellKey).getLast? = some (-127 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_581_3 Internal.SnakyRows009.named_envelope_581_6 (-127 : ℤ) Internal.SnakyRows009.named_envelope_581_6_last
def Internal.SnakyRows009.named_envelope_581_11 : List Cell := ([(-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_581_11_chain : (named_envelope_581_11.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_581_11_head : (named_envelope_581_11.map Internal.SnakyRows009.namedCellKey).head? = some (-126 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_581_11_last : (named_envelope_581_11.map Internal.SnakyRows009.namedCellKey).getLast? = some (-118 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_581_12 : List Cell := ([(0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_581_12_chain : (named_envelope_581_12.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_581_12_head : (named_envelope_581_12.map Internal.SnakyRows009.namedCellKey).head? = some (-3 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_581_12_last : (named_envelope_581_12.map Internal.SnakyRows009.namedCellKey).getLast? = some (5 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_581_10 : List Cell := Internal.SnakyRows009.named_envelope_581_11 ++ Internal.SnakyRows009.named_envelope_581_12
theorem Internal.SnakyRows009.named_envelope_581_10_chain : (named_envelope_581_10.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_581_11 Internal.SnakyRows009.named_envelope_581_12 (-118 : ℤ) (-3 : ℤ)
    Internal.SnakyRows009.named_envelope_581_11_chain Internal.SnakyRows009.named_envelope_581_12_chain Internal.SnakyRows009.named_envelope_581_11_last Internal.SnakyRows009.named_envelope_581_12_head (by decide)
theorem Internal.SnakyRows009.named_envelope_581_10_head : (named_envelope_581_10.map Internal.SnakyRows009.namedCellKey).head? = some (-126 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_581_11 Internal.SnakyRows009.named_envelope_581_12 (-126 : ℤ) Internal.SnakyRows009.named_envelope_581_11_head
theorem Internal.SnakyRows009.named_envelope_581_10_last : (named_envelope_581_10.map Internal.SnakyRows009.namedCellKey).getLast? = some (5 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_581_11 Internal.SnakyRows009.named_envelope_581_12 (5 : ℤ) Internal.SnakyRows009.named_envelope_581_12_last
def Internal.SnakyRows009.named_envelope_581_14 : List Cell := ([(0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -4), (1, -3), (1, -2), (1, -1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_581_14_chain : (named_envelope_581_14.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_581_14_head : (named_envelope_581_14.map Internal.SnakyRows009.namedCellKey).head? = some (6 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_581_14_last : (named_envelope_581_14.map Internal.SnakyRows009.namedCellKey).getLast? = some (127 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_581_15 : List Cell := ([(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_581_15_chain : (named_envelope_581_15.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_581_15_head : (named_envelope_581_15.map Internal.SnakyRows009.namedCellKey).head? = some (128 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_581_15_last : (named_envelope_581_15.map Internal.SnakyRows009.namedCellKey).getLast? = some (137 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_581_13 : List Cell := Internal.SnakyRows009.named_envelope_581_14 ++ Internal.SnakyRows009.named_envelope_581_15
theorem Internal.SnakyRows009.named_envelope_581_13_chain : (named_envelope_581_13.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_581_14 Internal.SnakyRows009.named_envelope_581_15 (127 : ℤ) (128 : ℤ)
    Internal.SnakyRows009.named_envelope_581_14_chain Internal.SnakyRows009.named_envelope_581_15_chain Internal.SnakyRows009.named_envelope_581_14_last Internal.SnakyRows009.named_envelope_581_15_head (by decide)
theorem Internal.SnakyRows009.named_envelope_581_13_head : (named_envelope_581_13.map Internal.SnakyRows009.namedCellKey).head? = some (6 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_581_14 Internal.SnakyRows009.named_envelope_581_15 (6 : ℤ) Internal.SnakyRows009.named_envelope_581_14_head
theorem Internal.SnakyRows009.named_envelope_581_13_last : (named_envelope_581_13.map Internal.SnakyRows009.namedCellKey).getLast? = some (137 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_581_14 Internal.SnakyRows009.named_envelope_581_15 (137 : ℤ) Internal.SnakyRows009.named_envelope_581_15_last
def Internal.SnakyRows009.named_envelope_581_9 : List Cell := Internal.SnakyRows009.named_envelope_581_10 ++ Internal.SnakyRows009.named_envelope_581_13
theorem Internal.SnakyRows009.named_envelope_581_9_chain : (named_envelope_581_9.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_581_10 Internal.SnakyRows009.named_envelope_581_13 (5 : ℤ) (6 : ℤ)
    Internal.SnakyRows009.named_envelope_581_10_chain Internal.SnakyRows009.named_envelope_581_13_chain Internal.SnakyRows009.named_envelope_581_10_last Internal.SnakyRows009.named_envelope_581_13_head (by decide)
theorem Internal.SnakyRows009.named_envelope_581_9_head : (named_envelope_581_9.map Internal.SnakyRows009.namedCellKey).head? = some (-126 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_581_10 Internal.SnakyRows009.named_envelope_581_13 (-126 : ℤ) Internal.SnakyRows009.named_envelope_581_10_head
theorem Internal.SnakyRows009.named_envelope_581_9_last : (named_envelope_581_9.map Internal.SnakyRows009.namedCellKey).getLast? = some (137 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_581_10 Internal.SnakyRows009.named_envelope_581_13 (137 : ℤ) Internal.SnakyRows009.named_envelope_581_13_last
def Internal.SnakyRows009.named_envelope_581_1 : List Cell := Internal.SnakyRows009.named_envelope_581_2 ++ Internal.SnakyRows009.named_envelope_581_9
theorem Internal.SnakyRows009.named_envelope_581_1_chain : (named_envelope_581_1.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_581_2 Internal.SnakyRows009.named_envelope_581_9 (-127 : ℤ) (-126 : ℤ)
    Internal.SnakyRows009.named_envelope_581_2_chain Internal.SnakyRows009.named_envelope_581_9_chain Internal.SnakyRows009.named_envelope_581_2_last Internal.SnakyRows009.named_envelope_581_9_head (by decide)
theorem Internal.SnakyRows009.named_envelope_581_1_head : (named_envelope_581_1.map Internal.SnakyRows009.namedCellKey).head? = some (-766 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_581_2 Internal.SnakyRows009.named_envelope_581_9 (-766 : ℤ) Internal.SnakyRows009.named_envelope_581_2_head
theorem Internal.SnakyRows009.named_envelope_581_1_last : (named_envelope_581_1.map Internal.SnakyRows009.namedCellKey).getLast? = some (137 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_581_2 Internal.SnakyRows009.named_envelope_581_9 (137 : ℤ) Internal.SnakyRows009.named_envelope_581_9_last
def Internal.SnakyRows009.named_envelope_581_19 : List Cell := ([(1, 10), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_581_19_chain : (named_envelope_581_19.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_581_19_head : (named_envelope_581_19.map Internal.SnakyRows009.namedCellKey).head? = some (138 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_581_19_last : (named_envelope_581_19.map Internal.SnakyRows009.namedCellKey).getLast? = some (261 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_581_20 : List Cell := ([(2, 6), (2, 7), (2, 8), (2, 9), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_581_20_chain : (named_envelope_581_20.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_581_20_head : (named_envelope_581_20.map Internal.SnakyRows009.namedCellKey).head? = some (262 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_581_20_last : (named_envelope_581_20.map Internal.SnakyRows009.namedCellKey).getLast? = some (385 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_581_18 : List Cell := Internal.SnakyRows009.named_envelope_581_19 ++ Internal.SnakyRows009.named_envelope_581_20
theorem Internal.SnakyRows009.named_envelope_581_18_chain : (named_envelope_581_18.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_581_19 Internal.SnakyRows009.named_envelope_581_20 (261 : ℤ) (262 : ℤ)
    Internal.SnakyRows009.named_envelope_581_19_chain Internal.SnakyRows009.named_envelope_581_20_chain Internal.SnakyRows009.named_envelope_581_19_last Internal.SnakyRows009.named_envelope_581_20_head (by decide)
theorem Internal.SnakyRows009.named_envelope_581_18_head : (named_envelope_581_18.map Internal.SnakyRows009.namedCellKey).head? = some (138 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_581_19 Internal.SnakyRows009.named_envelope_581_20 (138 : ℤ) Internal.SnakyRows009.named_envelope_581_19_head
theorem Internal.SnakyRows009.named_envelope_581_18_last : (named_envelope_581_18.map Internal.SnakyRows009.namedCellKey).getLast? = some (385 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_581_19 Internal.SnakyRows009.named_envelope_581_20 (385 : ℤ) Internal.SnakyRows009.named_envelope_581_20_last
def Internal.SnakyRows009.named_envelope_581_22 : List Cell := ([(3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, -4)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_581_22_chain : (named_envelope_581_22.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_581_22_head : (named_envelope_581_22.map Internal.SnakyRows009.namedCellKey).head? = some (386 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_581_22_last : (named_envelope_581_22.map Internal.SnakyRows009.namedCellKey).getLast? = some (508 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_581_23 : List Cell := ([(4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_581_23_chain : (named_envelope_581_23.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_581_23_head : (named_envelope_581_23.map Internal.SnakyRows009.namedCellKey).head? = some (509 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_581_23_last : (named_envelope_581_23.map Internal.SnakyRows009.namedCellKey).getLast? = some (518 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_581_21 : List Cell := Internal.SnakyRows009.named_envelope_581_22 ++ Internal.SnakyRows009.named_envelope_581_23
theorem Internal.SnakyRows009.named_envelope_581_21_chain : (named_envelope_581_21.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_581_22 Internal.SnakyRows009.named_envelope_581_23 (508 : ℤ) (509 : ℤ)
    Internal.SnakyRows009.named_envelope_581_22_chain Internal.SnakyRows009.named_envelope_581_23_chain Internal.SnakyRows009.named_envelope_581_22_last Internal.SnakyRows009.named_envelope_581_23_head (by decide)
theorem Internal.SnakyRows009.named_envelope_581_21_head : (named_envelope_581_21.map Internal.SnakyRows009.namedCellKey).head? = some (386 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_581_22 Internal.SnakyRows009.named_envelope_581_23 (386 : ℤ) Internal.SnakyRows009.named_envelope_581_22_head
theorem Internal.SnakyRows009.named_envelope_581_21_last : (named_envelope_581_21.map Internal.SnakyRows009.namedCellKey).getLast? = some (518 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_581_22 Internal.SnakyRows009.named_envelope_581_23 (518 : ℤ) Internal.SnakyRows009.named_envelope_581_23_last
def Internal.SnakyRows009.named_envelope_581_17 : List Cell := Internal.SnakyRows009.named_envelope_581_18 ++ Internal.SnakyRows009.named_envelope_581_21
theorem Internal.SnakyRows009.named_envelope_581_17_chain : (named_envelope_581_17.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_581_18 Internal.SnakyRows009.named_envelope_581_21 (385 : ℤ) (386 : ℤ)
    Internal.SnakyRows009.named_envelope_581_18_chain Internal.SnakyRows009.named_envelope_581_21_chain Internal.SnakyRows009.named_envelope_581_18_last Internal.SnakyRows009.named_envelope_581_21_head (by decide)
theorem Internal.SnakyRows009.named_envelope_581_17_head : (named_envelope_581_17.map Internal.SnakyRows009.namedCellKey).head? = some (138 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_581_18 Internal.SnakyRows009.named_envelope_581_21 (138 : ℤ) Internal.SnakyRows009.named_envelope_581_18_head
theorem Internal.SnakyRows009.named_envelope_581_17_last : (named_envelope_581_17.map Internal.SnakyRows009.namedCellKey).getLast? = some (518 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_581_18 Internal.SnakyRows009.named_envelope_581_21 (518 : ℤ) Internal.SnakyRows009.named_envelope_581_21_last
def Internal.SnakyRows009.named_envelope_581_26 : List Cell := ([(4, 7), (4, 8), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_581_26_chain : (named_envelope_581_26.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_581_26_head : (named_envelope_581_26.map Internal.SnakyRows009.namedCellKey).head? = some (519 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_581_26_last : (named_envelope_581_26.map Internal.SnakyRows009.namedCellKey).getLast? = some (643 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_581_27 : List Cell := ([(5, 4), (5, 5), (5, 6), (5, 7), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_581_27_chain : (named_envelope_581_27.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_581_27_head : (named_envelope_581_27.map Internal.SnakyRows009.namedCellKey).head? = some (644 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_581_27_last : (named_envelope_581_27.map Internal.SnakyRows009.namedCellKey).getLast? = some (769 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_581_25 : List Cell := Internal.SnakyRows009.named_envelope_581_26 ++ Internal.SnakyRows009.named_envelope_581_27
theorem Internal.SnakyRows009.named_envelope_581_25_chain : (named_envelope_581_25.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_581_26 Internal.SnakyRows009.named_envelope_581_27 (643 : ℤ) (644 : ℤ)
    Internal.SnakyRows009.named_envelope_581_26_chain Internal.SnakyRows009.named_envelope_581_27_chain Internal.SnakyRows009.named_envelope_581_26_last Internal.SnakyRows009.named_envelope_581_27_head (by decide)
theorem Internal.SnakyRows009.named_envelope_581_25_head : (named_envelope_581_25.map Internal.SnakyRows009.namedCellKey).head? = some (519 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_581_26 Internal.SnakyRows009.named_envelope_581_27 (519 : ℤ) Internal.SnakyRows009.named_envelope_581_26_head
theorem Internal.SnakyRows009.named_envelope_581_25_last : (named_envelope_581_25.map Internal.SnakyRows009.namedCellKey).getLast? = some (769 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_581_26 Internal.SnakyRows009.named_envelope_581_27 (769 : ℤ) Internal.SnakyRows009.named_envelope_581_27_last
def Internal.SnakyRows009.named_envelope_581_29 : List Cell := ([(6, 2), (6, 3), (6, 4), (6, 5), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_581_29_chain : (named_envelope_581_29.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_581_29_head : (named_envelope_581_29.map Internal.SnakyRows009.namedCellKey).head? = some (770 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_581_29_last : (named_envelope_581_29.map Internal.SnakyRows009.namedCellKey).getLast? = some (898 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_581_30 : List Cell := ([(7, 3), (7, 4), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (9, -2), (9, 0), (9, 2)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_581_30_chain : (named_envelope_581_30.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_581_30_head : (named_envelope_581_30.map Internal.SnakyRows009.namedCellKey).head? = some (899 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_581_30_last : (named_envelope_581_30.map Internal.SnakyRows009.namedCellKey).getLast? = some (1154 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_581_28 : List Cell := Internal.SnakyRows009.named_envelope_581_29 ++ Internal.SnakyRows009.named_envelope_581_30
theorem Internal.SnakyRows009.named_envelope_581_28_chain : (named_envelope_581_28.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_581_29 Internal.SnakyRows009.named_envelope_581_30 (898 : ℤ) (899 : ℤ)
    Internal.SnakyRows009.named_envelope_581_29_chain Internal.SnakyRows009.named_envelope_581_30_chain Internal.SnakyRows009.named_envelope_581_29_last Internal.SnakyRows009.named_envelope_581_30_head (by decide)
theorem Internal.SnakyRows009.named_envelope_581_28_head : (named_envelope_581_28.map Internal.SnakyRows009.namedCellKey).head? = some (770 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_581_29 Internal.SnakyRows009.named_envelope_581_30 (770 : ℤ) Internal.SnakyRows009.named_envelope_581_29_head
theorem Internal.SnakyRows009.named_envelope_581_28_last : (named_envelope_581_28.map Internal.SnakyRows009.namedCellKey).getLast? = some (1154 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_581_29 Internal.SnakyRows009.named_envelope_581_30 (1154 : ℤ) Internal.SnakyRows009.named_envelope_581_30_last
def Internal.SnakyRows009.named_envelope_581_24 : List Cell := Internal.SnakyRows009.named_envelope_581_25 ++ Internal.SnakyRows009.named_envelope_581_28
theorem Internal.SnakyRows009.named_envelope_581_24_chain : (named_envelope_581_24.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_581_25 Internal.SnakyRows009.named_envelope_581_28 (769 : ℤ) (770 : ℤ)
    Internal.SnakyRows009.named_envelope_581_25_chain Internal.SnakyRows009.named_envelope_581_28_chain Internal.SnakyRows009.named_envelope_581_25_last Internal.SnakyRows009.named_envelope_581_28_head (by decide)
theorem Internal.SnakyRows009.named_envelope_581_24_head : (named_envelope_581_24.map Internal.SnakyRows009.namedCellKey).head? = some (519 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_581_25 Internal.SnakyRows009.named_envelope_581_28 (519 : ℤ) Internal.SnakyRows009.named_envelope_581_25_head
theorem Internal.SnakyRows009.named_envelope_581_24_last : (named_envelope_581_24.map Internal.SnakyRows009.namedCellKey).getLast? = some (1154 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_581_25 Internal.SnakyRows009.named_envelope_581_28 (1154 : ℤ) Internal.SnakyRows009.named_envelope_581_28_last
def Internal.SnakyRows009.named_envelope_581_16 : List Cell := Internal.SnakyRows009.named_envelope_581_17 ++ Internal.SnakyRows009.named_envelope_581_24
theorem Internal.SnakyRows009.named_envelope_581_16_chain : (named_envelope_581_16.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_581_17 Internal.SnakyRows009.named_envelope_581_24 (518 : ℤ) (519 : ℤ)
    Internal.SnakyRows009.named_envelope_581_17_chain Internal.SnakyRows009.named_envelope_581_24_chain Internal.SnakyRows009.named_envelope_581_17_last Internal.SnakyRows009.named_envelope_581_24_head (by decide)
theorem Internal.SnakyRows009.named_envelope_581_16_head : (named_envelope_581_16.map Internal.SnakyRows009.namedCellKey).head? = some (138 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_581_17 Internal.SnakyRows009.named_envelope_581_24 (138 : ℤ) Internal.SnakyRows009.named_envelope_581_17_head
theorem Internal.SnakyRows009.named_envelope_581_16_last : (named_envelope_581_16.map Internal.SnakyRows009.namedCellKey).getLast? = some (1154 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_581_17 Internal.SnakyRows009.named_envelope_581_24 (1154 : ℤ) Internal.SnakyRows009.named_envelope_581_24_last
def Internal.SnakyRows009.named_envelope_581_0 : List Cell := Internal.SnakyRows009.named_envelope_581_1 ++ Internal.SnakyRows009.named_envelope_581_16
theorem Internal.SnakyRows009.named_envelope_581_0_chain : (named_envelope_581_0.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_581_1 Internal.SnakyRows009.named_envelope_581_16 (137 : ℤ) (138 : ℤ)
    Internal.SnakyRows009.named_envelope_581_1_chain Internal.SnakyRows009.named_envelope_581_16_chain Internal.SnakyRows009.named_envelope_581_1_last Internal.SnakyRows009.named_envelope_581_16_head (by decide)
theorem Internal.SnakyRows009.named_envelope_581_0_head : (named_envelope_581_0.map Internal.SnakyRows009.namedCellKey).head? = some (-766 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_581_1 Internal.SnakyRows009.named_envelope_581_16 (-766 : ℤ) Internal.SnakyRows009.named_envelope_581_1_head
theorem Internal.SnakyRows009.named_envelope_581_0_last : (named_envelope_581_0.map Internal.SnakyRows009.namedCellKey).getLast? = some (1154 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_581_1 Internal.SnakyRows009.named_envelope_581_16 (1154 : ℤ) Internal.SnakyRows009.named_envelope_581_16_last
theorem Internal.SnakyRows009.named_envelope_581_nodup : (Internal.SnakyRows009.named_envelope_581_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows009.named_nodup_of_chain Internal.SnakyRows009.named_envelope_581_0 Internal.SnakyRows009.named_envelope_581_0_chain
def envelope_581 : Finset Cell := ⟨(Internal.SnakyRows009.named_envelope_581_0 : Multiset Cell), Internal.SnakyRows009.named_envelope_581_nodup⟩
def childrenC_581 : Fin 2 → Finset Cell := ![(placedSet 4 (1, -1) required_578), (placedSet 5 (0, -2) required_2)]
def childrenD_581 : Fin 2 → Finset Cell := ![(placedSet 4 (1, -1) envelope_578), (placedSet 5 (0, -2) envelope_2)]
theorem common_sub_581 : commonEnvelope childrenD_581 ⊆ insert (0, 0) required_581 := by decide
theorem child_required_sub_581 : ∀ j, childrenC_581 j ⊆ insert (0, 0) required_581 := by decide
theorem Internal.SnakyRows009.containment_581_0 :
    placedSet 4 (1, -1) envelope_578 ⊆ envelope_581 := by decide +kernel
theorem Internal.SnakyRows009.containment_581_1 :
    placedSet 5 (0, -2) envelope_2 ⊆ envelope_581 := by decide
theorem child_envelope_sub_581 : ∀ j, childrenD_581 j ⊆ envelope_581 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows009.containment_581_0
  · exact Internal.SnakyRows009.containment_581_1
theorem pivot_mem_581 : (0, 0) ∈ envelope_581 := by decide
theorem children_work_581 : ∀ j, Template HasSnaky 25 (childrenC_581 j) (childrenD_581 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_578 4 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_2 5 (0, -2)).mono (by decide)
theorem row_works_581 : Template HasSnaky 26 required_581 envelope_581 := by
  refine compose HasSnaky 25 childrenC_581 childrenD_581 children_work_581 (0, 0)
    required_581 envelope_581 pivot_mem_581 child_required_sub_581 child_envelope_sub_581 ?_
  intro b hb; exact common_sub_581 (mem_commonEnvelope childrenD_581 b hb)
end SnakyConditional

end OAI
