import OAI.GameTheory.SnakyConditional.Templates.Level26Part06

namespace OAI

namespace SnakyConditional
open Internal.SnakyRows009
def required_579 : Finset Cell := ⟨(([(0, -3), (0, -2), (1, 0), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows009.named_envelope_579_4 : List Cell := ([(-6, 3), (-6, 4), (-6, 5), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-4, 2)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_579_4_chain : (named_envelope_579_4.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_579_4_head : (named_envelope_579_4.map Internal.SnakyRows009.namedCellKey).head? = some (-765 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_579_4_last : (named_envelope_579_4.map Internal.SnakyRows009.namedCellKey).getLast? = some (-510 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_579_5 : List Cell := ([(-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-3, 0), (-3, 1), (-3, 2)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_579_5_chain : (named_envelope_579_5.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_579_5_head : (named_envelope_579_5.map Internal.SnakyRows009.namedCellKey).head? = some (-509 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_579_5_last : (named_envelope_579_5.map Internal.SnakyRows009.namedCellKey).getLast? = some (-382 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_579_3 : List Cell := Internal.SnakyRows009.named_envelope_579_4 ++ Internal.SnakyRows009.named_envelope_579_5
theorem Internal.SnakyRows009.named_envelope_579_3_chain : (named_envelope_579_3.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_579_4 Internal.SnakyRows009.named_envelope_579_5 (-510 : ℤ) (-509 : ℤ)
    Internal.SnakyRows009.named_envelope_579_4_chain Internal.SnakyRows009.named_envelope_579_5_chain Internal.SnakyRows009.named_envelope_579_4_last Internal.SnakyRows009.named_envelope_579_5_head (by decide)
theorem Internal.SnakyRows009.named_envelope_579_3_head : (named_envelope_579_3.map Internal.SnakyRows009.namedCellKey).head? = some (-765 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_579_4 Internal.SnakyRows009.named_envelope_579_5 (-765 : ℤ) Internal.SnakyRows009.named_envelope_579_4_head
theorem Internal.SnakyRows009.named_envelope_579_3_last : (named_envelope_579_3.map Internal.SnakyRows009.namedCellKey).getLast? = some (-382 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_579_4 Internal.SnakyRows009.named_envelope_579_5 (-382 : ℤ) Internal.SnakyRows009.named_envelope_579_5_last
def Internal.SnakyRows009.named_envelope_579_7 : List Cell := ([(-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, 1), (-2, 2), (-2, 3)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_579_7_chain : (named_envelope_579_7.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_579_7_head : (named_envelope_579_7.map Internal.SnakyRows009.namedCellKey).head? = some (-381 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_579_7_last : (named_envelope_579_7.map Internal.SnakyRows009.namedCellKey).getLast? = some (-253 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_579_8 : List Cell := ([(-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-1, 1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_579_8_chain : (named_envelope_579_8.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_579_8_head : (named_envelope_579_8.map Internal.SnakyRows009.namedCellKey).head? = some (-252 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_579_8_last : (named_envelope_579_8.map Internal.SnakyRows009.namedCellKey).getLast? = some (-127 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_579_6 : List Cell := Internal.SnakyRows009.named_envelope_579_7 ++ Internal.SnakyRows009.named_envelope_579_8
theorem Internal.SnakyRows009.named_envelope_579_6_chain : (named_envelope_579_6.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_579_7 Internal.SnakyRows009.named_envelope_579_8 (-253 : ℤ) (-252 : ℤ)
    Internal.SnakyRows009.named_envelope_579_7_chain Internal.SnakyRows009.named_envelope_579_8_chain Internal.SnakyRows009.named_envelope_579_7_last Internal.SnakyRows009.named_envelope_579_8_head (by decide)
theorem Internal.SnakyRows009.named_envelope_579_6_head : (named_envelope_579_6.map Internal.SnakyRows009.namedCellKey).head? = some (-381 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_579_7 Internal.SnakyRows009.named_envelope_579_8 (-381 : ℤ) Internal.SnakyRows009.named_envelope_579_7_head
theorem Internal.SnakyRows009.named_envelope_579_6_last : (named_envelope_579_6.map Internal.SnakyRows009.namedCellKey).getLast? = some (-127 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_579_7 Internal.SnakyRows009.named_envelope_579_8 (-127 : ℤ) Internal.SnakyRows009.named_envelope_579_8_last
def Internal.SnakyRows009.named_envelope_579_2 : List Cell := Internal.SnakyRows009.named_envelope_579_3 ++ Internal.SnakyRows009.named_envelope_579_6
theorem Internal.SnakyRows009.named_envelope_579_2_chain : (named_envelope_579_2.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_579_3 Internal.SnakyRows009.named_envelope_579_6 (-382 : ℤ) (-381 : ℤ)
    Internal.SnakyRows009.named_envelope_579_3_chain Internal.SnakyRows009.named_envelope_579_6_chain Internal.SnakyRows009.named_envelope_579_3_last Internal.SnakyRows009.named_envelope_579_6_head (by decide)
theorem Internal.SnakyRows009.named_envelope_579_2_head : (named_envelope_579_2.map Internal.SnakyRows009.namedCellKey).head? = some (-765 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_579_3 Internal.SnakyRows009.named_envelope_579_6 (-765 : ℤ) Internal.SnakyRows009.named_envelope_579_3_head
theorem Internal.SnakyRows009.named_envelope_579_2_last : (named_envelope_579_2.map Internal.SnakyRows009.namedCellKey).getLast? = some (-127 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_579_3 Internal.SnakyRows009.named_envelope_579_6 (-127 : ℤ) Internal.SnakyRows009.named_envelope_579_6_last
def Internal.SnakyRows009.named_envelope_579_11 : List Cell := ([(-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_579_11_chain : (named_envelope_579_11.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_579_11_head : (named_envelope_579_11.map Internal.SnakyRows009.namedCellKey).head? = some (-126 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_579_11_last : (named_envelope_579_11.map Internal.SnakyRows009.namedCellKey).getLast? = some (-118 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_579_12 : List Cell := ([(-1, 11), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_579_12_chain : (named_envelope_579_12.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_579_12_head : (named_envelope_579_12.map Internal.SnakyRows009.namedCellKey).head? = some (-117 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_579_12_last : (named_envelope_579_12.map Internal.SnakyRows009.namedCellKey).getLast? = some (4 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_579_10 : List Cell := Internal.SnakyRows009.named_envelope_579_11 ++ Internal.SnakyRows009.named_envelope_579_12
theorem Internal.SnakyRows009.named_envelope_579_10_chain : (named_envelope_579_10.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_579_11 Internal.SnakyRows009.named_envelope_579_12 (-118 : ℤ) (-117 : ℤ)
    Internal.SnakyRows009.named_envelope_579_11_chain Internal.SnakyRows009.named_envelope_579_12_chain Internal.SnakyRows009.named_envelope_579_11_last Internal.SnakyRows009.named_envelope_579_12_head (by decide)
theorem Internal.SnakyRows009.named_envelope_579_10_head : (named_envelope_579_10.map Internal.SnakyRows009.namedCellKey).head? = some (-126 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_579_11 Internal.SnakyRows009.named_envelope_579_12 (-126 : ℤ) Internal.SnakyRows009.named_envelope_579_11_head
theorem Internal.SnakyRows009.named_envelope_579_10_last : (named_envelope_579_10.map Internal.SnakyRows009.namedCellKey).getLast? = some (4 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_579_11 Internal.SnakyRows009.named_envelope_579_12 (4 : ℤ) Internal.SnakyRows009.named_envelope_579_12_last
def Internal.SnakyRows009.named_envelope_579_14 : List Cell := ([(0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, 0), (1, 1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_579_14_chain : (named_envelope_579_14.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_579_14_head : (named_envelope_579_14.map Internal.SnakyRows009.namedCellKey).head? = some (5 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_579_14_last : (named_envelope_579_14.map Internal.SnakyRows009.namedCellKey).getLast? = some (129 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_579_15 : List Cell := ([(1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_579_15_chain : (named_envelope_579_15.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_579_15_head : (named_envelope_579_15.map Internal.SnakyRows009.namedCellKey).head? = some (130 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_579_15_last : (named_envelope_579_15.map Internal.SnakyRows009.namedCellKey).getLast? = some (139 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_579_13 : List Cell := Internal.SnakyRows009.named_envelope_579_14 ++ Internal.SnakyRows009.named_envelope_579_15
theorem Internal.SnakyRows009.named_envelope_579_13_chain : (named_envelope_579_13.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_579_14 Internal.SnakyRows009.named_envelope_579_15 (129 : ℤ) (130 : ℤ)
    Internal.SnakyRows009.named_envelope_579_14_chain Internal.SnakyRows009.named_envelope_579_15_chain Internal.SnakyRows009.named_envelope_579_14_last Internal.SnakyRows009.named_envelope_579_15_head (by decide)
theorem Internal.SnakyRows009.named_envelope_579_13_head : (named_envelope_579_13.map Internal.SnakyRows009.namedCellKey).head? = some (5 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_579_14 Internal.SnakyRows009.named_envelope_579_15 (5 : ℤ) Internal.SnakyRows009.named_envelope_579_14_head
theorem Internal.SnakyRows009.named_envelope_579_13_last : (named_envelope_579_13.map Internal.SnakyRows009.namedCellKey).getLast? = some (139 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_579_14 Internal.SnakyRows009.named_envelope_579_15 (139 : ℤ) Internal.SnakyRows009.named_envelope_579_15_last
def Internal.SnakyRows009.named_envelope_579_9 : List Cell := Internal.SnakyRows009.named_envelope_579_10 ++ Internal.SnakyRows009.named_envelope_579_13
theorem Internal.SnakyRows009.named_envelope_579_9_chain : (named_envelope_579_9.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_579_10 Internal.SnakyRows009.named_envelope_579_13 (4 : ℤ) (5 : ℤ)
    Internal.SnakyRows009.named_envelope_579_10_chain Internal.SnakyRows009.named_envelope_579_13_chain Internal.SnakyRows009.named_envelope_579_10_last Internal.SnakyRows009.named_envelope_579_13_head (by decide)
theorem Internal.SnakyRows009.named_envelope_579_9_head : (named_envelope_579_9.map Internal.SnakyRows009.namedCellKey).head? = some (-126 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_579_10 Internal.SnakyRows009.named_envelope_579_13 (-126 : ℤ) Internal.SnakyRows009.named_envelope_579_10_head
theorem Internal.SnakyRows009.named_envelope_579_9_last : (named_envelope_579_9.map Internal.SnakyRows009.namedCellKey).getLast? = some (139 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_579_10 Internal.SnakyRows009.named_envelope_579_13 (139 : ℤ) Internal.SnakyRows009.named_envelope_579_13_last
def Internal.SnakyRows009.named_envelope_579_1 : List Cell := Internal.SnakyRows009.named_envelope_579_2 ++ Internal.SnakyRows009.named_envelope_579_9
theorem Internal.SnakyRows009.named_envelope_579_1_chain : (named_envelope_579_1.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_579_2 Internal.SnakyRows009.named_envelope_579_9 (-127 : ℤ) (-126 : ℤ)
    Internal.SnakyRows009.named_envelope_579_2_chain Internal.SnakyRows009.named_envelope_579_9_chain Internal.SnakyRows009.named_envelope_579_2_last Internal.SnakyRows009.named_envelope_579_9_head (by decide)
theorem Internal.SnakyRows009.named_envelope_579_1_head : (named_envelope_579_1.map Internal.SnakyRows009.namedCellKey).head? = some (-765 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_579_2 Internal.SnakyRows009.named_envelope_579_9 (-765 : ℤ) Internal.SnakyRows009.named_envelope_579_2_head
theorem Internal.SnakyRows009.named_envelope_579_1_last : (named_envelope_579_1.map Internal.SnakyRows009.namedCellKey).getLast? = some (139 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_579_2 Internal.SnakyRows009.named_envelope_579_9 (139 : ℤ) Internal.SnakyRows009.named_envelope_579_9_last
def Internal.SnakyRows009.named_envelope_579_19 : List Cell := ([(2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_579_19_chain : (named_envelope_579_19.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_579_19_head : (named_envelope_579_19.map Internal.SnakyRows009.namedCellKey).head? = some (255 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_579_19_last : (named_envelope_579_19.map Internal.SnakyRows009.namedCellKey).getLast? = some (263 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_579_20 : List Cell := ([(2, 8), (2, 9), (2, 10), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_579_20_chain : (named_envelope_579_20.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_579_20_head : (named_envelope_579_20.map Internal.SnakyRows009.namedCellKey).head? = some (264 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_579_20_last : (named_envelope_579_20.map Internal.SnakyRows009.namedCellKey).getLast? = some (387 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_579_18 : List Cell := Internal.SnakyRows009.named_envelope_579_19 ++ Internal.SnakyRows009.named_envelope_579_20
theorem Internal.SnakyRows009.named_envelope_579_18_chain : (named_envelope_579_18.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_579_19 Internal.SnakyRows009.named_envelope_579_20 (263 : ℤ) (264 : ℤ)
    Internal.SnakyRows009.named_envelope_579_19_chain Internal.SnakyRows009.named_envelope_579_20_chain Internal.SnakyRows009.named_envelope_579_19_last Internal.SnakyRows009.named_envelope_579_20_head (by decide)
theorem Internal.SnakyRows009.named_envelope_579_18_head : (named_envelope_579_18.map Internal.SnakyRows009.namedCellKey).head? = some (255 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_579_19 Internal.SnakyRows009.named_envelope_579_20 (255 : ℤ) Internal.SnakyRows009.named_envelope_579_19_head
theorem Internal.SnakyRows009.named_envelope_579_18_last : (named_envelope_579_18.map Internal.SnakyRows009.namedCellKey).getLast? = some (387 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_579_19 Internal.SnakyRows009.named_envelope_579_20 (387 : ℤ) Internal.SnakyRows009.named_envelope_579_20_last
def Internal.SnakyRows009.named_envelope_579_22 : List Cell := ([(3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, -3), (4, -2)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_579_22_chain : (named_envelope_579_22.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_579_22_head : (named_envelope_579_22.map Internal.SnakyRows009.namedCellKey).head? = some (388 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_579_22_last : (named_envelope_579_22.map Internal.SnakyRows009.namedCellKey).getLast? = some (510 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_579_23 : List Cell := ([(4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_579_23_chain : (named_envelope_579_23.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_579_23_head : (named_envelope_579_23.map Internal.SnakyRows009.namedCellKey).head? = some (511 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_579_23_last : (named_envelope_579_23.map Internal.SnakyRows009.namedCellKey).getLast? = some (520 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_579_21 : List Cell := Internal.SnakyRows009.named_envelope_579_22 ++ Internal.SnakyRows009.named_envelope_579_23
theorem Internal.SnakyRows009.named_envelope_579_21_chain : (named_envelope_579_21.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_579_22 Internal.SnakyRows009.named_envelope_579_23 (510 : ℤ) (511 : ℤ)
    Internal.SnakyRows009.named_envelope_579_22_chain Internal.SnakyRows009.named_envelope_579_23_chain Internal.SnakyRows009.named_envelope_579_22_last Internal.SnakyRows009.named_envelope_579_23_head (by decide)
theorem Internal.SnakyRows009.named_envelope_579_21_head : (named_envelope_579_21.map Internal.SnakyRows009.namedCellKey).head? = some (388 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_579_22 Internal.SnakyRows009.named_envelope_579_23 (388 : ℤ) Internal.SnakyRows009.named_envelope_579_22_head
theorem Internal.SnakyRows009.named_envelope_579_21_last : (named_envelope_579_21.map Internal.SnakyRows009.namedCellKey).getLast? = some (520 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_579_22 Internal.SnakyRows009.named_envelope_579_23 (520 : ℤ) Internal.SnakyRows009.named_envelope_579_23_last
def Internal.SnakyRows009.named_envelope_579_17 : List Cell := Internal.SnakyRows009.named_envelope_579_18 ++ Internal.SnakyRows009.named_envelope_579_21
theorem Internal.SnakyRows009.named_envelope_579_17_chain : (named_envelope_579_17.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_579_18 Internal.SnakyRows009.named_envelope_579_21 (387 : ℤ) (388 : ℤ)
    Internal.SnakyRows009.named_envelope_579_18_chain Internal.SnakyRows009.named_envelope_579_21_chain Internal.SnakyRows009.named_envelope_579_18_last Internal.SnakyRows009.named_envelope_579_21_head (by decide)
theorem Internal.SnakyRows009.named_envelope_579_17_head : (named_envelope_579_17.map Internal.SnakyRows009.namedCellKey).head? = some (255 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_579_18 Internal.SnakyRows009.named_envelope_579_21 (255 : ℤ) Internal.SnakyRows009.named_envelope_579_18_head
theorem Internal.SnakyRows009.named_envelope_579_17_last : (named_envelope_579_17.map Internal.SnakyRows009.namedCellKey).getLast? = some (520 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_579_18 Internal.SnakyRows009.named_envelope_579_21 (520 : ℤ) Internal.SnakyRows009.named_envelope_579_21_last
def Internal.SnakyRows009.named_envelope_579_26 : List Cell := ([(4, 9), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_579_26_chain : (named_envelope_579_26.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_579_26_head : (named_envelope_579_26.map Internal.SnakyRows009.namedCellKey).head? = some (521 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_579_26_last : (named_envelope_579_26.map Internal.SnakyRows009.namedCellKey).getLast? = some (645 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_579_27 : List Cell := ([(5, 6), (5, 7), (5, 8), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_579_27_chain : (named_envelope_579_27.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_579_27_head : (named_envelope_579_27.map Internal.SnakyRows009.namedCellKey).head? = some (646 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_579_27_last : (named_envelope_579_27.map Internal.SnakyRows009.namedCellKey).getLast? = some (770 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_579_25 : List Cell := Internal.SnakyRows009.named_envelope_579_26 ++ Internal.SnakyRows009.named_envelope_579_27
theorem Internal.SnakyRows009.named_envelope_579_25_chain : (named_envelope_579_25.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_579_26 Internal.SnakyRows009.named_envelope_579_27 (645 : ℤ) (646 : ℤ)
    Internal.SnakyRows009.named_envelope_579_26_chain Internal.SnakyRows009.named_envelope_579_27_chain Internal.SnakyRows009.named_envelope_579_26_last Internal.SnakyRows009.named_envelope_579_27_head (by decide)
theorem Internal.SnakyRows009.named_envelope_579_25_head : (named_envelope_579_25.map Internal.SnakyRows009.namedCellKey).head? = some (521 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_579_26 Internal.SnakyRows009.named_envelope_579_27 (521 : ℤ) Internal.SnakyRows009.named_envelope_579_26_head
theorem Internal.SnakyRows009.named_envelope_579_25_last : (named_envelope_579_25.map Internal.SnakyRows009.namedCellKey).getLast? = some (770 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_579_26 Internal.SnakyRows009.named_envelope_579_27 (770 : ℤ) Internal.SnakyRows009.named_envelope_579_27_last
def Internal.SnakyRows009.named_envelope_579_29 : List Cell := ([(6, 3), (6, 4), (6, 5), (6, 6), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_579_29_chain : (named_envelope_579_29.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_579_29_head : (named_envelope_579_29.map Internal.SnakyRows009.namedCellKey).head? = some (771 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_579_29_last : (named_envelope_579_29.map Internal.SnakyRows009.namedCellKey).getLast? = some (899 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_579_30 : List Cell := ([(7, 4), (7, 5), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (9, -1), (9, 1), (9, 3)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_579_30_chain : (named_envelope_579_30.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_579_30_head : (named_envelope_579_30.map Internal.SnakyRows009.namedCellKey).head? = some (900 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_579_30_last : (named_envelope_579_30.map Internal.SnakyRows009.namedCellKey).getLast? = some (1155 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_579_28 : List Cell := Internal.SnakyRows009.named_envelope_579_29 ++ Internal.SnakyRows009.named_envelope_579_30
theorem Internal.SnakyRows009.named_envelope_579_28_chain : (named_envelope_579_28.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_579_29 Internal.SnakyRows009.named_envelope_579_30 (899 : ℤ) (900 : ℤ)
    Internal.SnakyRows009.named_envelope_579_29_chain Internal.SnakyRows009.named_envelope_579_30_chain Internal.SnakyRows009.named_envelope_579_29_last Internal.SnakyRows009.named_envelope_579_30_head (by decide)
theorem Internal.SnakyRows009.named_envelope_579_28_head : (named_envelope_579_28.map Internal.SnakyRows009.namedCellKey).head? = some (771 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_579_29 Internal.SnakyRows009.named_envelope_579_30 (771 : ℤ) Internal.SnakyRows009.named_envelope_579_29_head
theorem Internal.SnakyRows009.named_envelope_579_28_last : (named_envelope_579_28.map Internal.SnakyRows009.namedCellKey).getLast? = some (1155 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_579_29 Internal.SnakyRows009.named_envelope_579_30 (1155 : ℤ) Internal.SnakyRows009.named_envelope_579_30_last
def Internal.SnakyRows009.named_envelope_579_24 : List Cell := Internal.SnakyRows009.named_envelope_579_25 ++ Internal.SnakyRows009.named_envelope_579_28
theorem Internal.SnakyRows009.named_envelope_579_24_chain : (named_envelope_579_24.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_579_25 Internal.SnakyRows009.named_envelope_579_28 (770 : ℤ) (771 : ℤ)
    Internal.SnakyRows009.named_envelope_579_25_chain Internal.SnakyRows009.named_envelope_579_28_chain Internal.SnakyRows009.named_envelope_579_25_last Internal.SnakyRows009.named_envelope_579_28_head (by decide)
theorem Internal.SnakyRows009.named_envelope_579_24_head : (named_envelope_579_24.map Internal.SnakyRows009.namedCellKey).head? = some (521 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_579_25 Internal.SnakyRows009.named_envelope_579_28 (521 : ℤ) Internal.SnakyRows009.named_envelope_579_25_head
theorem Internal.SnakyRows009.named_envelope_579_24_last : (named_envelope_579_24.map Internal.SnakyRows009.namedCellKey).getLast? = some (1155 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_579_25 Internal.SnakyRows009.named_envelope_579_28 (1155 : ℤ) Internal.SnakyRows009.named_envelope_579_28_last
def Internal.SnakyRows009.named_envelope_579_16 : List Cell := Internal.SnakyRows009.named_envelope_579_17 ++ Internal.SnakyRows009.named_envelope_579_24
theorem Internal.SnakyRows009.named_envelope_579_16_chain : (named_envelope_579_16.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_579_17 Internal.SnakyRows009.named_envelope_579_24 (520 : ℤ) (521 : ℤ)
    Internal.SnakyRows009.named_envelope_579_17_chain Internal.SnakyRows009.named_envelope_579_24_chain Internal.SnakyRows009.named_envelope_579_17_last Internal.SnakyRows009.named_envelope_579_24_head (by decide)
theorem Internal.SnakyRows009.named_envelope_579_16_head : (named_envelope_579_16.map Internal.SnakyRows009.namedCellKey).head? = some (255 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_579_17 Internal.SnakyRows009.named_envelope_579_24 (255 : ℤ) Internal.SnakyRows009.named_envelope_579_17_head
theorem Internal.SnakyRows009.named_envelope_579_16_last : (named_envelope_579_16.map Internal.SnakyRows009.namedCellKey).getLast? = some (1155 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_579_17 Internal.SnakyRows009.named_envelope_579_24 (1155 : ℤ) Internal.SnakyRows009.named_envelope_579_24_last
def Internal.SnakyRows009.named_envelope_579_0 : List Cell := Internal.SnakyRows009.named_envelope_579_1 ++ Internal.SnakyRows009.named_envelope_579_16
theorem Internal.SnakyRows009.named_envelope_579_0_chain : (named_envelope_579_0.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_579_1 Internal.SnakyRows009.named_envelope_579_16 (139 : ℤ) (255 : ℤ)
    Internal.SnakyRows009.named_envelope_579_1_chain Internal.SnakyRows009.named_envelope_579_16_chain Internal.SnakyRows009.named_envelope_579_1_last Internal.SnakyRows009.named_envelope_579_16_head (by decide)
theorem Internal.SnakyRows009.named_envelope_579_0_head : (named_envelope_579_0.map Internal.SnakyRows009.namedCellKey).head? = some (-765 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_579_1 Internal.SnakyRows009.named_envelope_579_16 (-765 : ℤ) Internal.SnakyRows009.named_envelope_579_1_head
theorem Internal.SnakyRows009.named_envelope_579_0_last : (named_envelope_579_0.map Internal.SnakyRows009.namedCellKey).getLast? = some (1155 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_579_1 Internal.SnakyRows009.named_envelope_579_16 (1155 : ℤ) Internal.SnakyRows009.named_envelope_579_16_last
theorem Internal.SnakyRows009.named_envelope_579_nodup : (Internal.SnakyRows009.named_envelope_579_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows009.named_nodup_of_chain Internal.SnakyRows009.named_envelope_579_0 Internal.SnakyRows009.named_envelope_579_0_chain
def envelope_579 : Finset Cell := ⟨(Internal.SnakyRows009.named_envelope_579_0 : Multiset Cell), Internal.SnakyRows009.named_envelope_579_nodup⟩
def childrenC_579 : Fin 2 → Finset Cell := ![(placedSet 1 (0, -1) required_2), (placedSet 4 (0, 1) required_576)]
def childrenD_579 : Fin 2 → Finset Cell := ![(placedSet 1 (0, -1) envelope_2), (placedSet 4 (0, 1) envelope_576)]
theorem common_sub_579 : commonEnvelope childrenD_579 ⊆ insert (0, 0) required_579 := by decide
theorem child_required_sub_579 : ∀ j, childrenC_579 j ⊆ insert (0, 0) required_579 := by decide
theorem Internal.SnakyRows009.containment_579_0 :
    placedSet 1 (0, -1) envelope_2 ⊆ envelope_579 := by decide
theorem Internal.SnakyRows009.containment_579_1 :
    placedSet 4 (0, 1) envelope_576 ⊆ envelope_579 := by decide +kernel
theorem child_envelope_sub_579 : ∀ j, childrenD_579 j ⊆ envelope_579 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows009.containment_579_0
  · exact Internal.SnakyRows009.containment_579_1
theorem pivot_mem_579 : (0, 0) ∈ envelope_579 := by decide
theorem children_work_579 : ∀ j, Template HasSnaky 24 (childrenC_579 j) (childrenD_579 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_2 1 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_576 4 (0, 1)).mono (by decide)
theorem row_works_579 : Template HasSnaky 25 required_579 envelope_579 := by
  refine compose HasSnaky 24 childrenC_579 childrenD_579 children_work_579 (0, 0)
    required_579 envelope_579 pivot_mem_579 child_required_sub_579 child_envelope_sub_579 ?_
  intro b hb; exact common_sub_579 (mem_commonEnvelope childrenD_579 b hb)
end SnakyConditional

end OAI
