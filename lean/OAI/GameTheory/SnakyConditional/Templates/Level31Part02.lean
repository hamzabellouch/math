import OAI.GameTheory.SnakyConditional.Templates.Level30Part02
import OAI.GameTheory.SnakyConditional.Templates.Level30Part03

namespace OAI

namespace SnakyConditional
def required_598 : Finset Cell := ⟨(([(-3, -2), (-2, -2), (-2, -1), (0, -1), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows011C.named_envelope_598_4 : List Cell := ([(-6, 7), (-6, 8), (-6, 10), (-5, 5), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8)] : List Cell)
theorem Internal.SnakyRows011C.named_envelope_598_4_chain : (named_envelope_598_4.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_4_head : (named_envelope_598_4.map Internal.SnakyRows011C.namedCellKey).head? = some (-761 : ℤ) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_4_last : (named_envelope_598_4.map Internal.SnakyRows011C.namedCellKey).getLast? = some (-504 : ℤ) := by decide
def Internal.SnakyRows011C.named_envelope_598_5 : List Cell := ([(-4, 9), (-4, 10), (-4, 11), (-4, 12), (-4, 13), (-3, -2), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10)] : List Cell)
theorem Internal.SnakyRows011C.named_envelope_598_5_chain : (named_envelope_598_5.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_5_head : (named_envelope_598_5.map Internal.SnakyRows011C.namedCellKey).head? = some (-503 : ℤ) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_5_last : (named_envelope_598_5.map Internal.SnakyRows011C.namedCellKey).getLast? = some (-374 : ℤ) := by decide
def Internal.SnakyRows011C.named_envelope_598_3 : List Cell := Internal.SnakyRows011C.named_envelope_598_4 ++ Internal.SnakyRows011C.named_envelope_598_5
theorem Internal.SnakyRows011C.named_envelope_598_3_chain : (named_envelope_598_3.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011C.named_chain_append Internal.SnakyRows011C.named_envelope_598_4 Internal.SnakyRows011C.named_envelope_598_5 (-504 : ℤ) (-503 : ℤ)
    Internal.SnakyRows011C.named_envelope_598_4_chain Internal.SnakyRows011C.named_envelope_598_5_chain Internal.SnakyRows011C.named_envelope_598_4_last Internal.SnakyRows011C.named_envelope_598_5_head (by decide)
theorem Internal.SnakyRows011C.named_envelope_598_3_head : (named_envelope_598_3.map Internal.SnakyRows011C.namedCellKey).head? = some (-761 : ℤ) :=
  Internal.SnakyRows011C.named_head_append Internal.SnakyRows011C.named_envelope_598_4 Internal.SnakyRows011C.named_envelope_598_5 (-761 : ℤ) Internal.SnakyRows011C.named_envelope_598_4_head
theorem Internal.SnakyRows011C.named_envelope_598_3_last : (named_envelope_598_3.map Internal.SnakyRows011C.namedCellKey).getLast? = some (-374 : ℤ) :=
  Internal.SnakyRows011C.named_last_append Internal.SnakyRows011C.named_envelope_598_4 Internal.SnakyRows011C.named_envelope_598_5 (-374 : ℤ) Internal.SnakyRows011C.named_envelope_598_5_last
def Internal.SnakyRows011C.named_envelope_598_7 : List Cell := ([(-3, 11), (-3, 12), (-2, -2), (-2, -1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11)] : List Cell)
theorem Internal.SnakyRows011C.named_envelope_598_7_chain : (named_envelope_598_7.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_7_head : (named_envelope_598_7.map Internal.SnakyRows011C.namedCellKey).head? = some (-373 : ℤ) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_7_last : (named_envelope_598_7.map Internal.SnakyRows011C.namedCellKey).getLast? = some (-245 : ℤ) := by decide
def Internal.SnakyRows011C.named_envelope_598_8 : List Cell := ([(-2, 12), (-2, 13), (-2, 14), (-2, 15), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7)] : List Cell)
theorem Internal.SnakyRows011C.named_envelope_598_8_chain : (named_envelope_598_8.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_8_head : (named_envelope_598_8.map Internal.SnakyRows011C.namedCellKey).head? = some (-244 : ℤ) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_8_last : (named_envelope_598_8.map Internal.SnakyRows011C.namedCellKey).getLast? = some (-121 : ℤ) := by decide
def Internal.SnakyRows011C.named_envelope_598_6 : List Cell := Internal.SnakyRows011C.named_envelope_598_7 ++ Internal.SnakyRows011C.named_envelope_598_8
theorem Internal.SnakyRows011C.named_envelope_598_6_chain : (named_envelope_598_6.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011C.named_chain_append Internal.SnakyRows011C.named_envelope_598_7 Internal.SnakyRows011C.named_envelope_598_8 (-245 : ℤ) (-244 : ℤ)
    Internal.SnakyRows011C.named_envelope_598_7_chain Internal.SnakyRows011C.named_envelope_598_8_chain Internal.SnakyRows011C.named_envelope_598_7_last Internal.SnakyRows011C.named_envelope_598_8_head (by decide)
theorem Internal.SnakyRows011C.named_envelope_598_6_head : (named_envelope_598_6.map Internal.SnakyRows011C.namedCellKey).head? = some (-373 : ℤ) :=
  Internal.SnakyRows011C.named_head_append Internal.SnakyRows011C.named_envelope_598_7 Internal.SnakyRows011C.named_envelope_598_8 (-373 : ℤ) Internal.SnakyRows011C.named_envelope_598_7_head
theorem Internal.SnakyRows011C.named_envelope_598_6_last : (named_envelope_598_6.map Internal.SnakyRows011C.namedCellKey).getLast? = some (-121 : ℤ) :=
  Internal.SnakyRows011C.named_last_append Internal.SnakyRows011C.named_envelope_598_7 Internal.SnakyRows011C.named_envelope_598_8 (-121 : ℤ) Internal.SnakyRows011C.named_envelope_598_8_last
def Internal.SnakyRows011C.named_envelope_598_2 : List Cell := Internal.SnakyRows011C.named_envelope_598_3 ++ Internal.SnakyRows011C.named_envelope_598_6
theorem Internal.SnakyRows011C.named_envelope_598_2_chain : (named_envelope_598_2.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011C.named_chain_append Internal.SnakyRows011C.named_envelope_598_3 Internal.SnakyRows011C.named_envelope_598_6 (-374 : ℤ) (-373 : ℤ)
    Internal.SnakyRows011C.named_envelope_598_3_chain Internal.SnakyRows011C.named_envelope_598_6_chain Internal.SnakyRows011C.named_envelope_598_3_last Internal.SnakyRows011C.named_envelope_598_6_head (by decide)
theorem Internal.SnakyRows011C.named_envelope_598_2_head : (named_envelope_598_2.map Internal.SnakyRows011C.namedCellKey).head? = some (-761 : ℤ) :=
  Internal.SnakyRows011C.named_head_append Internal.SnakyRows011C.named_envelope_598_3 Internal.SnakyRows011C.named_envelope_598_6 (-761 : ℤ) Internal.SnakyRows011C.named_envelope_598_3_head
theorem Internal.SnakyRows011C.named_envelope_598_2_last : (named_envelope_598_2.map Internal.SnakyRows011C.namedCellKey).getLast? = some (-121 : ℤ) :=
  Internal.SnakyRows011C.named_last_append Internal.SnakyRows011C.named_envelope_598_3 Internal.SnakyRows011C.named_envelope_598_6 (-121 : ℤ) Internal.SnakyRows011C.named_envelope_598_6_last
def Internal.SnakyRows011C.named_envelope_598_11 : List Cell := ([(-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (-1, 14), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3)] : List Cell)
theorem Internal.SnakyRows011C.named_envelope_598_11_chain : (named_envelope_598_11.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_11_head : (named_envelope_598_11.map Internal.SnakyRows011C.namedCellKey).head? = some (-120 : ℤ) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_11_last : (named_envelope_598_11.map Internal.SnakyRows011C.namedCellKey).getLast? = some (3 : ℤ) := by decide
def Internal.SnakyRows011C.named_envelope_598_12 : List Cell := ([(0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (1, -4), (1, -3), (1, -2)] : List Cell)
theorem Internal.SnakyRows011C.named_envelope_598_12_chain : (named_envelope_598_12.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_12_head : (named_envelope_598_12.map Internal.SnakyRows011C.namedCellKey).head? = some (4 : ℤ) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_12_last : (named_envelope_598_12.map Internal.SnakyRows011C.namedCellKey).getLast? = some (126 : ℤ) := by decide
def Internal.SnakyRows011C.named_envelope_598_10 : List Cell := Internal.SnakyRows011C.named_envelope_598_11 ++ Internal.SnakyRows011C.named_envelope_598_12
theorem Internal.SnakyRows011C.named_envelope_598_10_chain : (named_envelope_598_10.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011C.named_chain_append Internal.SnakyRows011C.named_envelope_598_11 Internal.SnakyRows011C.named_envelope_598_12 (3 : ℤ) (4 : ℤ)
    Internal.SnakyRows011C.named_envelope_598_11_chain Internal.SnakyRows011C.named_envelope_598_12_chain Internal.SnakyRows011C.named_envelope_598_11_last Internal.SnakyRows011C.named_envelope_598_12_head (by decide)
theorem Internal.SnakyRows011C.named_envelope_598_10_head : (named_envelope_598_10.map Internal.SnakyRows011C.namedCellKey).head? = some (-120 : ℤ) :=
  Internal.SnakyRows011C.named_head_append Internal.SnakyRows011C.named_envelope_598_11 Internal.SnakyRows011C.named_envelope_598_12 (-120 : ℤ) Internal.SnakyRows011C.named_envelope_598_11_head
theorem Internal.SnakyRows011C.named_envelope_598_10_last : (named_envelope_598_10.map Internal.SnakyRows011C.namedCellKey).getLast? = some (126 : ℤ) :=
  Internal.SnakyRows011C.named_last_append Internal.SnakyRows011C.named_envelope_598_11 Internal.SnakyRows011C.named_envelope_598_12 (126 : ℤ) Internal.SnakyRows011C.named_envelope_598_12_last
def Internal.SnakyRows011C.named_envelope_598_14 : List Cell := ([(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13)] : List Cell)
theorem Internal.SnakyRows011C.named_envelope_598_14_chain : (named_envelope_598_14.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_14_head : (named_envelope_598_14.map Internal.SnakyRows011C.namedCellKey).head? = some (128 : ℤ) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_14_last : (named_envelope_598_14.map Internal.SnakyRows011C.namedCellKey).getLast? = some (141 : ℤ) := by decide
def Internal.SnakyRows011C.named_envelope_598_15 : List Cell := ([(2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9)] : List Cell)
theorem Internal.SnakyRows011C.named_envelope_598_15_chain : (named_envelope_598_15.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_15_head : (named_envelope_598_15.map Internal.SnakyRows011C.namedCellKey).head? = some (251 : ℤ) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_15_last : (named_envelope_598_15.map Internal.SnakyRows011C.namedCellKey).getLast? = some (265 : ℤ) := by decide
def Internal.SnakyRows011C.named_envelope_598_13 : List Cell := Internal.SnakyRows011C.named_envelope_598_14 ++ Internal.SnakyRows011C.named_envelope_598_15
theorem Internal.SnakyRows011C.named_envelope_598_13_chain : (named_envelope_598_13.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011C.named_chain_append Internal.SnakyRows011C.named_envelope_598_14 Internal.SnakyRows011C.named_envelope_598_15 (141 : ℤ) (251 : ℤ)
    Internal.SnakyRows011C.named_envelope_598_14_chain Internal.SnakyRows011C.named_envelope_598_15_chain Internal.SnakyRows011C.named_envelope_598_14_last Internal.SnakyRows011C.named_envelope_598_15_head (by decide)
theorem Internal.SnakyRows011C.named_envelope_598_13_head : (named_envelope_598_13.map Internal.SnakyRows011C.namedCellKey).head? = some (128 : ℤ) :=
  Internal.SnakyRows011C.named_head_append Internal.SnakyRows011C.named_envelope_598_14 Internal.SnakyRows011C.named_envelope_598_15 (128 : ℤ) Internal.SnakyRows011C.named_envelope_598_14_head
theorem Internal.SnakyRows011C.named_envelope_598_13_last : (named_envelope_598_13.map Internal.SnakyRows011C.namedCellKey).getLast? = some (265 : ℤ) :=
  Internal.SnakyRows011C.named_last_append Internal.SnakyRows011C.named_envelope_598_14 Internal.SnakyRows011C.named_envelope_598_15 (265 : ℤ) Internal.SnakyRows011C.named_envelope_598_15_last
def Internal.SnakyRows011C.named_envelope_598_9 : List Cell := Internal.SnakyRows011C.named_envelope_598_10 ++ Internal.SnakyRows011C.named_envelope_598_13
theorem Internal.SnakyRows011C.named_envelope_598_9_chain : (named_envelope_598_9.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011C.named_chain_append Internal.SnakyRows011C.named_envelope_598_10 Internal.SnakyRows011C.named_envelope_598_13 (126 : ℤ) (128 : ℤ)
    Internal.SnakyRows011C.named_envelope_598_10_chain Internal.SnakyRows011C.named_envelope_598_13_chain Internal.SnakyRows011C.named_envelope_598_10_last Internal.SnakyRows011C.named_envelope_598_13_head (by decide)
theorem Internal.SnakyRows011C.named_envelope_598_9_head : (named_envelope_598_9.map Internal.SnakyRows011C.namedCellKey).head? = some (-120 : ℤ) :=
  Internal.SnakyRows011C.named_head_append Internal.SnakyRows011C.named_envelope_598_10 Internal.SnakyRows011C.named_envelope_598_13 (-120 : ℤ) Internal.SnakyRows011C.named_envelope_598_10_head
theorem Internal.SnakyRows011C.named_envelope_598_9_last : (named_envelope_598_9.map Internal.SnakyRows011C.namedCellKey).getLast? = some (265 : ℤ) :=
  Internal.SnakyRows011C.named_last_append Internal.SnakyRows011C.named_envelope_598_10 Internal.SnakyRows011C.named_envelope_598_13 (265 : ℤ) Internal.SnakyRows011C.named_envelope_598_13_last
def Internal.SnakyRows011C.named_envelope_598_1 : List Cell := Internal.SnakyRows011C.named_envelope_598_2 ++ Internal.SnakyRows011C.named_envelope_598_9
theorem Internal.SnakyRows011C.named_envelope_598_1_chain : (named_envelope_598_1.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011C.named_chain_append Internal.SnakyRows011C.named_envelope_598_2 Internal.SnakyRows011C.named_envelope_598_9 (-121 : ℤ) (-120 : ℤ)
    Internal.SnakyRows011C.named_envelope_598_2_chain Internal.SnakyRows011C.named_envelope_598_9_chain Internal.SnakyRows011C.named_envelope_598_2_last Internal.SnakyRows011C.named_envelope_598_9_head (by decide)
theorem Internal.SnakyRows011C.named_envelope_598_1_head : (named_envelope_598_1.map Internal.SnakyRows011C.namedCellKey).head? = some (-761 : ℤ) :=
  Internal.SnakyRows011C.named_head_append Internal.SnakyRows011C.named_envelope_598_2 Internal.SnakyRows011C.named_envelope_598_9 (-761 : ℤ) Internal.SnakyRows011C.named_envelope_598_2_head
theorem Internal.SnakyRows011C.named_envelope_598_1_last : (named_envelope_598_1.map Internal.SnakyRows011C.namedCellKey).getLast? = some (265 : ℤ) :=
  Internal.SnakyRows011C.named_last_append Internal.SnakyRows011C.named_envelope_598_2 Internal.SnakyRows011C.named_envelope_598_9 (265 : ℤ) Internal.SnakyRows011C.named_envelope_598_9_last
def Internal.SnakyRows011C.named_envelope_598_19 : List Cell := ([(2, 10), (2, 11), (2, 12), (2, 13), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5)] : List Cell)
theorem Internal.SnakyRows011C.named_envelope_598_19_chain : (named_envelope_598_19.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_19_head : (named_envelope_598_19.map Internal.SnakyRows011C.namedCellKey).head? = some (266 : ℤ) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_19_last : (named_envelope_598_19.map Internal.SnakyRows011C.namedCellKey).getLast? = some (389 : ℤ) := by decide
def Internal.SnakyRows011C.named_envelope_598_20 : List Cell := ([(3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1)] : List Cell)
theorem Internal.SnakyRows011C.named_envelope_598_20_chain : (named_envelope_598_20.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_20_head : (named_envelope_598_20.map Internal.SnakyRows011C.namedCellKey).head? = some (390 : ℤ) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_20_last : (named_envelope_598_20.map Internal.SnakyRows011C.namedCellKey).getLast? = some (513 : ℤ) := by decide
def Internal.SnakyRows011C.named_envelope_598_18 : List Cell := Internal.SnakyRows011C.named_envelope_598_19 ++ Internal.SnakyRows011C.named_envelope_598_20
theorem Internal.SnakyRows011C.named_envelope_598_18_chain : (named_envelope_598_18.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011C.named_chain_append Internal.SnakyRows011C.named_envelope_598_19 Internal.SnakyRows011C.named_envelope_598_20 (389 : ℤ) (390 : ℤ)
    Internal.SnakyRows011C.named_envelope_598_19_chain Internal.SnakyRows011C.named_envelope_598_20_chain Internal.SnakyRows011C.named_envelope_598_19_last Internal.SnakyRows011C.named_envelope_598_20_head (by decide)
theorem Internal.SnakyRows011C.named_envelope_598_18_head : (named_envelope_598_18.map Internal.SnakyRows011C.namedCellKey).head? = some (266 : ℤ) :=
  Internal.SnakyRows011C.named_head_append Internal.SnakyRows011C.named_envelope_598_19 Internal.SnakyRows011C.named_envelope_598_20 (266 : ℤ) Internal.SnakyRows011C.named_envelope_598_19_head
theorem Internal.SnakyRows011C.named_envelope_598_18_last : (named_envelope_598_18.map Internal.SnakyRows011C.namedCellKey).getLast? = some (513 : ℤ) :=
  Internal.SnakyRows011C.named_last_append Internal.SnakyRows011C.named_envelope_598_19 Internal.SnakyRows011C.named_envelope_598_20 (513 : ℤ) Internal.SnakyRows011C.named_envelope_598_20_last
def Internal.SnakyRows011C.named_envelope_598_22 : List Cell := ([(4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (5, -3), (5, -2)] : List Cell)
theorem Internal.SnakyRows011C.named_envelope_598_22_chain : (named_envelope_598_22.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_22_head : (named_envelope_598_22.map Internal.SnakyRows011C.namedCellKey).head? = some (514 : ℤ) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_22_last : (named_envelope_598_22.map Internal.SnakyRows011C.namedCellKey).getLast? = some (638 : ℤ) := by decide
def Internal.SnakyRows011C.named_envelope_598_23 : List Cell := ([(5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, -3), (6, -2)] : List Cell)
theorem Internal.SnakyRows011C.named_envelope_598_23_chain : (named_envelope_598_23.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_23_head : (named_envelope_598_23.map Internal.SnakyRows011C.namedCellKey).head? = some (639 : ℤ) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_23_last : (named_envelope_598_23.map Internal.SnakyRows011C.namedCellKey).getLast? = some (766 : ℤ) := by decide
def Internal.SnakyRows011C.named_envelope_598_21 : List Cell := Internal.SnakyRows011C.named_envelope_598_22 ++ Internal.SnakyRows011C.named_envelope_598_23
theorem Internal.SnakyRows011C.named_envelope_598_21_chain : (named_envelope_598_21.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011C.named_chain_append Internal.SnakyRows011C.named_envelope_598_22 Internal.SnakyRows011C.named_envelope_598_23 (638 : ℤ) (639 : ℤ)
    Internal.SnakyRows011C.named_envelope_598_22_chain Internal.SnakyRows011C.named_envelope_598_23_chain Internal.SnakyRows011C.named_envelope_598_22_last Internal.SnakyRows011C.named_envelope_598_23_head (by decide)
theorem Internal.SnakyRows011C.named_envelope_598_21_head : (named_envelope_598_21.map Internal.SnakyRows011C.namedCellKey).head? = some (514 : ℤ) :=
  Internal.SnakyRows011C.named_head_append Internal.SnakyRows011C.named_envelope_598_22 Internal.SnakyRows011C.named_envelope_598_23 (514 : ℤ) Internal.SnakyRows011C.named_envelope_598_22_head
theorem Internal.SnakyRows011C.named_envelope_598_21_last : (named_envelope_598_21.map Internal.SnakyRows011C.namedCellKey).getLast? = some (766 : ℤ) :=
  Internal.SnakyRows011C.named_last_append Internal.SnakyRows011C.named_envelope_598_22 Internal.SnakyRows011C.named_envelope_598_23 (766 : ℤ) Internal.SnakyRows011C.named_envelope_598_23_last
def Internal.SnakyRows011C.named_envelope_598_17 : List Cell := Internal.SnakyRows011C.named_envelope_598_18 ++ Internal.SnakyRows011C.named_envelope_598_21
theorem Internal.SnakyRows011C.named_envelope_598_17_chain : (named_envelope_598_17.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011C.named_chain_append Internal.SnakyRows011C.named_envelope_598_18 Internal.SnakyRows011C.named_envelope_598_21 (513 : ℤ) (514 : ℤ)
    Internal.SnakyRows011C.named_envelope_598_18_chain Internal.SnakyRows011C.named_envelope_598_21_chain Internal.SnakyRows011C.named_envelope_598_18_last Internal.SnakyRows011C.named_envelope_598_21_head (by decide)
theorem Internal.SnakyRows011C.named_envelope_598_17_head : (named_envelope_598_17.map Internal.SnakyRows011C.namedCellKey).head? = some (266 : ℤ) :=
  Internal.SnakyRows011C.named_head_append Internal.SnakyRows011C.named_envelope_598_18 Internal.SnakyRows011C.named_envelope_598_21 (266 : ℤ) Internal.SnakyRows011C.named_envelope_598_18_head
theorem Internal.SnakyRows011C.named_envelope_598_17_last : (named_envelope_598_17.map Internal.SnakyRows011C.namedCellKey).getLast? = some (766 : ℤ) :=
  Internal.SnakyRows011C.named_last_append Internal.SnakyRows011C.named_envelope_598_18 Internal.SnakyRows011C.named_envelope_598_21 (766 : ℤ) Internal.SnakyRows011C.named_envelope_598_21_last
def Internal.SnakyRows011C.named_envelope_598_26 : List Cell := ([(6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -3), (7, -2)] : List Cell)
theorem Internal.SnakyRows011C.named_envelope_598_26_chain : (named_envelope_598_26.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_26_head : (named_envelope_598_26.map Internal.SnakyRows011C.namedCellKey).head? = some (767 : ℤ) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_26_last : (named_envelope_598_26.map Internal.SnakyRows011C.namedCellKey).getLast? = some (894 : ℤ) := by decide
def Internal.SnakyRows011C.named_envelope_598_27 : List Cell := ([(7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -1), (8, 0), (8, 1)] : List Cell)
theorem Internal.SnakyRows011C.named_envelope_598_27_chain : (named_envelope_598_27.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_27_head : (named_envelope_598_27.map Internal.SnakyRows011C.namedCellKey).head? = some (895 : ℤ) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_27_last : (named_envelope_598_27.map Internal.SnakyRows011C.namedCellKey).getLast? = some (1025 : ℤ) := by decide
def Internal.SnakyRows011C.named_envelope_598_25 : List Cell := Internal.SnakyRows011C.named_envelope_598_26 ++ Internal.SnakyRows011C.named_envelope_598_27
theorem Internal.SnakyRows011C.named_envelope_598_25_chain : (named_envelope_598_25.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011C.named_chain_append Internal.SnakyRows011C.named_envelope_598_26 Internal.SnakyRows011C.named_envelope_598_27 (894 : ℤ) (895 : ℤ)
    Internal.SnakyRows011C.named_envelope_598_26_chain Internal.SnakyRows011C.named_envelope_598_27_chain Internal.SnakyRows011C.named_envelope_598_26_last Internal.SnakyRows011C.named_envelope_598_27_head (by decide)
theorem Internal.SnakyRows011C.named_envelope_598_25_head : (named_envelope_598_25.map Internal.SnakyRows011C.namedCellKey).head? = some (767 : ℤ) :=
  Internal.SnakyRows011C.named_head_append Internal.SnakyRows011C.named_envelope_598_26 Internal.SnakyRows011C.named_envelope_598_27 (767 : ℤ) Internal.SnakyRows011C.named_envelope_598_26_head
theorem Internal.SnakyRows011C.named_envelope_598_25_last : (named_envelope_598_25.map Internal.SnakyRows011C.namedCellKey).getLast? = some (1025 : ℤ) :=
  Internal.SnakyRows011C.named_last_append Internal.SnakyRows011C.named_envelope_598_26 Internal.SnakyRows011C.named_envelope_598_27 (1025 : ℤ) Internal.SnakyRows011C.named_envelope_598_27_last
def Internal.SnakyRows011C.named_envelope_598_29 : List Cell := ([(8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, -1), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5)] : List Cell)
theorem Internal.SnakyRows011C.named_envelope_598_29_chain : (named_envelope_598_29.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_29_head : (named_envelope_598_29.map Internal.SnakyRows011C.namedCellKey).head? = some (1026 : ℤ) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_29_last : (named_envelope_598_29.map Internal.SnakyRows011C.namedCellKey).getLast? = some (1157 : ℤ) := by decide
def Internal.SnakyRows011C.named_envelope_598_30 : List Cell := ([(9, 6), (9, 7), (9, 8), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (11, 2), (11, 3), (11, 4), (12, 2), (12, 4)] : List Cell)
theorem Internal.SnakyRows011C.named_envelope_598_30_chain : (named_envelope_598_30.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_30_head : (named_envelope_598_30.map Internal.SnakyRows011C.namedCellKey).head? = some (1158 : ℤ) := by decide
theorem Internal.SnakyRows011C.named_envelope_598_30_last : (named_envelope_598_30.map Internal.SnakyRows011C.namedCellKey).getLast? = some (1540 : ℤ) := by decide
def Internal.SnakyRows011C.named_envelope_598_28 : List Cell := Internal.SnakyRows011C.named_envelope_598_29 ++ Internal.SnakyRows011C.named_envelope_598_30
theorem Internal.SnakyRows011C.named_envelope_598_28_chain : (named_envelope_598_28.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011C.named_chain_append Internal.SnakyRows011C.named_envelope_598_29 Internal.SnakyRows011C.named_envelope_598_30 (1157 : ℤ) (1158 : ℤ)
    Internal.SnakyRows011C.named_envelope_598_29_chain Internal.SnakyRows011C.named_envelope_598_30_chain Internal.SnakyRows011C.named_envelope_598_29_last Internal.SnakyRows011C.named_envelope_598_30_head (by decide)
theorem Internal.SnakyRows011C.named_envelope_598_28_head : (named_envelope_598_28.map Internal.SnakyRows011C.namedCellKey).head? = some (1026 : ℤ) :=
  Internal.SnakyRows011C.named_head_append Internal.SnakyRows011C.named_envelope_598_29 Internal.SnakyRows011C.named_envelope_598_30 (1026 : ℤ) Internal.SnakyRows011C.named_envelope_598_29_head
theorem Internal.SnakyRows011C.named_envelope_598_28_last : (named_envelope_598_28.map Internal.SnakyRows011C.namedCellKey).getLast? = some (1540 : ℤ) :=
  Internal.SnakyRows011C.named_last_append Internal.SnakyRows011C.named_envelope_598_29 Internal.SnakyRows011C.named_envelope_598_30 (1540 : ℤ) Internal.SnakyRows011C.named_envelope_598_30_last
def Internal.SnakyRows011C.named_envelope_598_24 : List Cell := Internal.SnakyRows011C.named_envelope_598_25 ++ Internal.SnakyRows011C.named_envelope_598_28
theorem Internal.SnakyRows011C.named_envelope_598_24_chain : (named_envelope_598_24.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011C.named_chain_append Internal.SnakyRows011C.named_envelope_598_25 Internal.SnakyRows011C.named_envelope_598_28 (1025 : ℤ) (1026 : ℤ)
    Internal.SnakyRows011C.named_envelope_598_25_chain Internal.SnakyRows011C.named_envelope_598_28_chain Internal.SnakyRows011C.named_envelope_598_25_last Internal.SnakyRows011C.named_envelope_598_28_head (by decide)
theorem Internal.SnakyRows011C.named_envelope_598_24_head : (named_envelope_598_24.map Internal.SnakyRows011C.namedCellKey).head? = some (767 : ℤ) :=
  Internal.SnakyRows011C.named_head_append Internal.SnakyRows011C.named_envelope_598_25 Internal.SnakyRows011C.named_envelope_598_28 (767 : ℤ) Internal.SnakyRows011C.named_envelope_598_25_head
theorem Internal.SnakyRows011C.named_envelope_598_24_last : (named_envelope_598_24.map Internal.SnakyRows011C.namedCellKey).getLast? = some (1540 : ℤ) :=
  Internal.SnakyRows011C.named_last_append Internal.SnakyRows011C.named_envelope_598_25 Internal.SnakyRows011C.named_envelope_598_28 (1540 : ℤ) Internal.SnakyRows011C.named_envelope_598_28_last
def Internal.SnakyRows011C.named_envelope_598_16 : List Cell := Internal.SnakyRows011C.named_envelope_598_17 ++ Internal.SnakyRows011C.named_envelope_598_24
theorem Internal.SnakyRows011C.named_envelope_598_16_chain : (named_envelope_598_16.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011C.named_chain_append Internal.SnakyRows011C.named_envelope_598_17 Internal.SnakyRows011C.named_envelope_598_24 (766 : ℤ) (767 : ℤ)
    Internal.SnakyRows011C.named_envelope_598_17_chain Internal.SnakyRows011C.named_envelope_598_24_chain Internal.SnakyRows011C.named_envelope_598_17_last Internal.SnakyRows011C.named_envelope_598_24_head (by decide)
theorem Internal.SnakyRows011C.named_envelope_598_16_head : (named_envelope_598_16.map Internal.SnakyRows011C.namedCellKey).head? = some (266 : ℤ) :=
  Internal.SnakyRows011C.named_head_append Internal.SnakyRows011C.named_envelope_598_17 Internal.SnakyRows011C.named_envelope_598_24 (266 : ℤ) Internal.SnakyRows011C.named_envelope_598_17_head
theorem Internal.SnakyRows011C.named_envelope_598_16_last : (named_envelope_598_16.map Internal.SnakyRows011C.namedCellKey).getLast? = some (1540 : ℤ) :=
  Internal.SnakyRows011C.named_last_append Internal.SnakyRows011C.named_envelope_598_17 Internal.SnakyRows011C.named_envelope_598_24 (1540 : ℤ) Internal.SnakyRows011C.named_envelope_598_24_last
def Internal.SnakyRows011C.named_envelope_598_0 : List Cell := Internal.SnakyRows011C.named_envelope_598_1 ++ Internal.SnakyRows011C.named_envelope_598_16
theorem Internal.SnakyRows011C.named_envelope_598_0_chain : (named_envelope_598_0.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011C.named_chain_append Internal.SnakyRows011C.named_envelope_598_1 Internal.SnakyRows011C.named_envelope_598_16 (265 : ℤ) (266 : ℤ)
    Internal.SnakyRows011C.named_envelope_598_1_chain Internal.SnakyRows011C.named_envelope_598_16_chain Internal.SnakyRows011C.named_envelope_598_1_last Internal.SnakyRows011C.named_envelope_598_16_head (by decide)
theorem Internal.SnakyRows011C.named_envelope_598_0_head : (named_envelope_598_0.map Internal.SnakyRows011C.namedCellKey).head? = some (-761 : ℤ) :=
  Internal.SnakyRows011C.named_head_append Internal.SnakyRows011C.named_envelope_598_1 Internal.SnakyRows011C.named_envelope_598_16 (-761 : ℤ) Internal.SnakyRows011C.named_envelope_598_1_head
theorem Internal.SnakyRows011C.named_envelope_598_0_last : (named_envelope_598_0.map Internal.SnakyRows011C.namedCellKey).getLast? = some (1540 : ℤ) :=
  Internal.SnakyRows011C.named_last_append Internal.SnakyRows011C.named_envelope_598_1 Internal.SnakyRows011C.named_envelope_598_16 (1540 : ℤ) Internal.SnakyRows011C.named_envelope_598_16_last
theorem Internal.SnakyRows011C.named_envelope_598_nodup : (Internal.SnakyRows011C.named_envelope_598_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows011C.named_nodup_of_chain Internal.SnakyRows011C.named_envelope_598_0 Internal.SnakyRows011C.named_envelope_598_0_chain
def envelope_598 : Finset Cell := ⟨(Internal.SnakyRows011C.named_envelope_598_0 : Multiset Cell), Internal.SnakyRows011C.named_envelope_598_nodup⟩
def childrenC_598 : Fin 5 → Finset Cell := ![(placedSet 0 (1, 2) required_594), (placedSet 5 (0, -2) required_456), (placedSet 1 (-1, -2) required_254), (placedSet 1 (-1, -2) required_554), (placedSet 0 (0, 2) required_465)]
def childrenD_598 : Fin 5 → Finset Cell := ![(placedSet 0 (1, 2) envelope_594), (placedSet 5 (0, -2) envelope_456), (placedSet 1 (-1, -2) envelope_254), (placedSet 1 (-1, -2) envelope_554), (placedSet 0 (0, 2) envelope_465)]
theorem common_sub_598 : commonEnvelope childrenD_598 ⊆ insert (0, 0) required_598 := by decide
theorem child_required_sub_598 : ∀ j, childrenC_598 j ⊆ insert (0, 0) required_598 := by decide
theorem Internal.SnakyRows011C.containment_598_0 :
    placedSet 0 (1, 2) envelope_594 ⊆ envelope_598 := by decide +kernel
theorem Internal.SnakyRows011C.containment_598_1 :
    placedSet 5 (0, -2) envelope_456 ⊆ envelope_598 := by decide
theorem Internal.SnakyRows011C.containment_598_2 :
    placedSet 1 (-1, -2) envelope_254 ⊆ envelope_598 := by decide
theorem Internal.SnakyRows011C.containment_598_3 :
    placedSet 1 (-1, -2) envelope_554 ⊆ envelope_598 := by decide +kernel
theorem Internal.SnakyRows011C.containment_598_4 :
    placedSet 0 (0, 2) envelope_465 ⊆ envelope_598 := by decide
theorem child_envelope_sub_598 : ∀ j, childrenD_598 j ⊆ envelope_598 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows011C.containment_598_0
  · exact Internal.SnakyRows011C.containment_598_1
  · exact Internal.SnakyRows011C.containment_598_2
  · exact Internal.SnakyRows011C.containment_598_3
  · exact Internal.SnakyRows011C.containment_598_4
theorem pivot_mem_598 : (0, 0) ∈ envelope_598 := by decide
theorem children_work_598 : ∀ j, Template HasSnaky 28 (childrenC_598 j) (childrenD_598 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_594 0 (1, 2)).mono (by decide)
  · exact (placed_template_map row_works_456 5 (0, -2)).mono (by decide)
  · exact (placed_template_map row_works_254 1 (-1, -2)).mono (by decide)
  · exact (placed_template_map row_works_554 1 (-1, -2)).mono (by decide)
  · exact (placed_template_map row_works_465 0 (0, 2)).mono (by decide)
theorem row_works_598 : Template HasSnaky 29 required_598 envelope_598 := by
  refine compose HasSnaky 28 childrenC_598 childrenD_598 children_work_598 (0, 0)
    required_598 envelope_598 pivot_mem_598 child_required_sub_598 child_envelope_sub_598 ?_
  intro b hb; exact common_sub_598 (mem_commonEnvelope childrenD_598 b hb)
def required_600 : Finset Cell := ⟨(([(-2, 0), (-1, 0), (-1, 1)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows011E.named_envelope_600_4 : List Cell := ([(-5, -1), (-5, 1), (-5, 2), (-5, 4), (-4, -5), (-4, -3), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -5), (-3, -4), (-3, -3), (-3, -2)] : List Cell)
theorem Internal.SnakyRows011E.named_envelope_600_4_chain : (named_envelope_600_4.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_4_head : (named_envelope_600_4.map Internal.SnakyRows011E.namedCellKey).head? = some (-641 : ℤ) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_4_last : (named_envelope_600_4.map Internal.SnakyRows011E.namedCellKey).getLast? = some (-386 : ℤ) := by decide
def Internal.SnakyRows011E.named_envelope_600_5 : List Cell := ([(-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-2, -8), (-2, -7), (-2, -6), (-2, -5), (-2, -4)] : List Cell)
theorem Internal.SnakyRows011E.named_envelope_600_5_chain : (named_envelope_600_5.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_5_head : (named_envelope_600_5.map Internal.SnakyRows011E.namedCellKey).head? = some (-385 : ℤ) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_5_last : (named_envelope_600_5.map Internal.SnakyRows011E.namedCellKey).getLast? = some (-260 : ℤ) := by decide
def Internal.SnakyRows011E.named_envelope_600_3 : List Cell := Internal.SnakyRows011E.named_envelope_600_4 ++ Internal.SnakyRows011E.named_envelope_600_5
theorem Internal.SnakyRows011E.named_envelope_600_3_chain : (named_envelope_600_3.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011E.named_chain_append Internal.SnakyRows011E.named_envelope_600_4 Internal.SnakyRows011E.named_envelope_600_5 (-386 : ℤ) (-385 : ℤ)
    Internal.SnakyRows011E.named_envelope_600_4_chain Internal.SnakyRows011E.named_envelope_600_5_chain Internal.SnakyRows011E.named_envelope_600_4_last Internal.SnakyRows011E.named_envelope_600_5_head (by decide)
theorem Internal.SnakyRows011E.named_envelope_600_3_head : (named_envelope_600_3.map Internal.SnakyRows011E.namedCellKey).head? = some (-641 : ℤ) :=
  Internal.SnakyRows011E.named_head_append Internal.SnakyRows011E.named_envelope_600_4 Internal.SnakyRows011E.named_envelope_600_5 (-641 : ℤ) Internal.SnakyRows011E.named_envelope_600_4_head
theorem Internal.SnakyRows011E.named_envelope_600_3_last : (named_envelope_600_3.map Internal.SnakyRows011E.namedCellKey).getLast? = some (-260 : ℤ) :=
  Internal.SnakyRows011E.named_last_append Internal.SnakyRows011E.named_envelope_600_4 Internal.SnakyRows011E.named_envelope_600_5 (-260 : ℤ) Internal.SnakyRows011E.named_envelope_600_5_last
def Internal.SnakyRows011E.named_envelope_600_7 : List Cell := ([(-2, -3), (-2, -2), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -8), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3)] : List Cell)
theorem Internal.SnakyRows011E.named_envelope_600_7_chain : (named_envelope_600_7.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_7_head : (named_envelope_600_7.map Internal.SnakyRows011E.namedCellKey).head? = some (-259 : ℤ) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_7_last : (named_envelope_600_7.map Internal.SnakyRows011E.namedCellKey).getLast? = some (-131 : ℤ) := by decide
def Internal.SnakyRows011E.named_envelope_600_8 : List Cell := ([(-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, -8), (0, -7), (0, -6), (0, -5), (0, -4)] : List Cell)
theorem Internal.SnakyRows011E.named_envelope_600_8_chain : (named_envelope_600_8.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_8_head : (named_envelope_600_8.map Internal.SnakyRows011E.namedCellKey).head? = some (-130 : ℤ) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_8_last : (named_envelope_600_8.map Internal.SnakyRows011E.namedCellKey).getLast? = some (-4 : ℤ) := by decide
def Internal.SnakyRows011E.named_envelope_600_6 : List Cell := Internal.SnakyRows011E.named_envelope_600_7 ++ Internal.SnakyRows011E.named_envelope_600_8
theorem Internal.SnakyRows011E.named_envelope_600_6_chain : (named_envelope_600_6.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011E.named_chain_append Internal.SnakyRows011E.named_envelope_600_7 Internal.SnakyRows011E.named_envelope_600_8 (-131 : ℤ) (-130 : ℤ)
    Internal.SnakyRows011E.named_envelope_600_7_chain Internal.SnakyRows011E.named_envelope_600_8_chain Internal.SnakyRows011E.named_envelope_600_7_last Internal.SnakyRows011E.named_envelope_600_8_head (by decide)
theorem Internal.SnakyRows011E.named_envelope_600_6_head : (named_envelope_600_6.map Internal.SnakyRows011E.namedCellKey).head? = some (-259 : ℤ) :=
  Internal.SnakyRows011E.named_head_append Internal.SnakyRows011E.named_envelope_600_7 Internal.SnakyRows011E.named_envelope_600_8 (-259 : ℤ) Internal.SnakyRows011E.named_envelope_600_7_head
theorem Internal.SnakyRows011E.named_envelope_600_6_last : (named_envelope_600_6.map Internal.SnakyRows011E.namedCellKey).getLast? = some (-4 : ℤ) :=
  Internal.SnakyRows011E.named_last_append Internal.SnakyRows011E.named_envelope_600_7 Internal.SnakyRows011E.named_envelope_600_8 (-4 : ℤ) Internal.SnakyRows011E.named_envelope_600_8_last
def Internal.SnakyRows011E.named_envelope_600_2 : List Cell := Internal.SnakyRows011E.named_envelope_600_3 ++ Internal.SnakyRows011E.named_envelope_600_6
theorem Internal.SnakyRows011E.named_envelope_600_2_chain : (named_envelope_600_2.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011E.named_chain_append Internal.SnakyRows011E.named_envelope_600_3 Internal.SnakyRows011E.named_envelope_600_6 (-260 : ℤ) (-259 : ℤ)
    Internal.SnakyRows011E.named_envelope_600_3_chain Internal.SnakyRows011E.named_envelope_600_6_chain Internal.SnakyRows011E.named_envelope_600_3_last Internal.SnakyRows011E.named_envelope_600_6_head (by decide)
theorem Internal.SnakyRows011E.named_envelope_600_2_head : (named_envelope_600_2.map Internal.SnakyRows011E.namedCellKey).head? = some (-641 : ℤ) :=
  Internal.SnakyRows011E.named_head_append Internal.SnakyRows011E.named_envelope_600_3 Internal.SnakyRows011E.named_envelope_600_6 (-641 : ℤ) Internal.SnakyRows011E.named_envelope_600_3_head
theorem Internal.SnakyRows011E.named_envelope_600_2_last : (named_envelope_600_2.map Internal.SnakyRows011E.namedCellKey).getLast? = some (-4 : ℤ) :=
  Internal.SnakyRows011E.named_last_append Internal.SnakyRows011E.named_envelope_600_3 Internal.SnakyRows011E.named_envelope_600_6 (-4 : ℤ) Internal.SnakyRows011E.named_envelope_600_6_last
def Internal.SnakyRows011E.named_envelope_600_11 : List Cell := ([(0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -12), (1, -11), (1, -10), (1, -9), (1, -8)] : List Cell)
theorem Internal.SnakyRows011E.named_envelope_600_11_chain : (named_envelope_600_11.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_11_head : (named_envelope_600_11.map Internal.SnakyRows011E.namedCellKey).head? = some (-3 : ℤ) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_11_last : (named_envelope_600_11.map Internal.SnakyRows011E.namedCellKey).getLast? = some (120 : ℤ) := by decide
def Internal.SnakyRows011E.named_envelope_600_12 : List Cell := ([(1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -11)] : List Cell)
theorem Internal.SnakyRows011E.named_envelope_600_12_chain : (named_envelope_600_12.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_12_head : (named_envelope_600_12.map Internal.SnakyRows011E.namedCellKey).head? = some (121 : ℤ) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_12_last : (named_envelope_600_12.map Internal.SnakyRows011E.namedCellKey).getLast? = some (245 : ℤ) := by decide
def Internal.SnakyRows011E.named_envelope_600_10 : List Cell := Internal.SnakyRows011E.named_envelope_600_11 ++ Internal.SnakyRows011E.named_envelope_600_12
theorem Internal.SnakyRows011E.named_envelope_600_10_chain : (named_envelope_600_10.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011E.named_chain_append Internal.SnakyRows011E.named_envelope_600_11 Internal.SnakyRows011E.named_envelope_600_12 (120 : ℤ) (121 : ℤ)
    Internal.SnakyRows011E.named_envelope_600_11_chain Internal.SnakyRows011E.named_envelope_600_12_chain Internal.SnakyRows011E.named_envelope_600_11_last Internal.SnakyRows011E.named_envelope_600_12_head (by decide)
theorem Internal.SnakyRows011E.named_envelope_600_10_head : (named_envelope_600_10.map Internal.SnakyRows011E.namedCellKey).head? = some (-3 : ℤ) :=
  Internal.SnakyRows011E.named_head_append Internal.SnakyRows011E.named_envelope_600_11 Internal.SnakyRows011E.named_envelope_600_12 (-3 : ℤ) Internal.SnakyRows011E.named_envelope_600_11_head
theorem Internal.SnakyRows011E.named_envelope_600_10_last : (named_envelope_600_10.map Internal.SnakyRows011E.namedCellKey).getLast? = some (245 : ℤ) :=
  Internal.SnakyRows011E.named_last_append Internal.SnakyRows011E.named_envelope_600_11 Internal.SnakyRows011E.named_envelope_600_12 (245 : ℤ) Internal.SnakyRows011E.named_envelope_600_12_last
def Internal.SnakyRows011E.named_envelope_600_14 : List Cell := ([(2, -10), (2, -9), (2, -8), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5)] : List Cell)
theorem Internal.SnakyRows011E.named_envelope_600_14_chain : (named_envelope_600_14.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_14_head : (named_envelope_600_14.map Internal.SnakyRows011E.namedCellKey).head? = some (246 : ℤ) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_14_last : (named_envelope_600_14.map Internal.SnakyRows011E.namedCellKey).getLast? = some (261 : ℤ) := by decide
def Internal.SnakyRows011E.named_envelope_600_16 : List Cell := ([(2, 6), (2, 7), (3, -12), (3, -11), (3, -10), (3, -9), (3, -8), (3, -7)] : List Cell)
theorem Internal.SnakyRows011E.named_envelope_600_16_chain : (named_envelope_600_16.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_16_head : (named_envelope_600_16.map Internal.SnakyRows011E.namedCellKey).head? = some (262 : ℤ) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_16_last : (named_envelope_600_16.map Internal.SnakyRows011E.namedCellKey).getLast? = some (377 : ℤ) := by decide
def Internal.SnakyRows011E.named_envelope_600_17 : List Cell := ([(3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2)] : List Cell)
theorem Internal.SnakyRows011E.named_envelope_600_17_chain : (named_envelope_600_17.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_17_head : (named_envelope_600_17.map Internal.SnakyRows011E.namedCellKey).head? = some (378 : ℤ) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_17_last : (named_envelope_600_17.map Internal.SnakyRows011E.namedCellKey).getLast? = some (386 : ℤ) := by decide
def Internal.SnakyRows011E.named_envelope_600_15 : List Cell := Internal.SnakyRows011E.named_envelope_600_16 ++ Internal.SnakyRows011E.named_envelope_600_17
theorem Internal.SnakyRows011E.named_envelope_600_15_chain : (named_envelope_600_15.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011E.named_chain_append Internal.SnakyRows011E.named_envelope_600_16 Internal.SnakyRows011E.named_envelope_600_17 (377 : ℤ) (378 : ℤ)
    Internal.SnakyRows011E.named_envelope_600_16_chain Internal.SnakyRows011E.named_envelope_600_17_chain Internal.SnakyRows011E.named_envelope_600_16_last Internal.SnakyRows011E.named_envelope_600_17_head (by decide)
theorem Internal.SnakyRows011E.named_envelope_600_15_head : (named_envelope_600_15.map Internal.SnakyRows011E.namedCellKey).head? = some (262 : ℤ) :=
  Internal.SnakyRows011E.named_head_append Internal.SnakyRows011E.named_envelope_600_16 Internal.SnakyRows011E.named_envelope_600_17 (262 : ℤ) Internal.SnakyRows011E.named_envelope_600_16_head
theorem Internal.SnakyRows011E.named_envelope_600_15_last : (named_envelope_600_15.map Internal.SnakyRows011E.namedCellKey).getLast? = some (386 : ℤ) :=
  Internal.SnakyRows011E.named_last_append Internal.SnakyRows011E.named_envelope_600_16 Internal.SnakyRows011E.named_envelope_600_17 (386 : ℤ) Internal.SnakyRows011E.named_envelope_600_17_last
def Internal.SnakyRows011E.named_envelope_600_13 : List Cell := Internal.SnakyRows011E.named_envelope_600_14 ++ Internal.SnakyRows011E.named_envelope_600_15
theorem Internal.SnakyRows011E.named_envelope_600_13_chain : (named_envelope_600_13.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011E.named_chain_append Internal.SnakyRows011E.named_envelope_600_14 Internal.SnakyRows011E.named_envelope_600_15 (261 : ℤ) (262 : ℤ)
    Internal.SnakyRows011E.named_envelope_600_14_chain Internal.SnakyRows011E.named_envelope_600_15_chain Internal.SnakyRows011E.named_envelope_600_14_last Internal.SnakyRows011E.named_envelope_600_15_head (by decide)
theorem Internal.SnakyRows011E.named_envelope_600_13_head : (named_envelope_600_13.map Internal.SnakyRows011E.namedCellKey).head? = some (246 : ℤ) :=
  Internal.SnakyRows011E.named_head_append Internal.SnakyRows011E.named_envelope_600_14 Internal.SnakyRows011E.named_envelope_600_15 (246 : ℤ) Internal.SnakyRows011E.named_envelope_600_14_head
theorem Internal.SnakyRows011E.named_envelope_600_13_last : (named_envelope_600_13.map Internal.SnakyRows011E.namedCellKey).getLast? = some (386 : ℤ) :=
  Internal.SnakyRows011E.named_last_append Internal.SnakyRows011E.named_envelope_600_14 Internal.SnakyRows011E.named_envelope_600_15 (386 : ℤ) Internal.SnakyRows011E.named_envelope_600_15_last
def Internal.SnakyRows011E.named_envelope_600_9 : List Cell := Internal.SnakyRows011E.named_envelope_600_10 ++ Internal.SnakyRows011E.named_envelope_600_13
theorem Internal.SnakyRows011E.named_envelope_600_9_chain : (named_envelope_600_9.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011E.named_chain_append Internal.SnakyRows011E.named_envelope_600_10 Internal.SnakyRows011E.named_envelope_600_13 (245 : ℤ) (246 : ℤ)
    Internal.SnakyRows011E.named_envelope_600_10_chain Internal.SnakyRows011E.named_envelope_600_13_chain Internal.SnakyRows011E.named_envelope_600_10_last Internal.SnakyRows011E.named_envelope_600_13_head (by decide)
theorem Internal.SnakyRows011E.named_envelope_600_9_head : (named_envelope_600_9.map Internal.SnakyRows011E.namedCellKey).head? = some (-3 : ℤ) :=
  Internal.SnakyRows011E.named_head_append Internal.SnakyRows011E.named_envelope_600_10 Internal.SnakyRows011E.named_envelope_600_13 (-3 : ℤ) Internal.SnakyRows011E.named_envelope_600_10_head
theorem Internal.SnakyRows011E.named_envelope_600_9_last : (named_envelope_600_9.map Internal.SnakyRows011E.namedCellKey).getLast? = some (386 : ℤ) :=
  Internal.SnakyRows011E.named_last_append Internal.SnakyRows011E.named_envelope_600_10 Internal.SnakyRows011E.named_envelope_600_13 (386 : ℤ) Internal.SnakyRows011E.named_envelope_600_13_last
def Internal.SnakyRows011E.named_envelope_600_1 : List Cell := Internal.SnakyRows011E.named_envelope_600_2 ++ Internal.SnakyRows011E.named_envelope_600_9
theorem Internal.SnakyRows011E.named_envelope_600_1_chain : (named_envelope_600_1.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011E.named_chain_append Internal.SnakyRows011E.named_envelope_600_2 Internal.SnakyRows011E.named_envelope_600_9 (-4 : ℤ) (-3 : ℤ)
    Internal.SnakyRows011E.named_envelope_600_2_chain Internal.SnakyRows011E.named_envelope_600_9_chain Internal.SnakyRows011E.named_envelope_600_2_last Internal.SnakyRows011E.named_envelope_600_9_head (by decide)
theorem Internal.SnakyRows011E.named_envelope_600_1_head : (named_envelope_600_1.map Internal.SnakyRows011E.namedCellKey).head? = some (-641 : ℤ) :=
  Internal.SnakyRows011E.named_head_append Internal.SnakyRows011E.named_envelope_600_2 Internal.SnakyRows011E.named_envelope_600_9 (-641 : ℤ) Internal.SnakyRows011E.named_envelope_600_2_head
theorem Internal.SnakyRows011E.named_envelope_600_1_last : (named_envelope_600_1.map Internal.SnakyRows011E.namedCellKey).getLast? = some (386 : ℤ) :=
  Internal.SnakyRows011E.named_last_append Internal.SnakyRows011E.named_envelope_600_2 Internal.SnakyRows011E.named_envelope_600_9 (386 : ℤ) Internal.SnakyRows011E.named_envelope_600_9_last
def Internal.SnakyRows011E.named_envelope_600_21 : List Cell := ([(3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -10), (4, -9), (4, -8), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0)] : List Cell)
theorem Internal.SnakyRows011E.named_envelope_600_21_chain : (named_envelope_600_21.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_21_head : (named_envelope_600_21.map Internal.SnakyRows011E.namedCellKey).head? = some (387 : ℤ) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_21_last : (named_envelope_600_21.map Internal.SnakyRows011E.namedCellKey).getLast? = some (512 : ℤ) := by decide
def Internal.SnakyRows011E.named_envelope_600_22 : List Cell := ([(4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, -10), (5, -9), (5, -8), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0)] : List Cell)
theorem Internal.SnakyRows011E.named_envelope_600_22_chain : (named_envelope_600_22.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_22_head : (named_envelope_600_22.map Internal.SnakyRows011E.namedCellKey).head? = some (513 : ℤ) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_22_last : (named_envelope_600_22.map Internal.SnakyRows011E.namedCellKey).getLast? = some (640 : ℤ) := by decide
def Internal.SnakyRows011E.named_envelope_600_20 : List Cell := Internal.SnakyRows011E.named_envelope_600_21 ++ Internal.SnakyRows011E.named_envelope_600_22
theorem Internal.SnakyRows011E.named_envelope_600_20_chain : (named_envelope_600_20.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011E.named_chain_append Internal.SnakyRows011E.named_envelope_600_21 Internal.SnakyRows011E.named_envelope_600_22 (512 : ℤ) (513 : ℤ)
    Internal.SnakyRows011E.named_envelope_600_21_chain Internal.SnakyRows011E.named_envelope_600_22_chain Internal.SnakyRows011E.named_envelope_600_21_last Internal.SnakyRows011E.named_envelope_600_22_head (by decide)
theorem Internal.SnakyRows011E.named_envelope_600_20_head : (named_envelope_600_20.map Internal.SnakyRows011E.namedCellKey).head? = some (387 : ℤ) :=
  Internal.SnakyRows011E.named_head_append Internal.SnakyRows011E.named_envelope_600_21 Internal.SnakyRows011E.named_envelope_600_22 (387 : ℤ) Internal.SnakyRows011E.named_envelope_600_21_head
theorem Internal.SnakyRows011E.named_envelope_600_20_last : (named_envelope_600_20.map Internal.SnakyRows011E.namedCellKey).getLast? = some (640 : ℤ) :=
  Internal.SnakyRows011E.named_last_append Internal.SnakyRows011E.named_envelope_600_21 Internal.SnakyRows011E.named_envelope_600_22 (640 : ℤ) Internal.SnakyRows011E.named_envelope_600_22_last
def Internal.SnakyRows011E.named_envelope_600_24 : List Cell := ([(5, 1), (5, 2), (5, 3), (5, 4), (6, -10), (6, -9), (6, -8), (6, -7), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1)] : List Cell)
theorem Internal.SnakyRows011E.named_envelope_600_24_chain : (named_envelope_600_24.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_24_head : (named_envelope_600_24.map Internal.SnakyRows011E.namedCellKey).head? = some (641 : ℤ) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_24_last : (named_envelope_600_24.map Internal.SnakyRows011E.namedCellKey).getLast? = some (769 : ℤ) := by decide
def Internal.SnakyRows011E.named_envelope_600_26 : List Cell := ([(6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, -10), (7, -9), (7, -8)] : List Cell)
theorem Internal.SnakyRows011E.named_envelope_600_26_chain : (named_envelope_600_26.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_26_head : (named_envelope_600_26.map Internal.SnakyRows011E.namedCellKey).head? = some (770 : ℤ) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_26_last : (named_envelope_600_26.map Internal.SnakyRows011E.namedCellKey).getLast? = some (888 : ℤ) := by decide
def Internal.SnakyRows011E.named_envelope_600_27 : List Cell := ([(7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1)] : List Cell)
theorem Internal.SnakyRows011E.named_envelope_600_27_chain : (named_envelope_600_27.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_27_head : (named_envelope_600_27.map Internal.SnakyRows011E.namedCellKey).head? = some (889 : ℤ) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_27_last : (named_envelope_600_27.map Internal.SnakyRows011E.namedCellKey).getLast? = some (897 : ℤ) := by decide
def Internal.SnakyRows011E.named_envelope_600_25 : List Cell := Internal.SnakyRows011E.named_envelope_600_26 ++ Internal.SnakyRows011E.named_envelope_600_27
theorem Internal.SnakyRows011E.named_envelope_600_25_chain : (named_envelope_600_25.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011E.named_chain_append Internal.SnakyRows011E.named_envelope_600_26 Internal.SnakyRows011E.named_envelope_600_27 (888 : ℤ) (889 : ℤ)
    Internal.SnakyRows011E.named_envelope_600_26_chain Internal.SnakyRows011E.named_envelope_600_27_chain Internal.SnakyRows011E.named_envelope_600_26_last Internal.SnakyRows011E.named_envelope_600_27_head (by decide)
theorem Internal.SnakyRows011E.named_envelope_600_25_head : (named_envelope_600_25.map Internal.SnakyRows011E.namedCellKey).head? = some (770 : ℤ) :=
  Internal.SnakyRows011E.named_head_append Internal.SnakyRows011E.named_envelope_600_26 Internal.SnakyRows011E.named_envelope_600_27 (770 : ℤ) Internal.SnakyRows011E.named_envelope_600_26_head
theorem Internal.SnakyRows011E.named_envelope_600_25_last : (named_envelope_600_25.map Internal.SnakyRows011E.namedCellKey).getLast? = some (897 : ℤ) :=
  Internal.SnakyRows011E.named_last_append Internal.SnakyRows011E.named_envelope_600_26 Internal.SnakyRows011E.named_envelope_600_27 (897 : ℤ) Internal.SnakyRows011E.named_envelope_600_27_last
def Internal.SnakyRows011E.named_envelope_600_23 : List Cell := Internal.SnakyRows011E.named_envelope_600_24 ++ Internal.SnakyRows011E.named_envelope_600_25
theorem Internal.SnakyRows011E.named_envelope_600_23_chain : (named_envelope_600_23.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011E.named_chain_append Internal.SnakyRows011E.named_envelope_600_24 Internal.SnakyRows011E.named_envelope_600_25 (769 : ℤ) (770 : ℤ)
    Internal.SnakyRows011E.named_envelope_600_24_chain Internal.SnakyRows011E.named_envelope_600_25_chain Internal.SnakyRows011E.named_envelope_600_24_last Internal.SnakyRows011E.named_envelope_600_25_head (by decide)
theorem Internal.SnakyRows011E.named_envelope_600_23_head : (named_envelope_600_23.map Internal.SnakyRows011E.namedCellKey).head? = some (641 : ℤ) :=
  Internal.SnakyRows011E.named_head_append Internal.SnakyRows011E.named_envelope_600_24 Internal.SnakyRows011E.named_envelope_600_25 (641 : ℤ) Internal.SnakyRows011E.named_envelope_600_24_head
theorem Internal.SnakyRows011E.named_envelope_600_23_last : (named_envelope_600_23.map Internal.SnakyRows011E.namedCellKey).getLast? = some (897 : ℤ) :=
  Internal.SnakyRows011E.named_last_append Internal.SnakyRows011E.named_envelope_600_24 Internal.SnakyRows011E.named_envelope_600_25 (897 : ℤ) Internal.SnakyRows011E.named_envelope_600_25_last
def Internal.SnakyRows011E.named_envelope_600_19 : List Cell := Internal.SnakyRows011E.named_envelope_600_20 ++ Internal.SnakyRows011E.named_envelope_600_23
theorem Internal.SnakyRows011E.named_envelope_600_19_chain : (named_envelope_600_19.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011E.named_chain_append Internal.SnakyRows011E.named_envelope_600_20 Internal.SnakyRows011E.named_envelope_600_23 (640 : ℤ) (641 : ℤ)
    Internal.SnakyRows011E.named_envelope_600_20_chain Internal.SnakyRows011E.named_envelope_600_23_chain Internal.SnakyRows011E.named_envelope_600_20_last Internal.SnakyRows011E.named_envelope_600_23_head (by decide)
theorem Internal.SnakyRows011E.named_envelope_600_19_head : (named_envelope_600_19.map Internal.SnakyRows011E.namedCellKey).head? = some (387 : ℤ) :=
  Internal.SnakyRows011E.named_head_append Internal.SnakyRows011E.named_envelope_600_20 Internal.SnakyRows011E.named_envelope_600_23 (387 : ℤ) Internal.SnakyRows011E.named_envelope_600_20_head
theorem Internal.SnakyRows011E.named_envelope_600_19_last : (named_envelope_600_19.map Internal.SnakyRows011E.namedCellKey).getLast? = some (897 : ℤ) :=
  Internal.SnakyRows011E.named_last_append Internal.SnakyRows011E.named_envelope_600_20 Internal.SnakyRows011E.named_envelope_600_23 (897 : ℤ) Internal.SnakyRows011E.named_envelope_600_23_last
def Internal.SnakyRows011E.named_envelope_600_30 : List Cell := ([(7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, -8), (8, -7), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2)] : List Cell)
theorem Internal.SnakyRows011E.named_envelope_600_30_chain : (named_envelope_600_30.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_30_head : (named_envelope_600_30.map Internal.SnakyRows011E.namedCellKey).head? = some (898 : ℤ) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_30_last : (named_envelope_600_30.map Internal.SnakyRows011E.namedCellKey).getLast? = some (1026 : ℤ) := by decide
def Internal.SnakyRows011E.named_envelope_600_31 : List Cell := ([(8, 3), (8, 4), (8, 5), (9, -7), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5)] : List Cell)
theorem Internal.SnakyRows011E.named_envelope_600_31_chain : (named_envelope_600_31.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_31_head : (named_envelope_600_31.map Internal.SnakyRows011E.namedCellKey).head? = some (1027 : ℤ) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_31_last : (named_envelope_600_31.map Internal.SnakyRows011E.namedCellKey).getLast? = some (1157 : ℤ) := by decide
def Internal.SnakyRows011E.named_envelope_600_29 : List Cell := Internal.SnakyRows011E.named_envelope_600_30 ++ Internal.SnakyRows011E.named_envelope_600_31
theorem Internal.SnakyRows011E.named_envelope_600_29_chain : (named_envelope_600_29.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011E.named_chain_append Internal.SnakyRows011E.named_envelope_600_30 Internal.SnakyRows011E.named_envelope_600_31 (1026 : ℤ) (1027 : ℤ)
    Internal.SnakyRows011E.named_envelope_600_30_chain Internal.SnakyRows011E.named_envelope_600_31_chain Internal.SnakyRows011E.named_envelope_600_30_last Internal.SnakyRows011E.named_envelope_600_31_head (by decide)
theorem Internal.SnakyRows011E.named_envelope_600_29_head : (named_envelope_600_29.map Internal.SnakyRows011E.namedCellKey).head? = some (898 : ℤ) :=
  Internal.SnakyRows011E.named_head_append Internal.SnakyRows011E.named_envelope_600_30 Internal.SnakyRows011E.named_envelope_600_31 (898 : ℤ) Internal.SnakyRows011E.named_envelope_600_30_head
theorem Internal.SnakyRows011E.named_envelope_600_29_last : (named_envelope_600_29.map Internal.SnakyRows011E.namedCellKey).getLast? = some (1157 : ℤ) :=
  Internal.SnakyRows011E.named_last_append Internal.SnakyRows011E.named_envelope_600_30 Internal.SnakyRows011E.named_envelope_600_31 (1157 : ℤ) Internal.SnakyRows011E.named_envelope_600_31_last
def Internal.SnakyRows011E.named_envelope_600_33 : List Cell := ([(9, 6), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0)] : List Cell)
theorem Internal.SnakyRows011E.named_envelope_600_33_chain : (named_envelope_600_33.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_33_head : (named_envelope_600_33.map Internal.SnakyRows011E.namedCellKey).head? = some (1158 : ℤ) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_33_last : (named_envelope_600_33.map Internal.SnakyRows011E.namedCellKey).getLast? = some (1408 : ℤ) := by decide
def Internal.SnakyRows011E.named_envelope_600_35 : List Cell := ([(11, 1), (11, 2), (11, 3), (11, 4), (12, -4), (12, -3), (12, -2), (12, -1)] : List Cell)
theorem Internal.SnakyRows011E.named_envelope_600_35_chain : (named_envelope_600_35.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_35_head : (named_envelope_600_35.map Internal.SnakyRows011E.namedCellKey).head? = some (1409 : ℤ) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_35_last : (named_envelope_600_35.map Internal.SnakyRows011E.namedCellKey).getLast? = some (1535 : ℤ) := by decide
def Internal.SnakyRows011E.named_envelope_600_36 : List Cell := ([(12, 0), (12, 1), (12, 2), (12, 4), (13, 0), (13, 1), (13, 2), (14, 0), (14, 2)] : List Cell)
theorem Internal.SnakyRows011E.named_envelope_600_36_chain : (named_envelope_600_36.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_36_head : (named_envelope_600_36.map Internal.SnakyRows011E.namedCellKey).head? = some (1536 : ℤ) := by decide
theorem Internal.SnakyRows011E.named_envelope_600_36_last : (named_envelope_600_36.map Internal.SnakyRows011E.namedCellKey).getLast? = some (1794 : ℤ) := by decide
def Internal.SnakyRows011E.named_envelope_600_34 : List Cell := Internal.SnakyRows011E.named_envelope_600_35 ++ Internal.SnakyRows011E.named_envelope_600_36
theorem Internal.SnakyRows011E.named_envelope_600_34_chain : (named_envelope_600_34.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011E.named_chain_append Internal.SnakyRows011E.named_envelope_600_35 Internal.SnakyRows011E.named_envelope_600_36 (1535 : ℤ) (1536 : ℤ)
    Internal.SnakyRows011E.named_envelope_600_35_chain Internal.SnakyRows011E.named_envelope_600_36_chain Internal.SnakyRows011E.named_envelope_600_35_last Internal.SnakyRows011E.named_envelope_600_36_head (by decide)
theorem Internal.SnakyRows011E.named_envelope_600_34_head : (named_envelope_600_34.map Internal.SnakyRows011E.namedCellKey).head? = some (1409 : ℤ) :=
  Internal.SnakyRows011E.named_head_append Internal.SnakyRows011E.named_envelope_600_35 Internal.SnakyRows011E.named_envelope_600_36 (1409 : ℤ) Internal.SnakyRows011E.named_envelope_600_35_head
theorem Internal.SnakyRows011E.named_envelope_600_34_last : (named_envelope_600_34.map Internal.SnakyRows011E.namedCellKey).getLast? = some (1794 : ℤ) :=
  Internal.SnakyRows011E.named_last_append Internal.SnakyRows011E.named_envelope_600_35 Internal.SnakyRows011E.named_envelope_600_36 (1794 : ℤ) Internal.SnakyRows011E.named_envelope_600_36_last
def Internal.SnakyRows011E.named_envelope_600_32 : List Cell := Internal.SnakyRows011E.named_envelope_600_33 ++ Internal.SnakyRows011E.named_envelope_600_34
theorem Internal.SnakyRows011E.named_envelope_600_32_chain : (named_envelope_600_32.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011E.named_chain_append Internal.SnakyRows011E.named_envelope_600_33 Internal.SnakyRows011E.named_envelope_600_34 (1408 : ℤ) (1409 : ℤ)
    Internal.SnakyRows011E.named_envelope_600_33_chain Internal.SnakyRows011E.named_envelope_600_34_chain Internal.SnakyRows011E.named_envelope_600_33_last Internal.SnakyRows011E.named_envelope_600_34_head (by decide)
theorem Internal.SnakyRows011E.named_envelope_600_32_head : (named_envelope_600_32.map Internal.SnakyRows011E.namedCellKey).head? = some (1158 : ℤ) :=
  Internal.SnakyRows011E.named_head_append Internal.SnakyRows011E.named_envelope_600_33 Internal.SnakyRows011E.named_envelope_600_34 (1158 : ℤ) Internal.SnakyRows011E.named_envelope_600_33_head
theorem Internal.SnakyRows011E.named_envelope_600_32_last : (named_envelope_600_32.map Internal.SnakyRows011E.namedCellKey).getLast? = some (1794 : ℤ) :=
  Internal.SnakyRows011E.named_last_append Internal.SnakyRows011E.named_envelope_600_33 Internal.SnakyRows011E.named_envelope_600_34 (1794 : ℤ) Internal.SnakyRows011E.named_envelope_600_34_last
def Internal.SnakyRows011E.named_envelope_600_28 : List Cell := Internal.SnakyRows011E.named_envelope_600_29 ++ Internal.SnakyRows011E.named_envelope_600_32
theorem Internal.SnakyRows011E.named_envelope_600_28_chain : (named_envelope_600_28.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011E.named_chain_append Internal.SnakyRows011E.named_envelope_600_29 Internal.SnakyRows011E.named_envelope_600_32 (1157 : ℤ) (1158 : ℤ)
    Internal.SnakyRows011E.named_envelope_600_29_chain Internal.SnakyRows011E.named_envelope_600_32_chain Internal.SnakyRows011E.named_envelope_600_29_last Internal.SnakyRows011E.named_envelope_600_32_head (by decide)
theorem Internal.SnakyRows011E.named_envelope_600_28_head : (named_envelope_600_28.map Internal.SnakyRows011E.namedCellKey).head? = some (898 : ℤ) :=
  Internal.SnakyRows011E.named_head_append Internal.SnakyRows011E.named_envelope_600_29 Internal.SnakyRows011E.named_envelope_600_32 (898 : ℤ) Internal.SnakyRows011E.named_envelope_600_29_head
theorem Internal.SnakyRows011E.named_envelope_600_28_last : (named_envelope_600_28.map Internal.SnakyRows011E.namedCellKey).getLast? = some (1794 : ℤ) :=
  Internal.SnakyRows011E.named_last_append Internal.SnakyRows011E.named_envelope_600_29 Internal.SnakyRows011E.named_envelope_600_32 (1794 : ℤ) Internal.SnakyRows011E.named_envelope_600_32_last
def Internal.SnakyRows011E.named_envelope_600_18 : List Cell := Internal.SnakyRows011E.named_envelope_600_19 ++ Internal.SnakyRows011E.named_envelope_600_28
theorem Internal.SnakyRows011E.named_envelope_600_18_chain : (named_envelope_600_18.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011E.named_chain_append Internal.SnakyRows011E.named_envelope_600_19 Internal.SnakyRows011E.named_envelope_600_28 (897 : ℤ) (898 : ℤ)
    Internal.SnakyRows011E.named_envelope_600_19_chain Internal.SnakyRows011E.named_envelope_600_28_chain Internal.SnakyRows011E.named_envelope_600_19_last Internal.SnakyRows011E.named_envelope_600_28_head (by decide)
theorem Internal.SnakyRows011E.named_envelope_600_18_head : (named_envelope_600_18.map Internal.SnakyRows011E.namedCellKey).head? = some (387 : ℤ) :=
  Internal.SnakyRows011E.named_head_append Internal.SnakyRows011E.named_envelope_600_19 Internal.SnakyRows011E.named_envelope_600_28 (387 : ℤ) Internal.SnakyRows011E.named_envelope_600_19_head
theorem Internal.SnakyRows011E.named_envelope_600_18_last : (named_envelope_600_18.map Internal.SnakyRows011E.namedCellKey).getLast? = some (1794 : ℤ) :=
  Internal.SnakyRows011E.named_last_append Internal.SnakyRows011E.named_envelope_600_19 Internal.SnakyRows011E.named_envelope_600_28 (1794 : ℤ) Internal.SnakyRows011E.named_envelope_600_28_last
def Internal.SnakyRows011E.named_envelope_600_0 : List Cell := Internal.SnakyRows011E.named_envelope_600_1 ++ Internal.SnakyRows011E.named_envelope_600_18
theorem Internal.SnakyRows011E.named_envelope_600_0_chain : (named_envelope_600_0.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011E.named_chain_append Internal.SnakyRows011E.named_envelope_600_1 Internal.SnakyRows011E.named_envelope_600_18 (386 : ℤ) (387 : ℤ)
    Internal.SnakyRows011E.named_envelope_600_1_chain Internal.SnakyRows011E.named_envelope_600_18_chain Internal.SnakyRows011E.named_envelope_600_1_last Internal.SnakyRows011E.named_envelope_600_18_head (by decide)
theorem Internal.SnakyRows011E.named_envelope_600_0_head : (named_envelope_600_0.map Internal.SnakyRows011E.namedCellKey).head? = some (-641 : ℤ) :=
  Internal.SnakyRows011E.named_head_append Internal.SnakyRows011E.named_envelope_600_1 Internal.SnakyRows011E.named_envelope_600_18 (-641 : ℤ) Internal.SnakyRows011E.named_envelope_600_1_head
theorem Internal.SnakyRows011E.named_envelope_600_0_last : (named_envelope_600_0.map Internal.SnakyRows011E.namedCellKey).getLast? = some (1794 : ℤ) :=
  Internal.SnakyRows011E.named_last_append Internal.SnakyRows011E.named_envelope_600_1 Internal.SnakyRows011E.named_envelope_600_18 (1794 : ℤ) Internal.SnakyRows011E.named_envelope_600_18_last
theorem Internal.SnakyRows011E.named_envelope_600_nodup : (Internal.SnakyRows011E.named_envelope_600_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows011E.named_nodup_of_chain Internal.SnakyRows011E.named_envelope_600_0 Internal.SnakyRows011E.named_envelope_600_0_chain
def envelope_600 : Finset Cell := ⟨(Internal.SnakyRows011E.named_envelope_600_0 : Multiset Cell), Internal.SnakyRows011E.named_envelope_600_nodup⟩
def childrenC_600 : Fin 5 → Finset Cell := ![(placedSet 0 (0, 1) required_448), (placedSet 2 (-3, 0) required_278), (placedSet 5 (1, -1) required_592), (placedSet 5 (1, 0) required_403), (placedSet 5 (0, -1) required_146)]
def childrenD_600 : Fin 5 → Finset Cell := ![(placedSet 0 (0, 1) envelope_448), (placedSet 2 (-3, 0) envelope_278), (placedSet 5 (1, -1) envelope_592), (placedSet 5 (1, 0) envelope_403), (placedSet 5 (0, -1) envelope_146)]
theorem common_sub_600 : commonEnvelope childrenD_600 ⊆ insert (0, 0) required_600 := by decide
theorem child_required_sub_600 : ∀ j, childrenC_600 j ⊆ insert (0, 0) required_600 := by decide
theorem Internal.SnakyRows011E.containment_600_0 :
    placedSet 0 (0, 1) envelope_448 ⊆ envelope_600 := by decide
theorem Internal.SnakyRows011E.containment_600_1 :
    placedSet 2 (-3, 0) envelope_278 ⊆ envelope_600 := by decide
theorem Internal.SnakyRows011E.containment_600_2 :
    placedSet 5 (1, -1) envelope_592 ⊆ envelope_600 := by decide +kernel
theorem Internal.SnakyRows011E.containment_600_3 :
    placedSet 5 (1, 0) envelope_403 ⊆ envelope_600 := by decide
theorem Internal.SnakyRows011E.containment_600_4 :
    placedSet 5 (0, -1) envelope_146 ⊆ envelope_600 := by decide
theorem child_envelope_sub_600 : ∀ j, childrenD_600 j ⊆ envelope_600 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows011E.containment_600_0
  · exact Internal.SnakyRows011E.containment_600_1
  · exact Internal.SnakyRows011E.containment_600_2
  · exact Internal.SnakyRows011E.containment_600_3
  · exact Internal.SnakyRows011E.containment_600_4
theorem pivot_mem_600 : (0, 0) ∈ envelope_600 := by decide
theorem children_work_600 : ∀ j, Template HasSnaky 28 (childrenC_600 j) (childrenD_600 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_448 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_278 2 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_592 5 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_403 5 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_146 5 (0, -1)).mono (by decide)
theorem row_works_600 : Template HasSnaky 29 required_600 envelope_600 := by
  refine compose HasSnaky 28 childrenC_600 childrenD_600 children_work_600 (0, 0)
    required_600 envelope_600 pivot_mem_600 child_required_sub_600 child_envelope_sub_600 ?_
  intro b hb; exact common_sub_600 (mem_commonEnvelope childrenD_600 b hb)
end SnakyConditional

end OAI
