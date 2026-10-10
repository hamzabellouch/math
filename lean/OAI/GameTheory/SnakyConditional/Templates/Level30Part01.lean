import OAI.GameTheory.SnakyConditional.Templates.Level29Part02

namespace OAI

namespace SnakyConditional
def required_589 : Finset Cell := ⟨(([(-1, -4), (-1, -3), (-1, -2), (-1, -1)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows010.named_envelope_589_4 : List Cell := ([(-7, 5), (-7, 6), (-7, 8), (-6, 3), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-5, 1), (-5, 2), (-5, 3), (-5, 4)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_589_4_chain : (named_envelope_589_4.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_589_4_head : (named_envelope_589_4.map Internal.SnakyRows010.namedCellKey).head? = some (-891 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_589_4_last : (named_envelope_589_4.map Internal.SnakyRows010.namedCellKey).getLast? = some (-636 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_589_5 : List Cell := ([(-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_589_5_chain : (named_envelope_589_5.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_589_5_head : (named_envelope_589_5.map Internal.SnakyRows010.namedCellKey).head? = some (-635 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_589_5_last : (named_envelope_589_5.map Internal.SnakyRows010.namedCellKey).getLast? = some (-506 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_589_3 : List Cell := Internal.SnakyRows010.named_envelope_589_4 ++ Internal.SnakyRows010.named_envelope_589_5
theorem Internal.SnakyRows010.named_envelope_589_3_chain : (named_envelope_589_3.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_589_4 Internal.SnakyRows010.named_envelope_589_5 (-636 : ℤ) (-635 : ℤ)
    Internal.SnakyRows010.named_envelope_589_4_chain Internal.SnakyRows010.named_envelope_589_5_chain Internal.SnakyRows010.named_envelope_589_4_last Internal.SnakyRows010.named_envelope_589_5_head (by decide)
theorem Internal.SnakyRows010.named_envelope_589_3_head : (named_envelope_589_3.map Internal.SnakyRows010.namedCellKey).head? = some (-891 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_589_4 Internal.SnakyRows010.named_envelope_589_5 (-891 : ℤ) Internal.SnakyRows010.named_envelope_589_4_head
theorem Internal.SnakyRows010.named_envelope_589_3_last : (named_envelope_589_3.map Internal.SnakyRows010.namedCellKey).getLast? = some (-506 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_589_4 Internal.SnakyRows010.named_envelope_589_5 (-506 : ℤ) Internal.SnakyRows010.named_envelope_589_5_last
def Internal.SnakyRows010.named_envelope_589_7 : List Cell := ([(-4, 7), (-4, 8), (-4, 9), (-4, 10), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_589_7_chain : (named_envelope_589_7.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_589_7_head : (named_envelope_589_7.map Internal.SnakyRows010.namedCellKey).head? = some (-505 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_589_7_last : (named_envelope_589_7.map Internal.SnakyRows010.namedCellKey).getLast? = some (-375 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_589_8 : List Cell := ([(-3, 10), (-3, 11), (-3, 12), (-3, 13), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_589_8_chain : (named_envelope_589_8.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_589_8_head : (named_envelope_589_8.map Internal.SnakyRows010.namedCellKey).head? = some (-374 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_589_8_last : (named_envelope_589_8.map Internal.SnakyRows010.namedCellKey).getLast? = some (-248 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_589_6 : List Cell := Internal.SnakyRows010.named_envelope_589_7 ++ Internal.SnakyRows010.named_envelope_589_8
theorem Internal.SnakyRows010.named_envelope_589_6_chain : (named_envelope_589_6.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_589_7 Internal.SnakyRows010.named_envelope_589_8 (-375 : ℤ) (-374 : ℤ)
    Internal.SnakyRows010.named_envelope_589_7_chain Internal.SnakyRows010.named_envelope_589_8_chain Internal.SnakyRows010.named_envelope_589_7_last Internal.SnakyRows010.named_envelope_589_8_head (by decide)
theorem Internal.SnakyRows010.named_envelope_589_6_head : (named_envelope_589_6.map Internal.SnakyRows010.namedCellKey).head? = some (-505 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_589_7 Internal.SnakyRows010.named_envelope_589_8 (-505 : ℤ) Internal.SnakyRows010.named_envelope_589_7_head
theorem Internal.SnakyRows010.named_envelope_589_6_last : (named_envelope_589_6.map Internal.SnakyRows010.namedCellKey).getLast? = some (-248 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_589_7 Internal.SnakyRows010.named_envelope_589_8 (-248 : ℤ) Internal.SnakyRows010.named_envelope_589_8_last
def Internal.SnakyRows010.named_envelope_589_2 : List Cell := Internal.SnakyRows010.named_envelope_589_3 ++ Internal.SnakyRows010.named_envelope_589_6
theorem Internal.SnakyRows010.named_envelope_589_2_chain : (named_envelope_589_2.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_589_3 Internal.SnakyRows010.named_envelope_589_6 (-506 : ℤ) (-505 : ℤ)
    Internal.SnakyRows010.named_envelope_589_3_chain Internal.SnakyRows010.named_envelope_589_6_chain Internal.SnakyRows010.named_envelope_589_3_last Internal.SnakyRows010.named_envelope_589_6_head (by decide)
theorem Internal.SnakyRows010.named_envelope_589_2_head : (named_envelope_589_2.map Internal.SnakyRows010.namedCellKey).head? = some (-891 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_589_3 Internal.SnakyRows010.named_envelope_589_6 (-891 : ℤ) Internal.SnakyRows010.named_envelope_589_3_head
theorem Internal.SnakyRows010.named_envelope_589_2_last : (named_envelope_589_2.map Internal.SnakyRows010.namedCellKey).getLast? = some (-248 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_589_3 Internal.SnakyRows010.named_envelope_589_6 (-248 : ℤ) Internal.SnakyRows010.named_envelope_589_6_last
def Internal.SnakyRows010.named_envelope_589_11 : List Cell := ([(-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_589_11_chain : (named_envelope_589_11.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_589_11_head : (named_envelope_589_11.map Internal.SnakyRows010.namedCellKey).head? = some (-247 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_589_11_last : (named_envelope_589_11.map Internal.SnakyRows010.namedCellKey).getLast? = some (-125 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_589_12 : List Cell := ([(-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -1), (0, 0), (0, 1)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_589_12_chain : (named_envelope_589_12.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_589_12_head : (named_envelope_589_12.map Internal.SnakyRows010.namedCellKey).head? = some (-124 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_589_12_last : (named_envelope_589_12.map Internal.SnakyRows010.namedCellKey).getLast? = some (1 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_589_10 : List Cell := Internal.SnakyRows010.named_envelope_589_11 ++ Internal.SnakyRows010.named_envelope_589_12
theorem Internal.SnakyRows010.named_envelope_589_10_chain : (named_envelope_589_10.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_589_11 Internal.SnakyRows010.named_envelope_589_12 (-125 : ℤ) (-124 : ℤ)
    Internal.SnakyRows010.named_envelope_589_11_chain Internal.SnakyRows010.named_envelope_589_12_chain Internal.SnakyRows010.named_envelope_589_11_last Internal.SnakyRows010.named_envelope_589_12_head (by decide)
theorem Internal.SnakyRows010.named_envelope_589_10_head : (named_envelope_589_10.map Internal.SnakyRows010.namedCellKey).head? = some (-247 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_589_11 Internal.SnakyRows010.named_envelope_589_12 (-247 : ℤ) Internal.SnakyRows010.named_envelope_589_11_head
theorem Internal.SnakyRows010.named_envelope_589_10_last : (named_envelope_589_10.map Internal.SnakyRows010.namedCellKey).getLast? = some (1 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_589_11 Internal.SnakyRows010.named_envelope_589_12 (1 : ℤ) Internal.SnakyRows010.named_envelope_589_12_last
def Internal.SnakyRows010.named_envelope_589_14 : List Cell := ([(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -4), (1, -3), (1, -2)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_589_14_chain : (named_envelope_589_14.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_589_14_head : (named_envelope_589_14.map Internal.SnakyRows010.namedCellKey).head? = some (2 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_589_14_last : (named_envelope_589_14.map Internal.SnakyRows010.namedCellKey).getLast? = some (126 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_589_15 : List Cell := ([(1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_589_15_chain : (named_envelope_589_15.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_589_15_head : (named_envelope_589_15.map Internal.SnakyRows010.namedCellKey).head? = some (127 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_589_15_last : (named_envelope_589_15.map Internal.SnakyRows010.namedCellKey).getLast? = some (139 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_589_13 : List Cell := Internal.SnakyRows010.named_envelope_589_14 ++ Internal.SnakyRows010.named_envelope_589_15
theorem Internal.SnakyRows010.named_envelope_589_13_chain : (named_envelope_589_13.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_589_14 Internal.SnakyRows010.named_envelope_589_15 (126 : ℤ) (127 : ℤ)
    Internal.SnakyRows010.named_envelope_589_14_chain Internal.SnakyRows010.named_envelope_589_15_chain Internal.SnakyRows010.named_envelope_589_14_last Internal.SnakyRows010.named_envelope_589_15_head (by decide)
theorem Internal.SnakyRows010.named_envelope_589_13_head : (named_envelope_589_13.map Internal.SnakyRows010.namedCellKey).head? = some (2 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_589_14 Internal.SnakyRows010.named_envelope_589_15 (2 : ℤ) Internal.SnakyRows010.named_envelope_589_14_head
theorem Internal.SnakyRows010.named_envelope_589_13_last : (named_envelope_589_13.map Internal.SnakyRows010.namedCellKey).getLast? = some (139 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_589_14 Internal.SnakyRows010.named_envelope_589_15 (139 : ℤ) Internal.SnakyRows010.named_envelope_589_15_last
def Internal.SnakyRows010.named_envelope_589_9 : List Cell := Internal.SnakyRows010.named_envelope_589_10 ++ Internal.SnakyRows010.named_envelope_589_13
theorem Internal.SnakyRows010.named_envelope_589_9_chain : (named_envelope_589_9.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_589_10 Internal.SnakyRows010.named_envelope_589_13 (1 : ℤ) (2 : ℤ)
    Internal.SnakyRows010.named_envelope_589_10_chain Internal.SnakyRows010.named_envelope_589_13_chain Internal.SnakyRows010.named_envelope_589_10_last Internal.SnakyRows010.named_envelope_589_13_head (by decide)
theorem Internal.SnakyRows010.named_envelope_589_9_head : (named_envelope_589_9.map Internal.SnakyRows010.namedCellKey).head? = some (-247 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_589_10 Internal.SnakyRows010.named_envelope_589_13 (-247 : ℤ) Internal.SnakyRows010.named_envelope_589_10_head
theorem Internal.SnakyRows010.named_envelope_589_9_last : (named_envelope_589_9.map Internal.SnakyRows010.namedCellKey).getLast? = some (139 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_589_10 Internal.SnakyRows010.named_envelope_589_13 (139 : ℤ) Internal.SnakyRows010.named_envelope_589_13_last
def Internal.SnakyRows010.named_envelope_589_1 : List Cell := Internal.SnakyRows010.named_envelope_589_2 ++ Internal.SnakyRows010.named_envelope_589_9
theorem Internal.SnakyRows010.named_envelope_589_1_chain : (named_envelope_589_1.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_589_2 Internal.SnakyRows010.named_envelope_589_9 (-248 : ℤ) (-247 : ℤ)
    Internal.SnakyRows010.named_envelope_589_2_chain Internal.SnakyRows010.named_envelope_589_9_chain Internal.SnakyRows010.named_envelope_589_2_last Internal.SnakyRows010.named_envelope_589_9_head (by decide)
theorem Internal.SnakyRows010.named_envelope_589_1_head : (named_envelope_589_1.map Internal.SnakyRows010.namedCellKey).head? = some (-891 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_589_2 Internal.SnakyRows010.named_envelope_589_9 (-891 : ℤ) Internal.SnakyRows010.named_envelope_589_2_head
theorem Internal.SnakyRows010.named_envelope_589_1_last : (named_envelope_589_1.map Internal.SnakyRows010.namedCellKey).getLast? = some (139 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_589_2 Internal.SnakyRows010.named_envelope_589_9 (139 : ℤ) Internal.SnakyRows010.named_envelope_589_9_last
def Internal.SnakyRows010.named_envelope_589_19 : List Cell := ([(2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_589_19_chain : (named_envelope_589_19.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_589_19_head : (named_envelope_589_19.map Internal.SnakyRows010.namedCellKey).head? = some (251 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_589_19_last : (named_envelope_589_19.map Internal.SnakyRows010.namedCellKey).getLast? = some (262 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_589_20 : List Cell := ([(2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_589_20_chain : (named_envelope_589_20.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_589_20_head : (named_envelope_589_20.map Internal.SnakyRows010.namedCellKey).head? = some (263 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_589_20_last : (named_envelope_589_20.map Internal.SnakyRows010.namedCellKey).getLast? = some (387 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_589_18 : List Cell := Internal.SnakyRows010.named_envelope_589_19 ++ Internal.SnakyRows010.named_envelope_589_20
theorem Internal.SnakyRows010.named_envelope_589_18_chain : (named_envelope_589_18.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_589_19 Internal.SnakyRows010.named_envelope_589_20 (262 : ℤ) (263 : ℤ)
    Internal.SnakyRows010.named_envelope_589_19_chain Internal.SnakyRows010.named_envelope_589_20_chain Internal.SnakyRows010.named_envelope_589_19_last Internal.SnakyRows010.named_envelope_589_20_head (by decide)
theorem Internal.SnakyRows010.named_envelope_589_18_head : (named_envelope_589_18.map Internal.SnakyRows010.namedCellKey).head? = some (251 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_589_19 Internal.SnakyRows010.named_envelope_589_20 (251 : ℤ) Internal.SnakyRows010.named_envelope_589_19_head
theorem Internal.SnakyRows010.named_envelope_589_18_last : (named_envelope_589_18.map Internal.SnakyRows010.namedCellKey).getLast? = some (387 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_589_19 Internal.SnakyRows010.named_envelope_589_20 (387 : ℤ) Internal.SnakyRows010.named_envelope_589_20_last
def Internal.SnakyRows010.named_envelope_589_22 : List Cell := ([(3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_589_22_chain : (named_envelope_589_22.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_589_22_head : (named_envelope_589_22.map Internal.SnakyRows010.namedCellKey).head? = some (388 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_589_22_last : (named_envelope_589_22.map Internal.SnakyRows010.namedCellKey).getLast? = some (511 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_589_23 : List Cell := ([(4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -3), (5, -2), (5, -1)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_589_23_chain : (named_envelope_589_23.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_589_23_head : (named_envelope_589_23.map Internal.SnakyRows010.namedCellKey).head? = some (512 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_589_23_last : (named_envelope_589_23.map Internal.SnakyRows010.namedCellKey).getLast? = some (639 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_589_21 : List Cell := Internal.SnakyRows010.named_envelope_589_22 ++ Internal.SnakyRows010.named_envelope_589_23
theorem Internal.SnakyRows010.named_envelope_589_21_chain : (named_envelope_589_21.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_589_22 Internal.SnakyRows010.named_envelope_589_23 (511 : ℤ) (512 : ℤ)
    Internal.SnakyRows010.named_envelope_589_22_chain Internal.SnakyRows010.named_envelope_589_23_chain Internal.SnakyRows010.named_envelope_589_22_last Internal.SnakyRows010.named_envelope_589_23_head (by decide)
theorem Internal.SnakyRows010.named_envelope_589_21_head : (named_envelope_589_21.map Internal.SnakyRows010.namedCellKey).head? = some (388 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_589_22 Internal.SnakyRows010.named_envelope_589_23 (388 : ℤ) Internal.SnakyRows010.named_envelope_589_22_head
theorem Internal.SnakyRows010.named_envelope_589_21_last : (named_envelope_589_21.map Internal.SnakyRows010.namedCellKey).getLast? = some (639 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_589_22 Internal.SnakyRows010.named_envelope_589_23 (639 : ℤ) Internal.SnakyRows010.named_envelope_589_23_last
def Internal.SnakyRows010.named_envelope_589_17 : List Cell := Internal.SnakyRows010.named_envelope_589_18 ++ Internal.SnakyRows010.named_envelope_589_21
theorem Internal.SnakyRows010.named_envelope_589_17_chain : (named_envelope_589_17.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_589_18 Internal.SnakyRows010.named_envelope_589_21 (387 : ℤ) (388 : ℤ)
    Internal.SnakyRows010.named_envelope_589_18_chain Internal.SnakyRows010.named_envelope_589_21_chain Internal.SnakyRows010.named_envelope_589_18_last Internal.SnakyRows010.named_envelope_589_21_head (by decide)
theorem Internal.SnakyRows010.named_envelope_589_17_head : (named_envelope_589_17.map Internal.SnakyRows010.namedCellKey).head? = some (251 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_589_18 Internal.SnakyRows010.named_envelope_589_21 (251 : ℤ) Internal.SnakyRows010.named_envelope_589_18_head
theorem Internal.SnakyRows010.named_envelope_589_17_last : (named_envelope_589_17.map Internal.SnakyRows010.namedCellKey).getLast? = some (639 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_589_18 Internal.SnakyRows010.named_envelope_589_21 (639 : ℤ) Internal.SnakyRows010.named_envelope_589_21_last
def Internal.SnakyRows010.named_envelope_589_26 : List Cell := ([(5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, -3), (6, -2), (6, -1)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_589_26_chain : (named_envelope_589_26.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_589_26_head : (named_envelope_589_26.map Internal.SnakyRows010.namedCellKey).head? = some (640 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_589_26_last : (named_envelope_589_26.map Internal.SnakyRows010.namedCellKey).getLast? = some (767 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_589_27 : List Cell := ([(6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, -3), (7, -2), (7, -1), (7, 0)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_589_27_chain : (named_envelope_589_27.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_589_27_head : (named_envelope_589_27.map Internal.SnakyRows010.namedCellKey).head? = some (768 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_589_27_last : (named_envelope_589_27.map Internal.SnakyRows010.namedCellKey).getLast? = some (896 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_589_25 : List Cell := Internal.SnakyRows010.named_envelope_589_26 ++ Internal.SnakyRows010.named_envelope_589_27
theorem Internal.SnakyRows010.named_envelope_589_25_chain : (named_envelope_589_25.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_589_26 Internal.SnakyRows010.named_envelope_589_27 (767 : ℤ) (768 : ℤ)
    Internal.SnakyRows010.named_envelope_589_26_chain Internal.SnakyRows010.named_envelope_589_27_chain Internal.SnakyRows010.named_envelope_589_26_last Internal.SnakyRows010.named_envelope_589_27_head (by decide)
theorem Internal.SnakyRows010.named_envelope_589_25_head : (named_envelope_589_25.map Internal.SnakyRows010.namedCellKey).head? = some (640 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_589_26 Internal.SnakyRows010.named_envelope_589_27 (640 : ℤ) Internal.SnakyRows010.named_envelope_589_26_head
theorem Internal.SnakyRows010.named_envelope_589_25_last : (named_envelope_589_25.map Internal.SnakyRows010.namedCellKey).getLast? = some (896 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_589_26 Internal.SnakyRows010.named_envelope_589_27 (896 : ℤ) Internal.SnakyRows010.named_envelope_589_27_last
def Internal.SnakyRows010.named_envelope_589_29 : List Cell := ([(7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_589_29_chain : (named_envelope_589_29.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_589_29_head : (named_envelope_589_29.map Internal.SnakyRows010.namedCellKey).head? = some (897 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_589_29_last : (named_envelope_589_29.map Internal.SnakyRows010.namedCellKey).getLast? = some (1029 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_589_30 : List Cell := ([(8, 6), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (10, 0), (10, 1), (10, 2), (11, 0), (11, 2)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_589_30_chain : (named_envelope_589_30.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_589_30_head : (named_envelope_589_30.map Internal.SnakyRows010.namedCellKey).head? = some (1030 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_589_30_last : (named_envelope_589_30.map Internal.SnakyRows010.namedCellKey).getLast? = some (1410 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_589_28 : List Cell := Internal.SnakyRows010.named_envelope_589_29 ++ Internal.SnakyRows010.named_envelope_589_30
theorem Internal.SnakyRows010.named_envelope_589_28_chain : (named_envelope_589_28.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_589_29 Internal.SnakyRows010.named_envelope_589_30 (1029 : ℤ) (1030 : ℤ)
    Internal.SnakyRows010.named_envelope_589_29_chain Internal.SnakyRows010.named_envelope_589_30_chain Internal.SnakyRows010.named_envelope_589_29_last Internal.SnakyRows010.named_envelope_589_30_head (by decide)
theorem Internal.SnakyRows010.named_envelope_589_28_head : (named_envelope_589_28.map Internal.SnakyRows010.namedCellKey).head? = some (897 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_589_29 Internal.SnakyRows010.named_envelope_589_30 (897 : ℤ) Internal.SnakyRows010.named_envelope_589_29_head
theorem Internal.SnakyRows010.named_envelope_589_28_last : (named_envelope_589_28.map Internal.SnakyRows010.namedCellKey).getLast? = some (1410 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_589_29 Internal.SnakyRows010.named_envelope_589_30 (1410 : ℤ) Internal.SnakyRows010.named_envelope_589_30_last
def Internal.SnakyRows010.named_envelope_589_24 : List Cell := Internal.SnakyRows010.named_envelope_589_25 ++ Internal.SnakyRows010.named_envelope_589_28
theorem Internal.SnakyRows010.named_envelope_589_24_chain : (named_envelope_589_24.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_589_25 Internal.SnakyRows010.named_envelope_589_28 (896 : ℤ) (897 : ℤ)
    Internal.SnakyRows010.named_envelope_589_25_chain Internal.SnakyRows010.named_envelope_589_28_chain Internal.SnakyRows010.named_envelope_589_25_last Internal.SnakyRows010.named_envelope_589_28_head (by decide)
theorem Internal.SnakyRows010.named_envelope_589_24_head : (named_envelope_589_24.map Internal.SnakyRows010.namedCellKey).head? = some (640 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_589_25 Internal.SnakyRows010.named_envelope_589_28 (640 : ℤ) Internal.SnakyRows010.named_envelope_589_25_head
theorem Internal.SnakyRows010.named_envelope_589_24_last : (named_envelope_589_24.map Internal.SnakyRows010.namedCellKey).getLast? = some (1410 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_589_25 Internal.SnakyRows010.named_envelope_589_28 (1410 : ℤ) Internal.SnakyRows010.named_envelope_589_28_last
def Internal.SnakyRows010.named_envelope_589_16 : List Cell := Internal.SnakyRows010.named_envelope_589_17 ++ Internal.SnakyRows010.named_envelope_589_24
theorem Internal.SnakyRows010.named_envelope_589_16_chain : (named_envelope_589_16.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_589_17 Internal.SnakyRows010.named_envelope_589_24 (639 : ℤ) (640 : ℤ)
    Internal.SnakyRows010.named_envelope_589_17_chain Internal.SnakyRows010.named_envelope_589_24_chain Internal.SnakyRows010.named_envelope_589_17_last Internal.SnakyRows010.named_envelope_589_24_head (by decide)
theorem Internal.SnakyRows010.named_envelope_589_16_head : (named_envelope_589_16.map Internal.SnakyRows010.namedCellKey).head? = some (251 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_589_17 Internal.SnakyRows010.named_envelope_589_24 (251 : ℤ) Internal.SnakyRows010.named_envelope_589_17_head
theorem Internal.SnakyRows010.named_envelope_589_16_last : (named_envelope_589_16.map Internal.SnakyRows010.namedCellKey).getLast? = some (1410 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_589_17 Internal.SnakyRows010.named_envelope_589_24 (1410 : ℤ) Internal.SnakyRows010.named_envelope_589_24_last
def Internal.SnakyRows010.named_envelope_589_0 : List Cell := Internal.SnakyRows010.named_envelope_589_1 ++ Internal.SnakyRows010.named_envelope_589_16
theorem Internal.SnakyRows010.named_envelope_589_0_chain : (named_envelope_589_0.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_589_1 Internal.SnakyRows010.named_envelope_589_16 (139 : ℤ) (251 : ℤ)
    Internal.SnakyRows010.named_envelope_589_1_chain Internal.SnakyRows010.named_envelope_589_16_chain Internal.SnakyRows010.named_envelope_589_1_last Internal.SnakyRows010.named_envelope_589_16_head (by decide)
theorem Internal.SnakyRows010.named_envelope_589_0_head : (named_envelope_589_0.map Internal.SnakyRows010.namedCellKey).head? = some (-891 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_589_1 Internal.SnakyRows010.named_envelope_589_16 (-891 : ℤ) Internal.SnakyRows010.named_envelope_589_1_head
theorem Internal.SnakyRows010.named_envelope_589_0_last : (named_envelope_589_0.map Internal.SnakyRows010.namedCellKey).getLast? = some (1410 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_589_1 Internal.SnakyRows010.named_envelope_589_16 (1410 : ℤ) Internal.SnakyRows010.named_envelope_589_16_last
theorem Internal.SnakyRows010.named_envelope_589_nodup : (Internal.SnakyRows010.named_envelope_589_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows010.named_nodup_of_chain Internal.SnakyRows010.named_envelope_589_0 Internal.SnakyRows010.named_envelope_589_0_chain
def envelope_589 : Finset Cell := ⟨(Internal.SnakyRows010.named_envelope_589_0 : Multiset Cell), Internal.SnakyRows010.named_envelope_589_nodup⟩
def childrenC_589 : Fin 2 → Finset Cell := ![(placedSet 1 (0, -1) required_4), (placedSet 0 (0, 1) required_588)]
def childrenD_589 : Fin 2 → Finset Cell := ![(placedSet 1 (0, -1) envelope_4), (placedSet 0 (0, 1) envelope_588)]
theorem common_sub_589 : commonEnvelope childrenD_589 ⊆ insert (0, 0) required_589 := by decide
theorem child_required_sub_589 : ∀ j, childrenC_589 j ⊆ insert (0, 0) required_589 := by decide
theorem Internal.SnakyRows010.containment_589_0 :
    placedSet 1 (0, -1) envelope_4 ⊆ envelope_589 := by decide
theorem Internal.SnakyRows010.containment_589_1 :
    placedSet 0 (0, 1) envelope_588 ⊆ envelope_589 := by decide +kernel
theorem child_envelope_sub_589 : ∀ j, childrenD_589 j ⊆ envelope_589 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows010.containment_589_0
  · exact Internal.SnakyRows010.containment_589_1
theorem pivot_mem_589 : (0, 0) ∈ envelope_589 := by decide
theorem children_work_589 : ∀ j, Template HasSnaky 27 (childrenC_589 j) (childrenD_589 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_4 1 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_588 0 (0, 1)).mono (by decide)
theorem row_works_589 : Template HasSnaky 28 required_589 envelope_589 := by
  refine compose HasSnaky 27 childrenC_589 childrenD_589 children_work_589 (0, 0)
    required_589 envelope_589 pivot_mem_589 child_required_sub_589 child_envelope_sub_589 ?_
  intro b hb; exact common_sub_589 (mem_commonEnvelope childrenD_589 b hb)
end SnakyConditional

end OAI
