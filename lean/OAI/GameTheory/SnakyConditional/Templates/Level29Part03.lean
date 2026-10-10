import OAI.GameTheory.SnakyConditional.Templates.Level28Part04

namespace OAI

namespace SnakyConditional
def required_593 : Finset Cell := ⟨(([(-1, -4), (-1, -3), (0, -3), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows010.named_envelope_593_4 : List Cell := ([(-7, 4), (-7, 5), (-7, 7), (-6, 2), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 0), (-5, 1), (-5, 2), (-5, 3)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_593_4_chain : (named_envelope_593_4.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_593_4_head : (named_envelope_593_4.map Internal.SnakyRows010.namedCellKey).head? = some (-892 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_593_4_last : (named_envelope_593_4.map Internal.SnakyRows010.namedCellKey).getLast? = some (-637 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_593_5 : List Cell := ([(-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_593_5_chain : (named_envelope_593_5.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_593_5_head : (named_envelope_593_5.map Internal.SnakyRows010.namedCellKey).head? = some (-636 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_593_5_last : (named_envelope_593_5.map Internal.SnakyRows010.namedCellKey).getLast? = some (-507 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_593_3 : List Cell := Internal.SnakyRows010.named_envelope_593_4 ++ Internal.SnakyRows010.named_envelope_593_5
theorem Internal.SnakyRows010.named_envelope_593_3_chain : (named_envelope_593_3.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_593_4 Internal.SnakyRows010.named_envelope_593_5 (-637 : ℤ) (-636 : ℤ)
    Internal.SnakyRows010.named_envelope_593_4_chain Internal.SnakyRows010.named_envelope_593_5_chain Internal.SnakyRows010.named_envelope_593_4_last Internal.SnakyRows010.named_envelope_593_5_head (by decide)
theorem Internal.SnakyRows010.named_envelope_593_3_head : (named_envelope_593_3.map Internal.SnakyRows010.namedCellKey).head? = some (-892 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_593_4 Internal.SnakyRows010.named_envelope_593_5 (-892 : ℤ) Internal.SnakyRows010.named_envelope_593_4_head
theorem Internal.SnakyRows010.named_envelope_593_3_last : (named_envelope_593_3.map Internal.SnakyRows010.namedCellKey).getLast? = some (-507 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_593_4 Internal.SnakyRows010.named_envelope_593_5 (-507 : ℤ) Internal.SnakyRows010.named_envelope_593_5_last
def Internal.SnakyRows010.named_envelope_593_7 : List Cell := ([(-4, 6), (-4, 7), (-4, 8), (-4, 9), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_593_7_chain : (named_envelope_593_7.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_593_7_head : (named_envelope_593_7.map Internal.SnakyRows010.namedCellKey).head? = some (-506 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_593_7_last : (named_envelope_593_7.map Internal.SnakyRows010.namedCellKey).getLast? = some (-377 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_593_8 : List Cell := ([(-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_593_8_chain : (named_envelope_593_8.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_593_8_head : (named_envelope_593_8.map Internal.SnakyRows010.namedCellKey).head? = some (-376 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_593_8_last : (named_envelope_593_8.map Internal.SnakyRows010.namedCellKey).getLast? = some (-250 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_593_6 : List Cell := Internal.SnakyRows010.named_envelope_593_7 ++ Internal.SnakyRows010.named_envelope_593_8
theorem Internal.SnakyRows010.named_envelope_593_6_chain : (named_envelope_593_6.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_593_7 Internal.SnakyRows010.named_envelope_593_8 (-377 : ℤ) (-376 : ℤ)
    Internal.SnakyRows010.named_envelope_593_7_chain Internal.SnakyRows010.named_envelope_593_8_chain Internal.SnakyRows010.named_envelope_593_7_last Internal.SnakyRows010.named_envelope_593_8_head (by decide)
theorem Internal.SnakyRows010.named_envelope_593_6_head : (named_envelope_593_6.map Internal.SnakyRows010.namedCellKey).head? = some (-506 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_593_7 Internal.SnakyRows010.named_envelope_593_8 (-506 : ℤ) Internal.SnakyRows010.named_envelope_593_7_head
theorem Internal.SnakyRows010.named_envelope_593_6_last : (named_envelope_593_6.map Internal.SnakyRows010.namedCellKey).getLast? = some (-250 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_593_7 Internal.SnakyRows010.named_envelope_593_8 (-250 : ℤ) Internal.SnakyRows010.named_envelope_593_8_last
def Internal.SnakyRows010.named_envelope_593_2 : List Cell := Internal.SnakyRows010.named_envelope_593_3 ++ Internal.SnakyRows010.named_envelope_593_6
theorem Internal.SnakyRows010.named_envelope_593_2_chain : (named_envelope_593_2.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_593_3 Internal.SnakyRows010.named_envelope_593_6 (-507 : ℤ) (-506 : ℤ)
    Internal.SnakyRows010.named_envelope_593_3_chain Internal.SnakyRows010.named_envelope_593_6_chain Internal.SnakyRows010.named_envelope_593_3_last Internal.SnakyRows010.named_envelope_593_6_head (by decide)
theorem Internal.SnakyRows010.named_envelope_593_2_head : (named_envelope_593_2.map Internal.SnakyRows010.namedCellKey).head? = some (-892 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_593_3 Internal.SnakyRows010.named_envelope_593_6 (-892 : ℤ) Internal.SnakyRows010.named_envelope_593_3_head
theorem Internal.SnakyRows010.named_envelope_593_2_last : (named_envelope_593_2.map Internal.SnakyRows010.namedCellKey).getLast? = some (-250 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_593_3 Internal.SnakyRows010.named_envelope_593_6 (-250 : ℤ) Internal.SnakyRows010.named_envelope_593_6_last
def Internal.SnakyRows010.named_envelope_593_11 : List Cell := ([(-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_593_11_chain : (named_envelope_593_11.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_593_11_head : (named_envelope_593_11.map Internal.SnakyRows010.namedCellKey).head? = some (-249 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_593_11_last : (named_envelope_593_11.map Internal.SnakyRows010.namedCellKey).getLast? = some (-124 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_593_12 : List Cell := ([(-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_593_12_chain : (named_envelope_593_12.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_593_12_head : (named_envelope_593_12.map Internal.SnakyRows010.namedCellKey).head? = some (-123 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_593_12_last : (named_envelope_593_12.map Internal.SnakyRows010.namedCellKey).getLast? = some (1 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_593_10 : List Cell := Internal.SnakyRows010.named_envelope_593_11 ++ Internal.SnakyRows010.named_envelope_593_12
theorem Internal.SnakyRows010.named_envelope_593_10_chain : (named_envelope_593_10.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_593_11 Internal.SnakyRows010.named_envelope_593_12 (-124 : ℤ) (-123 : ℤ)
    Internal.SnakyRows010.named_envelope_593_11_chain Internal.SnakyRows010.named_envelope_593_12_chain Internal.SnakyRows010.named_envelope_593_11_last Internal.SnakyRows010.named_envelope_593_12_head (by decide)
theorem Internal.SnakyRows010.named_envelope_593_10_head : (named_envelope_593_10.map Internal.SnakyRows010.namedCellKey).head? = some (-249 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_593_11 Internal.SnakyRows010.named_envelope_593_12 (-249 : ℤ) Internal.SnakyRows010.named_envelope_593_11_head
theorem Internal.SnakyRows010.named_envelope_593_10_last : (named_envelope_593_10.map Internal.SnakyRows010.namedCellKey).getLast? = some (1 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_593_11 Internal.SnakyRows010.named_envelope_593_12 (1 : ℤ) Internal.SnakyRows010.named_envelope_593_12_last
def Internal.SnakyRows010.named_envelope_593_14 : List Cell := ([(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -5), (1, -4), (1, -3), (1, -2)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_593_14_chain : (named_envelope_593_14.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_593_14_head : (named_envelope_593_14.map Internal.SnakyRows010.namedCellKey).head? = some (2 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_593_14_last : (named_envelope_593_14.map Internal.SnakyRows010.namedCellKey).getLast? = some (126 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_593_15 : List Cell := ([(1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -6)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_593_15_chain : (named_envelope_593_15.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_593_15_head : (named_envelope_593_15.map Internal.SnakyRows010.namedCellKey).head? = some (127 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_593_15_last : (named_envelope_593_15.map Internal.SnakyRows010.namedCellKey).getLast? = some (250 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_593_13 : List Cell := Internal.SnakyRows010.named_envelope_593_14 ++ Internal.SnakyRows010.named_envelope_593_15
theorem Internal.SnakyRows010.named_envelope_593_13_chain : (named_envelope_593_13.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_593_14 Internal.SnakyRows010.named_envelope_593_15 (126 : ℤ) (127 : ℤ)
    Internal.SnakyRows010.named_envelope_593_14_chain Internal.SnakyRows010.named_envelope_593_15_chain Internal.SnakyRows010.named_envelope_593_14_last Internal.SnakyRows010.named_envelope_593_15_head (by decide)
theorem Internal.SnakyRows010.named_envelope_593_13_head : (named_envelope_593_13.map Internal.SnakyRows010.namedCellKey).head? = some (2 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_593_14 Internal.SnakyRows010.named_envelope_593_15 (2 : ℤ) Internal.SnakyRows010.named_envelope_593_14_head
theorem Internal.SnakyRows010.named_envelope_593_13_last : (named_envelope_593_13.map Internal.SnakyRows010.namedCellKey).getLast? = some (250 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_593_14 Internal.SnakyRows010.named_envelope_593_15 (250 : ℤ) Internal.SnakyRows010.named_envelope_593_15_last
def Internal.SnakyRows010.named_envelope_593_9 : List Cell := Internal.SnakyRows010.named_envelope_593_10 ++ Internal.SnakyRows010.named_envelope_593_13
theorem Internal.SnakyRows010.named_envelope_593_9_chain : (named_envelope_593_9.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_593_10 Internal.SnakyRows010.named_envelope_593_13 (1 : ℤ) (2 : ℤ)
    Internal.SnakyRows010.named_envelope_593_10_chain Internal.SnakyRows010.named_envelope_593_13_chain Internal.SnakyRows010.named_envelope_593_10_last Internal.SnakyRows010.named_envelope_593_13_head (by decide)
theorem Internal.SnakyRows010.named_envelope_593_9_head : (named_envelope_593_9.map Internal.SnakyRows010.namedCellKey).head? = some (-249 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_593_10 Internal.SnakyRows010.named_envelope_593_13 (-249 : ℤ) Internal.SnakyRows010.named_envelope_593_10_head
theorem Internal.SnakyRows010.named_envelope_593_9_last : (named_envelope_593_9.map Internal.SnakyRows010.namedCellKey).getLast? = some (250 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_593_10 Internal.SnakyRows010.named_envelope_593_13 (250 : ℤ) Internal.SnakyRows010.named_envelope_593_13_last
def Internal.SnakyRows010.named_envelope_593_1 : List Cell := Internal.SnakyRows010.named_envelope_593_2 ++ Internal.SnakyRows010.named_envelope_593_9
theorem Internal.SnakyRows010.named_envelope_593_1_chain : (named_envelope_593_1.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_593_2 Internal.SnakyRows010.named_envelope_593_9 (-250 : ℤ) (-249 : ℤ)
    Internal.SnakyRows010.named_envelope_593_2_chain Internal.SnakyRows010.named_envelope_593_9_chain Internal.SnakyRows010.named_envelope_593_2_last Internal.SnakyRows010.named_envelope_593_9_head (by decide)
theorem Internal.SnakyRows010.named_envelope_593_1_head : (named_envelope_593_1.map Internal.SnakyRows010.namedCellKey).head? = some (-892 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_593_2 Internal.SnakyRows010.named_envelope_593_9 (-892 : ℤ) Internal.SnakyRows010.named_envelope_593_2_head
theorem Internal.SnakyRows010.named_envelope_593_1_last : (named_envelope_593_1.map Internal.SnakyRows010.namedCellKey).getLast? = some (250 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_593_2 Internal.SnakyRows010.named_envelope_593_9 (250 : ℤ) Internal.SnakyRows010.named_envelope_593_9_last
def Internal.SnakyRows010.named_envelope_593_19 : List Cell := ([(2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_593_19_chain : (named_envelope_593_19.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_593_19_head : (named_envelope_593_19.map Internal.SnakyRows010.namedCellKey).head? = some (251 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_593_19_last : (named_envelope_593_19.map Internal.SnakyRows010.namedCellKey).getLast? = some (262 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_593_20 : List Cell := ([(2, 7), (2, 8), (2, 9), (2, 10), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_593_20_chain : (named_envelope_593_20.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_593_20_head : (named_envelope_593_20.map Internal.SnakyRows010.namedCellKey).head? = some (263 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_593_20_last : (named_envelope_593_20.map Internal.SnakyRows010.namedCellKey).getLast? = some (387 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_593_18 : List Cell := Internal.SnakyRows010.named_envelope_593_19 ++ Internal.SnakyRows010.named_envelope_593_20
theorem Internal.SnakyRows010.named_envelope_593_18_chain : (named_envelope_593_18.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_593_19 Internal.SnakyRows010.named_envelope_593_20 (262 : ℤ) (263 : ℤ)
    Internal.SnakyRows010.named_envelope_593_19_chain Internal.SnakyRows010.named_envelope_593_20_chain Internal.SnakyRows010.named_envelope_593_19_last Internal.SnakyRows010.named_envelope_593_20_head (by decide)
theorem Internal.SnakyRows010.named_envelope_593_18_head : (named_envelope_593_18.map Internal.SnakyRows010.namedCellKey).head? = some (251 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_593_19 Internal.SnakyRows010.named_envelope_593_20 (251 : ℤ) Internal.SnakyRows010.named_envelope_593_19_head
theorem Internal.SnakyRows010.named_envelope_593_18_last : (named_envelope_593_18.map Internal.SnakyRows010.namedCellKey).getLast? = some (387 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_593_19 Internal.SnakyRows010.named_envelope_593_20 (387 : ℤ) Internal.SnakyRows010.named_envelope_593_20_last
def Internal.SnakyRows010.named_envelope_593_22 : List Cell := ([(3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_593_22_chain : (named_envelope_593_22.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_593_22_head : (named_envelope_593_22.map Internal.SnakyRows010.namedCellKey).head? = some (388 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_593_22_last : (named_envelope_593_22.map Internal.SnakyRows010.namedCellKey).getLast? = some (510 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_593_23 : List Cell := ([(4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, -4), (5, -3), (5, -2)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_593_23_chain : (named_envelope_593_23.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_593_23_head : (named_envelope_593_23.map Internal.SnakyRows010.namedCellKey).head? = some (511 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_593_23_last : (named_envelope_593_23.map Internal.SnakyRows010.namedCellKey).getLast? = some (638 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_593_21 : List Cell := Internal.SnakyRows010.named_envelope_593_22 ++ Internal.SnakyRows010.named_envelope_593_23
theorem Internal.SnakyRows010.named_envelope_593_21_chain : (named_envelope_593_21.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_593_22 Internal.SnakyRows010.named_envelope_593_23 (510 : ℤ) (511 : ℤ)
    Internal.SnakyRows010.named_envelope_593_22_chain Internal.SnakyRows010.named_envelope_593_23_chain Internal.SnakyRows010.named_envelope_593_22_last Internal.SnakyRows010.named_envelope_593_23_head (by decide)
theorem Internal.SnakyRows010.named_envelope_593_21_head : (named_envelope_593_21.map Internal.SnakyRows010.namedCellKey).head? = some (388 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_593_22 Internal.SnakyRows010.named_envelope_593_23 (388 : ℤ) Internal.SnakyRows010.named_envelope_593_22_head
theorem Internal.SnakyRows010.named_envelope_593_21_last : (named_envelope_593_21.map Internal.SnakyRows010.namedCellKey).getLast? = some (638 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_593_22 Internal.SnakyRows010.named_envelope_593_23 (638 : ℤ) Internal.SnakyRows010.named_envelope_593_23_last
def Internal.SnakyRows010.named_envelope_593_17 : List Cell := Internal.SnakyRows010.named_envelope_593_18 ++ Internal.SnakyRows010.named_envelope_593_21
theorem Internal.SnakyRows010.named_envelope_593_17_chain : (named_envelope_593_17.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_593_18 Internal.SnakyRows010.named_envelope_593_21 (387 : ℤ) (388 : ℤ)
    Internal.SnakyRows010.named_envelope_593_18_chain Internal.SnakyRows010.named_envelope_593_21_chain Internal.SnakyRows010.named_envelope_593_18_last Internal.SnakyRows010.named_envelope_593_21_head (by decide)
theorem Internal.SnakyRows010.named_envelope_593_17_head : (named_envelope_593_17.map Internal.SnakyRows010.namedCellKey).head? = some (251 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_593_18 Internal.SnakyRows010.named_envelope_593_21 (251 : ℤ) Internal.SnakyRows010.named_envelope_593_18_head
theorem Internal.SnakyRows010.named_envelope_593_17_last : (named_envelope_593_17.map Internal.SnakyRows010.namedCellKey).getLast? = some (638 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_593_18 Internal.SnakyRows010.named_envelope_593_21 (638 : ℤ) Internal.SnakyRows010.named_envelope_593_21_last
def Internal.SnakyRows010.named_envelope_593_26 : List Cell := ([(5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, -4), (6, -3), (6, -2)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_593_26_chain : (named_envelope_593_26.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_593_26_head : (named_envelope_593_26.map Internal.SnakyRows010.namedCellKey).head? = some (639 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_593_26_last : (named_envelope_593_26.map Internal.SnakyRows010.namedCellKey).getLast? = some (766 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_593_27 : List Cell := ([(6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, -4), (7, -3), (7, -2), (7, -1)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_593_27_chain : (named_envelope_593_27.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_593_27_head : (named_envelope_593_27.map Internal.SnakyRows010.namedCellKey).head? = some (767 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_593_27_last : (named_envelope_593_27.map Internal.SnakyRows010.namedCellKey).getLast? = some (895 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_593_25 : List Cell := Internal.SnakyRows010.named_envelope_593_26 ++ Internal.SnakyRows010.named_envelope_593_27
theorem Internal.SnakyRows010.named_envelope_593_25_chain : (named_envelope_593_25.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_593_26 Internal.SnakyRows010.named_envelope_593_27 (766 : ℤ) (767 : ℤ)
    Internal.SnakyRows010.named_envelope_593_26_chain Internal.SnakyRows010.named_envelope_593_27_chain Internal.SnakyRows010.named_envelope_593_26_last Internal.SnakyRows010.named_envelope_593_27_head (by decide)
theorem Internal.SnakyRows010.named_envelope_593_25_head : (named_envelope_593_25.map Internal.SnakyRows010.namedCellKey).head? = some (639 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_593_26 Internal.SnakyRows010.named_envelope_593_27 (639 : ℤ) Internal.SnakyRows010.named_envelope_593_26_head
theorem Internal.SnakyRows010.named_envelope_593_25_last : (named_envelope_593_25.map Internal.SnakyRows010.namedCellKey).getLast? = some (895 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_593_26 Internal.SnakyRows010.named_envelope_593_27 (895 : ℤ) Internal.SnakyRows010.named_envelope_593_27_last
def Internal.SnakyRows010.named_envelope_593_29 : List Cell := ([(7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_593_29_chain : (named_envelope_593_29.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_593_29_head : (named_envelope_593_29.map Internal.SnakyRows010.namedCellKey).head? = some (896 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_593_29_last : (named_envelope_593_29.map Internal.SnakyRows010.namedCellKey).getLast? = some (1028 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_593_30 : List Cell := ([(8, 5), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (10, -1), (10, 0), (10, 1), (11, -1), (11, 1)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_593_30_chain : (named_envelope_593_30.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_593_30_head : (named_envelope_593_30.map Internal.SnakyRows010.namedCellKey).head? = some (1029 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_593_30_last : (named_envelope_593_30.map Internal.SnakyRows010.namedCellKey).getLast? = some (1409 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_593_28 : List Cell := Internal.SnakyRows010.named_envelope_593_29 ++ Internal.SnakyRows010.named_envelope_593_30
theorem Internal.SnakyRows010.named_envelope_593_28_chain : (named_envelope_593_28.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_593_29 Internal.SnakyRows010.named_envelope_593_30 (1028 : ℤ) (1029 : ℤ)
    Internal.SnakyRows010.named_envelope_593_29_chain Internal.SnakyRows010.named_envelope_593_30_chain Internal.SnakyRows010.named_envelope_593_29_last Internal.SnakyRows010.named_envelope_593_30_head (by decide)
theorem Internal.SnakyRows010.named_envelope_593_28_head : (named_envelope_593_28.map Internal.SnakyRows010.namedCellKey).head? = some (896 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_593_29 Internal.SnakyRows010.named_envelope_593_30 (896 : ℤ) Internal.SnakyRows010.named_envelope_593_29_head
theorem Internal.SnakyRows010.named_envelope_593_28_last : (named_envelope_593_28.map Internal.SnakyRows010.namedCellKey).getLast? = some (1409 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_593_29 Internal.SnakyRows010.named_envelope_593_30 (1409 : ℤ) Internal.SnakyRows010.named_envelope_593_30_last
def Internal.SnakyRows010.named_envelope_593_24 : List Cell := Internal.SnakyRows010.named_envelope_593_25 ++ Internal.SnakyRows010.named_envelope_593_28
theorem Internal.SnakyRows010.named_envelope_593_24_chain : (named_envelope_593_24.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_593_25 Internal.SnakyRows010.named_envelope_593_28 (895 : ℤ) (896 : ℤ)
    Internal.SnakyRows010.named_envelope_593_25_chain Internal.SnakyRows010.named_envelope_593_28_chain Internal.SnakyRows010.named_envelope_593_25_last Internal.SnakyRows010.named_envelope_593_28_head (by decide)
theorem Internal.SnakyRows010.named_envelope_593_24_head : (named_envelope_593_24.map Internal.SnakyRows010.namedCellKey).head? = some (639 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_593_25 Internal.SnakyRows010.named_envelope_593_28 (639 : ℤ) Internal.SnakyRows010.named_envelope_593_25_head
theorem Internal.SnakyRows010.named_envelope_593_24_last : (named_envelope_593_24.map Internal.SnakyRows010.namedCellKey).getLast? = some (1409 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_593_25 Internal.SnakyRows010.named_envelope_593_28 (1409 : ℤ) Internal.SnakyRows010.named_envelope_593_28_last
def Internal.SnakyRows010.named_envelope_593_16 : List Cell := Internal.SnakyRows010.named_envelope_593_17 ++ Internal.SnakyRows010.named_envelope_593_24
theorem Internal.SnakyRows010.named_envelope_593_16_chain : (named_envelope_593_16.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_593_17 Internal.SnakyRows010.named_envelope_593_24 (638 : ℤ) (639 : ℤ)
    Internal.SnakyRows010.named_envelope_593_17_chain Internal.SnakyRows010.named_envelope_593_24_chain Internal.SnakyRows010.named_envelope_593_17_last Internal.SnakyRows010.named_envelope_593_24_head (by decide)
theorem Internal.SnakyRows010.named_envelope_593_16_head : (named_envelope_593_16.map Internal.SnakyRows010.namedCellKey).head? = some (251 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_593_17 Internal.SnakyRows010.named_envelope_593_24 (251 : ℤ) Internal.SnakyRows010.named_envelope_593_17_head
theorem Internal.SnakyRows010.named_envelope_593_16_last : (named_envelope_593_16.map Internal.SnakyRows010.namedCellKey).getLast? = some (1409 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_593_17 Internal.SnakyRows010.named_envelope_593_24 (1409 : ℤ) Internal.SnakyRows010.named_envelope_593_24_last
def Internal.SnakyRows010.named_envelope_593_0 : List Cell := Internal.SnakyRows010.named_envelope_593_1 ++ Internal.SnakyRows010.named_envelope_593_16
theorem Internal.SnakyRows010.named_envelope_593_0_chain : (named_envelope_593_0.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_593_1 Internal.SnakyRows010.named_envelope_593_16 (250 : ℤ) (251 : ℤ)
    Internal.SnakyRows010.named_envelope_593_1_chain Internal.SnakyRows010.named_envelope_593_16_chain Internal.SnakyRows010.named_envelope_593_1_last Internal.SnakyRows010.named_envelope_593_16_head (by decide)
theorem Internal.SnakyRows010.named_envelope_593_0_head : (named_envelope_593_0.map Internal.SnakyRows010.namedCellKey).head? = some (-892 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_593_1 Internal.SnakyRows010.named_envelope_593_16 (-892 : ℤ) Internal.SnakyRows010.named_envelope_593_1_head
theorem Internal.SnakyRows010.named_envelope_593_0_last : (named_envelope_593_0.map Internal.SnakyRows010.namedCellKey).getLast? = some (1409 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_593_1 Internal.SnakyRows010.named_envelope_593_16 (1409 : ℤ) Internal.SnakyRows010.named_envelope_593_16_last
theorem Internal.SnakyRows010.named_envelope_593_nodup : (Internal.SnakyRows010.named_envelope_593_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows010.named_nodup_of_chain Internal.SnakyRows010.named_envelope_593_0 Internal.SnakyRows010.named_envelope_593_0_chain
def envelope_593 : Finset Cell := ⟨(Internal.SnakyRows010.named_envelope_593_0 : Multiset Cell), Internal.SnakyRows010.named_envelope_593_nodup⟩
def childrenC_593 : Fin 2 → Finset Cell := ![(placedSet 7 (0, -2) required_2), (placedSet 0 (0, 1) required_586)]
def childrenD_593 : Fin 2 → Finset Cell := ![(placedSet 7 (0, -2) envelope_2), (placedSet 0 (0, 1) envelope_586)]
theorem common_sub_593 : commonEnvelope childrenD_593 ⊆ insert (0, 0) required_593 := by decide
theorem child_required_sub_593 : ∀ j, childrenC_593 j ⊆ insert (0, 0) required_593 := by decide
theorem Internal.SnakyRows010.containment_593_0 :
    placedSet 7 (0, -2) envelope_2 ⊆ envelope_593 := by decide
theorem Internal.SnakyRows010.containment_593_1 :
    placedSet 0 (0, 1) envelope_586 ⊆ envelope_593 := by decide +kernel
theorem child_envelope_sub_593 : ∀ j, childrenD_593 j ⊆ envelope_593 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows010.containment_593_0
  · exact Internal.SnakyRows010.containment_593_1
theorem pivot_mem_593 : (0, 0) ∈ envelope_593 := by decide
theorem children_work_593 : ∀ j, Template HasSnaky 26 (childrenC_593 j) (childrenD_593 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_2 7 (0, -2)).mono (by decide)
  · exact (placed_template_map row_works_586 0 (0, 1)).mono (by decide)
theorem row_works_593 : Template HasSnaky 27 required_593 envelope_593 := by
  refine compose HasSnaky 26 childrenC_593 childrenD_593 children_work_593 (0, 0)
    required_593 envelope_593 pivot_mem_593 child_required_sub_593 child_envelope_sub_593 ?_
  intro b hb; exact common_sub_593 (mem_commonEnvelope childrenD_593 b hb)
end SnakyConditional

end OAI
