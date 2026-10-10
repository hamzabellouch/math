import OAI.GameTheory.SnakyConditional.Templates.Level29Part02

namespace OAI

namespace SnakyConditional
def required_594 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (-1, -1)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows010.named_envelope_594_4 : List Cell := ([(-7, 5), (-7, 6), (-7, 8), (-6, 3), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_594_4_chain : (named_envelope_594_4.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_594_4_head : (named_envelope_594_4.map Internal.SnakyRows010.namedCellKey).head? = some (-891 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_594_4_last : (named_envelope_594_4.map Internal.SnakyRows010.namedCellKey).getLast? = some (-635 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_594_5 : List Cell := ([(-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_594_5_chain : (named_envelope_594_5.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_594_5_head : (named_envelope_594_5.map Internal.SnakyRows010.namedCellKey).head? = some (-634 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_594_5_last : (named_envelope_594_5.map Internal.SnakyRows010.namedCellKey).getLast? = some (-505 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_594_3 : List Cell := Internal.SnakyRows010.named_envelope_594_4 ++ Internal.SnakyRows010.named_envelope_594_5
theorem Internal.SnakyRows010.named_envelope_594_3_chain : (named_envelope_594_3.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_594_4 Internal.SnakyRows010.named_envelope_594_5 (-635 : ℤ) (-634 : ℤ)
    Internal.SnakyRows010.named_envelope_594_4_chain Internal.SnakyRows010.named_envelope_594_5_chain Internal.SnakyRows010.named_envelope_594_4_last Internal.SnakyRows010.named_envelope_594_5_head (by decide)
theorem Internal.SnakyRows010.named_envelope_594_3_head : (named_envelope_594_3.map Internal.SnakyRows010.namedCellKey).head? = some (-891 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_594_4 Internal.SnakyRows010.named_envelope_594_5 (-891 : ℤ) Internal.SnakyRows010.named_envelope_594_4_head
theorem Internal.SnakyRows010.named_envelope_594_3_last : (named_envelope_594_3.map Internal.SnakyRows010.namedCellKey).getLast? = some (-505 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_594_4 Internal.SnakyRows010.named_envelope_594_5 (-505 : ℤ) Internal.SnakyRows010.named_envelope_594_5_last
def Internal.SnakyRows010.named_envelope_594_7 : List Cell := ([(-4, 8), (-4, 9), (-4, 10), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_594_7_chain : (named_envelope_594_7.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_594_7_head : (named_envelope_594_7.map Internal.SnakyRows010.namedCellKey).head? = some (-504 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_594_7_last : (named_envelope_594_7.map Internal.SnakyRows010.namedCellKey).getLast? = some (-374 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_594_8 : List Cell := ([(-3, 11), (-3, 12), (-3, 13), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_594_8_chain : (named_envelope_594_8.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_594_8_head : (named_envelope_594_8.map Internal.SnakyRows010.namedCellKey).head? = some (-373 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_594_8_last : (named_envelope_594_8.map Internal.SnakyRows010.namedCellKey).getLast? = some (-246 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_594_6 : List Cell := Internal.SnakyRows010.named_envelope_594_7 ++ Internal.SnakyRows010.named_envelope_594_8
theorem Internal.SnakyRows010.named_envelope_594_6_chain : (named_envelope_594_6.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_594_7 Internal.SnakyRows010.named_envelope_594_8 (-374 : ℤ) (-373 : ℤ)
    Internal.SnakyRows010.named_envelope_594_7_chain Internal.SnakyRows010.named_envelope_594_8_chain Internal.SnakyRows010.named_envelope_594_7_last Internal.SnakyRows010.named_envelope_594_8_head (by decide)
theorem Internal.SnakyRows010.named_envelope_594_6_head : (named_envelope_594_6.map Internal.SnakyRows010.namedCellKey).head? = some (-504 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_594_7 Internal.SnakyRows010.named_envelope_594_8 (-504 : ℤ) Internal.SnakyRows010.named_envelope_594_7_head
theorem Internal.SnakyRows010.named_envelope_594_6_last : (named_envelope_594_6.map Internal.SnakyRows010.namedCellKey).getLast? = some (-246 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_594_7 Internal.SnakyRows010.named_envelope_594_8 (-246 : ℤ) Internal.SnakyRows010.named_envelope_594_8_last
def Internal.SnakyRows010.named_envelope_594_2 : List Cell := Internal.SnakyRows010.named_envelope_594_3 ++ Internal.SnakyRows010.named_envelope_594_6
theorem Internal.SnakyRows010.named_envelope_594_2_chain : (named_envelope_594_2.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_594_3 Internal.SnakyRows010.named_envelope_594_6 (-505 : ℤ) (-504 : ℤ)
    Internal.SnakyRows010.named_envelope_594_3_chain Internal.SnakyRows010.named_envelope_594_6_chain Internal.SnakyRows010.named_envelope_594_3_last Internal.SnakyRows010.named_envelope_594_6_head (by decide)
theorem Internal.SnakyRows010.named_envelope_594_2_head : (named_envelope_594_2.map Internal.SnakyRows010.namedCellKey).head? = some (-891 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_594_3 Internal.SnakyRows010.named_envelope_594_6 (-891 : ℤ) Internal.SnakyRows010.named_envelope_594_3_head
theorem Internal.SnakyRows010.named_envelope_594_2_last : (named_envelope_594_2.map Internal.SnakyRows010.namedCellKey).getLast? = some (-246 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_594_3 Internal.SnakyRows010.named_envelope_594_6 (-246 : ℤ) Internal.SnakyRows010.named_envelope_594_6_last
def Internal.SnakyRows010.named_envelope_594_11 : List Cell := ([(-2, 11), (-2, 12), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_594_11_chain : (named_envelope_594_11.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_594_11_head : (named_envelope_594_11.map Internal.SnakyRows010.namedCellKey).head? = some (-245 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_594_11_last : (named_envelope_594_11.map Internal.SnakyRows010.namedCellKey).getLast? = some (-122 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_594_12 : List Cell := ([(-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_594_12_chain : (named_envelope_594_12.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_594_12_head : (named_envelope_594_12.map Internal.SnakyRows010.namedCellKey).head? = some (-121 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_594_12_last : (named_envelope_594_12.map Internal.SnakyRows010.namedCellKey).getLast? = some (3 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_594_10 : List Cell := Internal.SnakyRows010.named_envelope_594_11 ++ Internal.SnakyRows010.named_envelope_594_12
theorem Internal.SnakyRows010.named_envelope_594_10_chain : (named_envelope_594_10.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_594_11 Internal.SnakyRows010.named_envelope_594_12 (-122 : ℤ) (-121 : ℤ)
    Internal.SnakyRows010.named_envelope_594_11_chain Internal.SnakyRows010.named_envelope_594_12_chain Internal.SnakyRows010.named_envelope_594_11_last Internal.SnakyRows010.named_envelope_594_12_head (by decide)
theorem Internal.SnakyRows010.named_envelope_594_10_head : (named_envelope_594_10.map Internal.SnakyRows010.namedCellKey).head? = some (-245 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_594_11 Internal.SnakyRows010.named_envelope_594_12 (-245 : ℤ) Internal.SnakyRows010.named_envelope_594_11_head
theorem Internal.SnakyRows010.named_envelope_594_10_last : (named_envelope_594_10.map Internal.SnakyRows010.namedCellKey).getLast? = some (3 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_594_11 Internal.SnakyRows010.named_envelope_594_12 (3 : ℤ) Internal.SnakyRows010.named_envelope_594_12_last
def Internal.SnakyRows010.named_envelope_594_14 : List Cell := ([(0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_594_14_chain : (named_envelope_594_14.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_594_14_head : (named_envelope_594_14.map Internal.SnakyRows010.namedCellKey).head? = some (4 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_594_14_last : (named_envelope_594_14.map Internal.SnakyRows010.namedCellKey).getLast? = some (126 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_594_15 : List Cell := ([(1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -5)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_594_15_chain : (named_envelope_594_15.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_594_15_head : (named_envelope_594_15.map Internal.SnakyRows010.namedCellKey).head? = some (127 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_594_15_last : (named_envelope_594_15.map Internal.SnakyRows010.namedCellKey).getLast? = some (251 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_594_13 : List Cell := Internal.SnakyRows010.named_envelope_594_14 ++ Internal.SnakyRows010.named_envelope_594_15
theorem Internal.SnakyRows010.named_envelope_594_13_chain : (named_envelope_594_13.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_594_14 Internal.SnakyRows010.named_envelope_594_15 (126 : ℤ) (127 : ℤ)
    Internal.SnakyRows010.named_envelope_594_14_chain Internal.SnakyRows010.named_envelope_594_15_chain Internal.SnakyRows010.named_envelope_594_14_last Internal.SnakyRows010.named_envelope_594_15_head (by decide)
theorem Internal.SnakyRows010.named_envelope_594_13_head : (named_envelope_594_13.map Internal.SnakyRows010.namedCellKey).head? = some (4 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_594_14 Internal.SnakyRows010.named_envelope_594_15 (4 : ℤ) Internal.SnakyRows010.named_envelope_594_14_head
theorem Internal.SnakyRows010.named_envelope_594_13_last : (named_envelope_594_13.map Internal.SnakyRows010.namedCellKey).getLast? = some (251 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_594_14 Internal.SnakyRows010.named_envelope_594_15 (251 : ℤ) Internal.SnakyRows010.named_envelope_594_15_last
def Internal.SnakyRows010.named_envelope_594_9 : List Cell := Internal.SnakyRows010.named_envelope_594_10 ++ Internal.SnakyRows010.named_envelope_594_13
theorem Internal.SnakyRows010.named_envelope_594_9_chain : (named_envelope_594_9.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_594_10 Internal.SnakyRows010.named_envelope_594_13 (3 : ℤ) (4 : ℤ)
    Internal.SnakyRows010.named_envelope_594_10_chain Internal.SnakyRows010.named_envelope_594_13_chain Internal.SnakyRows010.named_envelope_594_10_last Internal.SnakyRows010.named_envelope_594_13_head (by decide)
theorem Internal.SnakyRows010.named_envelope_594_9_head : (named_envelope_594_9.map Internal.SnakyRows010.namedCellKey).head? = some (-245 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_594_10 Internal.SnakyRows010.named_envelope_594_13 (-245 : ℤ) Internal.SnakyRows010.named_envelope_594_10_head
theorem Internal.SnakyRows010.named_envelope_594_9_last : (named_envelope_594_9.map Internal.SnakyRows010.namedCellKey).getLast? = some (251 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_594_10 Internal.SnakyRows010.named_envelope_594_13 (251 : ℤ) Internal.SnakyRows010.named_envelope_594_13_last
def Internal.SnakyRows010.named_envelope_594_1 : List Cell := Internal.SnakyRows010.named_envelope_594_2 ++ Internal.SnakyRows010.named_envelope_594_9
theorem Internal.SnakyRows010.named_envelope_594_1_chain : (named_envelope_594_1.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_594_2 Internal.SnakyRows010.named_envelope_594_9 (-246 : ℤ) (-245 : ℤ)
    Internal.SnakyRows010.named_envelope_594_2_chain Internal.SnakyRows010.named_envelope_594_9_chain Internal.SnakyRows010.named_envelope_594_2_last Internal.SnakyRows010.named_envelope_594_9_head (by decide)
theorem Internal.SnakyRows010.named_envelope_594_1_head : (named_envelope_594_1.map Internal.SnakyRows010.namedCellKey).head? = some (-891 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_594_2 Internal.SnakyRows010.named_envelope_594_9 (-891 : ℤ) Internal.SnakyRows010.named_envelope_594_2_head
theorem Internal.SnakyRows010.named_envelope_594_1_last : (named_envelope_594_1.map Internal.SnakyRows010.namedCellKey).getLast? = some (251 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_594_2 Internal.SnakyRows010.named_envelope_594_9 (251 : ℤ) Internal.SnakyRows010.named_envelope_594_9_last
def Internal.SnakyRows010.named_envelope_594_19 : List Cell := ([(2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_594_19_chain : (named_envelope_594_19.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_594_19_head : (named_envelope_594_19.map Internal.SnakyRows010.namedCellKey).head? = some (252 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_594_19_last : (named_envelope_594_19.map Internal.SnakyRows010.namedCellKey).getLast? = some (264 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_594_20 : List Cell := ([(2, 9), (2, 10), (2, 11), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_594_20_chain : (named_envelope_594_20.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_594_20_head : (named_envelope_594_20.map Internal.SnakyRows010.namedCellKey).head? = some (265 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_594_20_last : (named_envelope_594_20.map Internal.SnakyRows010.namedCellKey).getLast? = some (387 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_594_18 : List Cell := Internal.SnakyRows010.named_envelope_594_19 ++ Internal.SnakyRows010.named_envelope_594_20
theorem Internal.SnakyRows010.named_envelope_594_18_chain : (named_envelope_594_18.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_594_19 Internal.SnakyRows010.named_envelope_594_20 (264 : ℤ) (265 : ℤ)
    Internal.SnakyRows010.named_envelope_594_19_chain Internal.SnakyRows010.named_envelope_594_20_chain Internal.SnakyRows010.named_envelope_594_19_last Internal.SnakyRows010.named_envelope_594_20_head (by decide)
theorem Internal.SnakyRows010.named_envelope_594_18_head : (named_envelope_594_18.map Internal.SnakyRows010.namedCellKey).head? = some (252 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_594_19 Internal.SnakyRows010.named_envelope_594_20 (252 : ℤ) Internal.SnakyRows010.named_envelope_594_19_head
theorem Internal.SnakyRows010.named_envelope_594_18_last : (named_envelope_594_18.map Internal.SnakyRows010.namedCellKey).getLast? = some (387 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_594_19 Internal.SnakyRows010.named_envelope_594_20 (387 : ℤ) Internal.SnakyRows010.named_envelope_594_20_last
def Internal.SnakyRows010.named_envelope_594_22 : List Cell := ([(3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_594_22_chain : (named_envelope_594_22.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_594_22_head : (named_envelope_594_22.map Internal.SnakyRows010.namedCellKey).head? = some (388 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_594_22_last : (named_envelope_594_22.map Internal.SnakyRows010.namedCellKey).getLast? = some (511 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_594_23 : List Cell := ([(4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -4), (5, -3), (5, -2), (5, -1)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_594_23_chain : (named_envelope_594_23.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_594_23_head : (named_envelope_594_23.map Internal.SnakyRows010.namedCellKey).head? = some (512 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_594_23_last : (named_envelope_594_23.map Internal.SnakyRows010.namedCellKey).getLast? = some (639 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_594_21 : List Cell := Internal.SnakyRows010.named_envelope_594_22 ++ Internal.SnakyRows010.named_envelope_594_23
theorem Internal.SnakyRows010.named_envelope_594_21_chain : (named_envelope_594_21.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_594_22 Internal.SnakyRows010.named_envelope_594_23 (511 : ℤ) (512 : ℤ)
    Internal.SnakyRows010.named_envelope_594_22_chain Internal.SnakyRows010.named_envelope_594_23_chain Internal.SnakyRows010.named_envelope_594_22_last Internal.SnakyRows010.named_envelope_594_23_head (by decide)
theorem Internal.SnakyRows010.named_envelope_594_21_head : (named_envelope_594_21.map Internal.SnakyRows010.namedCellKey).head? = some (388 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_594_22 Internal.SnakyRows010.named_envelope_594_23 (388 : ℤ) Internal.SnakyRows010.named_envelope_594_22_head
theorem Internal.SnakyRows010.named_envelope_594_21_last : (named_envelope_594_21.map Internal.SnakyRows010.namedCellKey).getLast? = some (639 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_594_22 Internal.SnakyRows010.named_envelope_594_23 (639 : ℤ) Internal.SnakyRows010.named_envelope_594_23_last
def Internal.SnakyRows010.named_envelope_594_17 : List Cell := Internal.SnakyRows010.named_envelope_594_18 ++ Internal.SnakyRows010.named_envelope_594_21
theorem Internal.SnakyRows010.named_envelope_594_17_chain : (named_envelope_594_17.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_594_18 Internal.SnakyRows010.named_envelope_594_21 (387 : ℤ) (388 : ℤ)
    Internal.SnakyRows010.named_envelope_594_18_chain Internal.SnakyRows010.named_envelope_594_21_chain Internal.SnakyRows010.named_envelope_594_18_last Internal.SnakyRows010.named_envelope_594_21_head (by decide)
theorem Internal.SnakyRows010.named_envelope_594_17_head : (named_envelope_594_17.map Internal.SnakyRows010.namedCellKey).head? = some (252 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_594_18 Internal.SnakyRows010.named_envelope_594_21 (252 : ℤ) Internal.SnakyRows010.named_envelope_594_18_head
theorem Internal.SnakyRows010.named_envelope_594_17_last : (named_envelope_594_17.map Internal.SnakyRows010.namedCellKey).getLast? = some (639 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_594_18 Internal.SnakyRows010.named_envelope_594_21 (639 : ℤ) Internal.SnakyRows010.named_envelope_594_21_last
def Internal.SnakyRows010.named_envelope_594_26 : List Cell := ([(5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, -4), (6, -3), (6, -2), (6, -1)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_594_26_chain : (named_envelope_594_26.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_594_26_head : (named_envelope_594_26.map Internal.SnakyRows010.namedCellKey).head? = some (640 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_594_26_last : (named_envelope_594_26.map Internal.SnakyRows010.namedCellKey).getLast? = some (767 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_594_27 : List Cell := ([(6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_594_27_chain : (named_envelope_594_27.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_594_27_head : (named_envelope_594_27.map Internal.SnakyRows010.namedCellKey).head? = some (768 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_594_27_last : (named_envelope_594_27.map Internal.SnakyRows010.namedCellKey).getLast? = some (897 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_594_25 : List Cell := Internal.SnakyRows010.named_envelope_594_26 ++ Internal.SnakyRows010.named_envelope_594_27
theorem Internal.SnakyRows010.named_envelope_594_25_chain : (named_envelope_594_25.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_594_26 Internal.SnakyRows010.named_envelope_594_27 (767 : ℤ) (768 : ℤ)
    Internal.SnakyRows010.named_envelope_594_26_chain Internal.SnakyRows010.named_envelope_594_27_chain Internal.SnakyRows010.named_envelope_594_26_last Internal.SnakyRows010.named_envelope_594_27_head (by decide)
theorem Internal.SnakyRows010.named_envelope_594_25_head : (named_envelope_594_25.map Internal.SnakyRows010.namedCellKey).head? = some (640 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_594_26 Internal.SnakyRows010.named_envelope_594_27 (640 : ℤ) Internal.SnakyRows010.named_envelope_594_26_head
theorem Internal.SnakyRows010.named_envelope_594_25_last : (named_envelope_594_25.map Internal.SnakyRows010.namedCellKey).getLast? = some (897 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_594_26 Internal.SnakyRows010.named_envelope_594_27 (897 : ℤ) Internal.SnakyRows010.named_envelope_594_27_last
def Internal.SnakyRows010.named_envelope_594_29 : List Cell := ([(7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, -3), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_594_29_chain : (named_envelope_594_29.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_594_29_head : (named_envelope_594_29.map Internal.SnakyRows010.namedCellKey).head? = some (898 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_594_29_last : (named_envelope_594_29.map Internal.SnakyRows010.namedCellKey).getLast? = some (1028 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_594_30 : List Cell := ([(8, 5), (8, 6), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (10, 0), (10, 1), (10, 2), (11, 0), (11, 2)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_594_30_chain : (named_envelope_594_30.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_594_30_head : (named_envelope_594_30.map Internal.SnakyRows010.namedCellKey).head? = some (1029 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_594_30_last : (named_envelope_594_30.map Internal.SnakyRows010.namedCellKey).getLast? = some (1410 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_594_28 : List Cell := Internal.SnakyRows010.named_envelope_594_29 ++ Internal.SnakyRows010.named_envelope_594_30
theorem Internal.SnakyRows010.named_envelope_594_28_chain : (named_envelope_594_28.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_594_29 Internal.SnakyRows010.named_envelope_594_30 (1028 : ℤ) (1029 : ℤ)
    Internal.SnakyRows010.named_envelope_594_29_chain Internal.SnakyRows010.named_envelope_594_30_chain Internal.SnakyRows010.named_envelope_594_29_last Internal.SnakyRows010.named_envelope_594_30_head (by decide)
theorem Internal.SnakyRows010.named_envelope_594_28_head : (named_envelope_594_28.map Internal.SnakyRows010.namedCellKey).head? = some (898 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_594_29 Internal.SnakyRows010.named_envelope_594_30 (898 : ℤ) Internal.SnakyRows010.named_envelope_594_29_head
theorem Internal.SnakyRows010.named_envelope_594_28_last : (named_envelope_594_28.map Internal.SnakyRows010.namedCellKey).getLast? = some (1410 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_594_29 Internal.SnakyRows010.named_envelope_594_30 (1410 : ℤ) Internal.SnakyRows010.named_envelope_594_30_last
def Internal.SnakyRows010.named_envelope_594_24 : List Cell := Internal.SnakyRows010.named_envelope_594_25 ++ Internal.SnakyRows010.named_envelope_594_28
theorem Internal.SnakyRows010.named_envelope_594_24_chain : (named_envelope_594_24.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_594_25 Internal.SnakyRows010.named_envelope_594_28 (897 : ℤ) (898 : ℤ)
    Internal.SnakyRows010.named_envelope_594_25_chain Internal.SnakyRows010.named_envelope_594_28_chain Internal.SnakyRows010.named_envelope_594_25_last Internal.SnakyRows010.named_envelope_594_28_head (by decide)
theorem Internal.SnakyRows010.named_envelope_594_24_head : (named_envelope_594_24.map Internal.SnakyRows010.namedCellKey).head? = some (640 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_594_25 Internal.SnakyRows010.named_envelope_594_28 (640 : ℤ) Internal.SnakyRows010.named_envelope_594_25_head
theorem Internal.SnakyRows010.named_envelope_594_24_last : (named_envelope_594_24.map Internal.SnakyRows010.namedCellKey).getLast? = some (1410 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_594_25 Internal.SnakyRows010.named_envelope_594_28 (1410 : ℤ) Internal.SnakyRows010.named_envelope_594_28_last
def Internal.SnakyRows010.named_envelope_594_16 : List Cell := Internal.SnakyRows010.named_envelope_594_17 ++ Internal.SnakyRows010.named_envelope_594_24
theorem Internal.SnakyRows010.named_envelope_594_16_chain : (named_envelope_594_16.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_594_17 Internal.SnakyRows010.named_envelope_594_24 (639 : ℤ) (640 : ℤ)
    Internal.SnakyRows010.named_envelope_594_17_chain Internal.SnakyRows010.named_envelope_594_24_chain Internal.SnakyRows010.named_envelope_594_17_last Internal.SnakyRows010.named_envelope_594_24_head (by decide)
theorem Internal.SnakyRows010.named_envelope_594_16_head : (named_envelope_594_16.map Internal.SnakyRows010.namedCellKey).head? = some (252 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_594_17 Internal.SnakyRows010.named_envelope_594_24 (252 : ℤ) Internal.SnakyRows010.named_envelope_594_17_head
theorem Internal.SnakyRows010.named_envelope_594_16_last : (named_envelope_594_16.map Internal.SnakyRows010.namedCellKey).getLast? = some (1410 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_594_17 Internal.SnakyRows010.named_envelope_594_24 (1410 : ℤ) Internal.SnakyRows010.named_envelope_594_24_last
def Internal.SnakyRows010.named_envelope_594_0 : List Cell := Internal.SnakyRows010.named_envelope_594_1 ++ Internal.SnakyRows010.named_envelope_594_16
theorem Internal.SnakyRows010.named_envelope_594_0_chain : (named_envelope_594_0.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_594_1 Internal.SnakyRows010.named_envelope_594_16 (251 : ℤ) (252 : ℤ)
    Internal.SnakyRows010.named_envelope_594_1_chain Internal.SnakyRows010.named_envelope_594_16_chain Internal.SnakyRows010.named_envelope_594_1_last Internal.SnakyRows010.named_envelope_594_16_head (by decide)
theorem Internal.SnakyRows010.named_envelope_594_0_head : (named_envelope_594_0.map Internal.SnakyRows010.namedCellKey).head? = some (-891 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_594_1 Internal.SnakyRows010.named_envelope_594_16 (-891 : ℤ) Internal.SnakyRows010.named_envelope_594_1_head
theorem Internal.SnakyRows010.named_envelope_594_0_last : (named_envelope_594_0.map Internal.SnakyRows010.namedCellKey).getLast? = some (1410 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_594_1 Internal.SnakyRows010.named_envelope_594_16 (1410 : ℤ) Internal.SnakyRows010.named_envelope_594_16_last
theorem Internal.SnakyRows010.named_envelope_594_nodup : (Internal.SnakyRows010.named_envelope_594_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows010.named_nodup_of_chain Internal.SnakyRows010.named_envelope_594_0 Internal.SnakyRows010.named_envelope_594_0_chain
def envelope_594 : Finset Cell := ⟨(Internal.SnakyRows010.named_envelope_594_0 : Multiset Cell), Internal.SnakyRows010.named_envelope_594_nodup⟩
def childrenC_594 : Fin 3 → Finset Cell := ![(placedSet 1 (0, -1) required_30), (placedSet 1 (0, -1) required_476), (placedSet 0 (0, 1) required_588)]
def childrenD_594 : Fin 3 → Finset Cell := ![(placedSet 1 (0, -1) envelope_30), (placedSet 1 (0, -1) envelope_476), (placedSet 0 (0, 1) envelope_588)]
theorem common_sub_594 : commonEnvelope childrenD_594 ⊆ insert (0, 0) required_594 := by decide
theorem child_required_sub_594 : ∀ j, childrenC_594 j ⊆ insert (0, 0) required_594 := by decide
theorem Internal.SnakyRows010.containment_594_0 :
    placedSet 1 (0, -1) envelope_30 ⊆ envelope_594 := by decide
theorem Internal.SnakyRows010.containment_594_1 :
    placedSet 1 (0, -1) envelope_476 ⊆ envelope_594 := by decide +kernel
theorem Internal.SnakyRows010.containment_594_2 :
    placedSet 0 (0, 1) envelope_588 ⊆ envelope_594 := by decide +kernel
theorem child_envelope_sub_594 : ∀ j, childrenD_594 j ⊆ envelope_594 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows010.containment_594_0
  · exact Internal.SnakyRows010.containment_594_1
  · exact Internal.SnakyRows010.containment_594_2
theorem pivot_mem_594 : (0, 0) ∈ envelope_594 := by decide
theorem children_work_594 : ∀ j, Template HasSnaky 27 (childrenC_594 j) (childrenD_594 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_30 1 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_476 1 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_588 0 (0, 1)).mono (by decide)
theorem row_works_594 : Template HasSnaky 28 required_594 envelope_594 := by
  refine compose HasSnaky 27 childrenC_594 childrenD_594 children_work_594 (0, 0)
    required_594 envelope_594 pivot_mem_594 child_required_sub_594 child_envelope_sub_594 ?_
  intro b hb; exact common_sub_594 (mem_commonEnvelope childrenD_594 b hb)
end SnakyConditional

end OAI
