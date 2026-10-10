import OAI.GameTheory.SnakyConditional.Templates.Level27Part04

namespace OAI

namespace SnakyConditional
def required_580 : Finset Cell := ⟨(([(-1, -4), (-1, -3), (0, -3), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows009.named_envelope_580_4 : List Cell := ([(-7, 2), (-7, 3), (-7, 4), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-5, 1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_580_4_chain : (named_envelope_580_4.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_580_4_head : (named_envelope_580_4.map Internal.SnakyRows009.namedCellKey).head? = some (-894 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_580_4_last : (named_envelope_580_4.map Internal.SnakyRows009.namedCellKey).getLast? = some (-639 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_580_5 : List Cell := ([(-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, -1), (-4, 0), (-4, 1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_580_5_chain : (named_envelope_580_5.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_580_5_head : (named_envelope_580_5.map Internal.SnakyRows009.namedCellKey).head? = some (-638 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_580_5_last : (named_envelope_580_5.map Internal.SnakyRows009.namedCellKey).getLast? = some (-511 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_580_3 : List Cell := Internal.SnakyRows009.named_envelope_580_4 ++ Internal.SnakyRows009.named_envelope_580_5
theorem Internal.SnakyRows009.named_envelope_580_3_chain : (named_envelope_580_3.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_580_4 Internal.SnakyRows009.named_envelope_580_5 (-639 : ℤ) (-638 : ℤ)
    Internal.SnakyRows009.named_envelope_580_4_chain Internal.SnakyRows009.named_envelope_580_5_chain Internal.SnakyRows009.named_envelope_580_4_last Internal.SnakyRows009.named_envelope_580_5_head (by decide)
theorem Internal.SnakyRows009.named_envelope_580_3_head : (named_envelope_580_3.map Internal.SnakyRows009.namedCellKey).head? = some (-894 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_580_4 Internal.SnakyRows009.named_envelope_580_5 (-894 : ℤ) Internal.SnakyRows009.named_envelope_580_4_head
theorem Internal.SnakyRows009.named_envelope_580_3_last : (named_envelope_580_3.map Internal.SnakyRows009.namedCellKey).getLast? = some (-511 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_580_4 Internal.SnakyRows009.named_envelope_580_5 (-511 : ℤ) Internal.SnakyRows009.named_envelope_580_5_last
def Internal.SnakyRows009.named_envelope_580_7 : List Cell := ([(-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 0), (-3, 1), (-3, 2)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_580_7_chain : (named_envelope_580_7.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_580_7_head : (named_envelope_580_7.map Internal.SnakyRows009.namedCellKey).head? = some (-510 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_580_7_last : (named_envelope_580_7.map Internal.SnakyRows009.namedCellKey).getLast? = some (-382 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_580_8 : List Cell := ([(-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-2, 0), (-2, 1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_580_8_chain : (named_envelope_580_8.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_580_8_head : (named_envelope_580_8.map Internal.SnakyRows009.namedCellKey).head? = some (-381 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_580_8_last : (named_envelope_580_8.map Internal.SnakyRows009.namedCellKey).getLast? = some (-255 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_580_6 : List Cell := Internal.SnakyRows009.named_envelope_580_7 ++ Internal.SnakyRows009.named_envelope_580_8
theorem Internal.SnakyRows009.named_envelope_580_6_chain : (named_envelope_580_6.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_580_7 Internal.SnakyRows009.named_envelope_580_8 (-382 : ℤ) (-381 : ℤ)
    Internal.SnakyRows009.named_envelope_580_7_chain Internal.SnakyRows009.named_envelope_580_8_chain Internal.SnakyRows009.named_envelope_580_7_last Internal.SnakyRows009.named_envelope_580_8_head (by decide)
theorem Internal.SnakyRows009.named_envelope_580_6_head : (named_envelope_580_6.map Internal.SnakyRows009.namedCellKey).head? = some (-510 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_580_7 Internal.SnakyRows009.named_envelope_580_8 (-510 : ℤ) Internal.SnakyRows009.named_envelope_580_7_head
theorem Internal.SnakyRows009.named_envelope_580_6_last : (named_envelope_580_6.map Internal.SnakyRows009.namedCellKey).getLast? = some (-255 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_580_7 Internal.SnakyRows009.named_envelope_580_8 (-255 : ℤ) Internal.SnakyRows009.named_envelope_580_8_last
def Internal.SnakyRows009.named_envelope_580_2 : List Cell := Internal.SnakyRows009.named_envelope_580_3 ++ Internal.SnakyRows009.named_envelope_580_6
theorem Internal.SnakyRows009.named_envelope_580_2_chain : (named_envelope_580_2.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_580_3 Internal.SnakyRows009.named_envelope_580_6 (-511 : ℤ) (-510 : ℤ)
    Internal.SnakyRows009.named_envelope_580_3_chain Internal.SnakyRows009.named_envelope_580_6_chain Internal.SnakyRows009.named_envelope_580_3_last Internal.SnakyRows009.named_envelope_580_6_head (by decide)
theorem Internal.SnakyRows009.named_envelope_580_2_head : (named_envelope_580_2.map Internal.SnakyRows009.namedCellKey).head? = some (-894 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_580_3 Internal.SnakyRows009.named_envelope_580_6 (-894 : ℤ) Internal.SnakyRows009.named_envelope_580_3_head
theorem Internal.SnakyRows009.named_envelope_580_2_last : (named_envelope_580_2.map Internal.SnakyRows009.namedCellKey).getLast? = some (-255 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_580_3 Internal.SnakyRows009.named_envelope_580_6 (-255 : ℤ) Internal.SnakyRows009.named_envelope_580_6_last
def Internal.SnakyRows009.named_envelope_580_11 : List Cell := ([(-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_580_11_chain : (named_envelope_580_11.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_580_11_head : (named_envelope_580_11.map Internal.SnakyRows009.namedCellKey).head? = some (-254 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_580_11_last : (named_envelope_580_11.map Internal.SnakyRows009.namedCellKey).getLast? = some (-246 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_580_12 : List Cell := ([(-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_580_12_chain : (named_envelope_580_12.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_580_12_head : (named_envelope_580_12.map Internal.SnakyRows009.namedCellKey).head? = some (-132 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_580_12_last : (named_envelope_580_12.map Internal.SnakyRows009.namedCellKey).getLast? = some (-124 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_580_10 : List Cell := Internal.SnakyRows009.named_envelope_580_11 ++ Internal.SnakyRows009.named_envelope_580_12
theorem Internal.SnakyRows009.named_envelope_580_10_chain : (named_envelope_580_10.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_580_11 Internal.SnakyRows009.named_envelope_580_12 (-246 : ℤ) (-132 : ℤ)
    Internal.SnakyRows009.named_envelope_580_11_chain Internal.SnakyRows009.named_envelope_580_12_chain Internal.SnakyRows009.named_envelope_580_11_last Internal.SnakyRows009.named_envelope_580_12_head (by decide)
theorem Internal.SnakyRows009.named_envelope_580_10_head : (named_envelope_580_10.map Internal.SnakyRows009.namedCellKey).head? = some (-254 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_580_11 Internal.SnakyRows009.named_envelope_580_12 (-254 : ℤ) Internal.SnakyRows009.named_envelope_580_11_head
theorem Internal.SnakyRows009.named_envelope_580_10_last : (named_envelope_580_10.map Internal.SnakyRows009.namedCellKey).getLast? = some (-124 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_580_11 Internal.SnakyRows009.named_envelope_580_12 (-124 : ℤ) Internal.SnakyRows009.named_envelope_580_12_last
def Internal.SnakyRows009.named_envelope_580_14 : List Cell := ([(-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -3), (0, -2), (0, -1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_580_14_chain : (named_envelope_580_14.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_580_14_head : (named_envelope_580_14.map Internal.SnakyRows009.namedCellKey).head? = some (-123 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_580_14_last : (named_envelope_580_14.map Internal.SnakyRows009.namedCellKey).getLast? = some (-1 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_580_15 : List Cell := ([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_580_15_chain : (named_envelope_580_15.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_580_15_head : (named_envelope_580_15.map Internal.SnakyRows009.namedCellKey).head? = some (0 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_580_15_last : (named_envelope_580_15.map Internal.SnakyRows009.namedCellKey).getLast? = some (9 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_580_13 : List Cell := Internal.SnakyRows009.named_envelope_580_14 ++ Internal.SnakyRows009.named_envelope_580_15
theorem Internal.SnakyRows009.named_envelope_580_13_chain : (named_envelope_580_13.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_580_14 Internal.SnakyRows009.named_envelope_580_15 (-1 : ℤ) (0 : ℤ)
    Internal.SnakyRows009.named_envelope_580_14_chain Internal.SnakyRows009.named_envelope_580_15_chain Internal.SnakyRows009.named_envelope_580_14_last Internal.SnakyRows009.named_envelope_580_15_head (by decide)
theorem Internal.SnakyRows009.named_envelope_580_13_head : (named_envelope_580_13.map Internal.SnakyRows009.namedCellKey).head? = some (-123 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_580_14 Internal.SnakyRows009.named_envelope_580_15 (-123 : ℤ) Internal.SnakyRows009.named_envelope_580_14_head
theorem Internal.SnakyRows009.named_envelope_580_13_last : (named_envelope_580_13.map Internal.SnakyRows009.namedCellKey).getLast? = some (9 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_580_14 Internal.SnakyRows009.named_envelope_580_15 (9 : ℤ) Internal.SnakyRows009.named_envelope_580_15_last
def Internal.SnakyRows009.named_envelope_580_9 : List Cell := Internal.SnakyRows009.named_envelope_580_10 ++ Internal.SnakyRows009.named_envelope_580_13
theorem Internal.SnakyRows009.named_envelope_580_9_chain : (named_envelope_580_9.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_580_10 Internal.SnakyRows009.named_envelope_580_13 (-124 : ℤ) (-123 : ℤ)
    Internal.SnakyRows009.named_envelope_580_10_chain Internal.SnakyRows009.named_envelope_580_13_chain Internal.SnakyRows009.named_envelope_580_10_last Internal.SnakyRows009.named_envelope_580_13_head (by decide)
theorem Internal.SnakyRows009.named_envelope_580_9_head : (named_envelope_580_9.map Internal.SnakyRows009.namedCellKey).head? = some (-254 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_580_10 Internal.SnakyRows009.named_envelope_580_13 (-254 : ℤ) Internal.SnakyRows009.named_envelope_580_10_head
theorem Internal.SnakyRows009.named_envelope_580_9_last : (named_envelope_580_9.map Internal.SnakyRows009.namedCellKey).getLast? = some (9 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_580_10 Internal.SnakyRows009.named_envelope_580_13 (9 : ℤ) Internal.SnakyRows009.named_envelope_580_13_last
def Internal.SnakyRows009.named_envelope_580_1 : List Cell := Internal.SnakyRows009.named_envelope_580_2 ++ Internal.SnakyRows009.named_envelope_580_9
theorem Internal.SnakyRows009.named_envelope_580_1_chain : (named_envelope_580_1.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_580_2 Internal.SnakyRows009.named_envelope_580_9 (-255 : ℤ) (-254 : ℤ)
    Internal.SnakyRows009.named_envelope_580_2_chain Internal.SnakyRows009.named_envelope_580_9_chain Internal.SnakyRows009.named_envelope_580_2_last Internal.SnakyRows009.named_envelope_580_9_head (by decide)
theorem Internal.SnakyRows009.named_envelope_580_1_head : (named_envelope_580_1.map Internal.SnakyRows009.namedCellKey).head? = some (-894 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_580_2 Internal.SnakyRows009.named_envelope_580_9 (-894 : ℤ) Internal.SnakyRows009.named_envelope_580_2_head
theorem Internal.SnakyRows009.named_envelope_580_1_last : (named_envelope_580_1.map Internal.SnakyRows009.namedCellKey).getLast? = some (9 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_580_2 Internal.SnakyRows009.named_envelope_580_9 (9 : ℤ) Internal.SnakyRows009.named_envelope_580_9_last
def Internal.SnakyRows009.named_envelope_580_19 : List Cell := ([(0, 10), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_580_19_chain : (named_envelope_580_19.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_580_19_head : (named_envelope_580_19.map Internal.SnakyRows009.namedCellKey).head? = some (10 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_580_19_last : (named_envelope_580_19.map Internal.SnakyRows009.namedCellKey).getLast? = some (133 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_580_20 : List Cell := ([(1, 6), (1, 7), (1, 8), (1, 9), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_580_20_chain : (named_envelope_580_20.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_580_20_head : (named_envelope_580_20.map Internal.SnakyRows009.namedCellKey).head? = some (134 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_580_20_last : (named_envelope_580_20.map Internal.SnakyRows009.namedCellKey).getLast? = some (257 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_580_18 : List Cell := Internal.SnakyRows009.named_envelope_580_19 ++ Internal.SnakyRows009.named_envelope_580_20
theorem Internal.SnakyRows009.named_envelope_580_18_chain : (named_envelope_580_18.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_580_19 Internal.SnakyRows009.named_envelope_580_20 (133 : ℤ) (134 : ℤ)
    Internal.SnakyRows009.named_envelope_580_19_chain Internal.SnakyRows009.named_envelope_580_20_chain Internal.SnakyRows009.named_envelope_580_19_last Internal.SnakyRows009.named_envelope_580_20_head (by decide)
theorem Internal.SnakyRows009.named_envelope_580_18_head : (named_envelope_580_18.map Internal.SnakyRows009.namedCellKey).head? = some (10 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_580_19 Internal.SnakyRows009.named_envelope_580_20 (10 : ℤ) Internal.SnakyRows009.named_envelope_580_19_head
theorem Internal.SnakyRows009.named_envelope_580_18_last : (named_envelope_580_18.map Internal.SnakyRows009.namedCellKey).getLast? = some (257 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_580_19 Internal.SnakyRows009.named_envelope_580_20 (257 : ℤ) Internal.SnakyRows009.named_envelope_580_20_last
def Internal.SnakyRows009.named_envelope_580_22 : List Cell := ([(2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, -4)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_580_22_chain : (named_envelope_580_22.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_580_22_head : (named_envelope_580_22.map Internal.SnakyRows009.namedCellKey).head? = some (258 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_580_22_last : (named_envelope_580_22.map Internal.SnakyRows009.namedCellKey).getLast? = some (380 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_580_23 : List Cell := ([(3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_580_23_chain : (named_envelope_580_23.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_580_23_head : (named_envelope_580_23.map Internal.SnakyRows009.namedCellKey).head? = some (381 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_580_23_last : (named_envelope_580_23.map Internal.SnakyRows009.namedCellKey).getLast? = some (390 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_580_21 : List Cell := Internal.SnakyRows009.named_envelope_580_22 ++ Internal.SnakyRows009.named_envelope_580_23
theorem Internal.SnakyRows009.named_envelope_580_21_chain : (named_envelope_580_21.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_580_22 Internal.SnakyRows009.named_envelope_580_23 (380 : ℤ) (381 : ℤ)
    Internal.SnakyRows009.named_envelope_580_22_chain Internal.SnakyRows009.named_envelope_580_23_chain Internal.SnakyRows009.named_envelope_580_22_last Internal.SnakyRows009.named_envelope_580_23_head (by decide)
theorem Internal.SnakyRows009.named_envelope_580_21_head : (named_envelope_580_21.map Internal.SnakyRows009.namedCellKey).head? = some (258 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_580_22 Internal.SnakyRows009.named_envelope_580_23 (258 : ℤ) Internal.SnakyRows009.named_envelope_580_22_head
theorem Internal.SnakyRows009.named_envelope_580_21_last : (named_envelope_580_21.map Internal.SnakyRows009.namedCellKey).getLast? = some (390 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_580_22 Internal.SnakyRows009.named_envelope_580_23 (390 : ℤ) Internal.SnakyRows009.named_envelope_580_23_last
def Internal.SnakyRows009.named_envelope_580_17 : List Cell := Internal.SnakyRows009.named_envelope_580_18 ++ Internal.SnakyRows009.named_envelope_580_21
theorem Internal.SnakyRows009.named_envelope_580_17_chain : (named_envelope_580_17.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_580_18 Internal.SnakyRows009.named_envelope_580_21 (257 : ℤ) (258 : ℤ)
    Internal.SnakyRows009.named_envelope_580_18_chain Internal.SnakyRows009.named_envelope_580_21_chain Internal.SnakyRows009.named_envelope_580_18_last Internal.SnakyRows009.named_envelope_580_21_head (by decide)
theorem Internal.SnakyRows009.named_envelope_580_17_head : (named_envelope_580_17.map Internal.SnakyRows009.namedCellKey).head? = some (10 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_580_18 Internal.SnakyRows009.named_envelope_580_21 (10 : ℤ) Internal.SnakyRows009.named_envelope_580_18_head
theorem Internal.SnakyRows009.named_envelope_580_17_last : (named_envelope_580_17.map Internal.SnakyRows009.namedCellKey).getLast? = some (390 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_580_18 Internal.SnakyRows009.named_envelope_580_21 (390 : ℤ) Internal.SnakyRows009.named_envelope_580_21_last
def Internal.SnakyRows009.named_envelope_580_26 : List Cell := ([(3, 7), (3, 8), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_580_26_chain : (named_envelope_580_26.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_580_26_head : (named_envelope_580_26.map Internal.SnakyRows009.namedCellKey).head? = some (391 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_580_26_last : (named_envelope_580_26.map Internal.SnakyRows009.namedCellKey).getLast? = some (515 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_580_27 : List Cell := ([(4, 4), (4, 5), (4, 6), (4, 7), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_580_27_chain : (named_envelope_580_27.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_580_27_head : (named_envelope_580_27.map Internal.SnakyRows009.namedCellKey).head? = some (516 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_580_27_last : (named_envelope_580_27.map Internal.SnakyRows009.namedCellKey).getLast? = some (641 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_580_25 : List Cell := Internal.SnakyRows009.named_envelope_580_26 ++ Internal.SnakyRows009.named_envelope_580_27
theorem Internal.SnakyRows009.named_envelope_580_25_chain : (named_envelope_580_25.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_580_26 Internal.SnakyRows009.named_envelope_580_27 (515 : ℤ) (516 : ℤ)
    Internal.SnakyRows009.named_envelope_580_26_chain Internal.SnakyRows009.named_envelope_580_27_chain Internal.SnakyRows009.named_envelope_580_26_last Internal.SnakyRows009.named_envelope_580_27_head (by decide)
theorem Internal.SnakyRows009.named_envelope_580_25_head : (named_envelope_580_25.map Internal.SnakyRows009.namedCellKey).head? = some (391 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_580_26 Internal.SnakyRows009.named_envelope_580_27 (391 : ℤ) Internal.SnakyRows009.named_envelope_580_26_head
theorem Internal.SnakyRows009.named_envelope_580_25_last : (named_envelope_580_25.map Internal.SnakyRows009.namedCellKey).getLast? = some (641 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_580_26 Internal.SnakyRows009.named_envelope_580_27 (641 : ℤ) Internal.SnakyRows009.named_envelope_580_27_last
def Internal.SnakyRows009.named_envelope_580_29 : List Cell := ([(5, 2), (5, 3), (5, 4), (5, 5), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_580_29_chain : (named_envelope_580_29.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_580_29_head : (named_envelope_580_29.map Internal.SnakyRows009.namedCellKey).head? = some (642 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_580_29_last : (named_envelope_580_29.map Internal.SnakyRows009.namedCellKey).getLast? = some (770 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_580_30 : List Cell := ([(6, 3), (6, 4), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (8, -2), (8, 0), (8, 2)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_580_30_chain : (named_envelope_580_30.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_580_30_head : (named_envelope_580_30.map Internal.SnakyRows009.namedCellKey).head? = some (771 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_580_30_last : (named_envelope_580_30.map Internal.SnakyRows009.namedCellKey).getLast? = some (1026 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_580_28 : List Cell := Internal.SnakyRows009.named_envelope_580_29 ++ Internal.SnakyRows009.named_envelope_580_30
theorem Internal.SnakyRows009.named_envelope_580_28_chain : (named_envelope_580_28.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_580_29 Internal.SnakyRows009.named_envelope_580_30 (770 : ℤ) (771 : ℤ)
    Internal.SnakyRows009.named_envelope_580_29_chain Internal.SnakyRows009.named_envelope_580_30_chain Internal.SnakyRows009.named_envelope_580_29_last Internal.SnakyRows009.named_envelope_580_30_head (by decide)
theorem Internal.SnakyRows009.named_envelope_580_28_head : (named_envelope_580_28.map Internal.SnakyRows009.namedCellKey).head? = some (642 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_580_29 Internal.SnakyRows009.named_envelope_580_30 (642 : ℤ) Internal.SnakyRows009.named_envelope_580_29_head
theorem Internal.SnakyRows009.named_envelope_580_28_last : (named_envelope_580_28.map Internal.SnakyRows009.namedCellKey).getLast? = some (1026 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_580_29 Internal.SnakyRows009.named_envelope_580_30 (1026 : ℤ) Internal.SnakyRows009.named_envelope_580_30_last
def Internal.SnakyRows009.named_envelope_580_24 : List Cell := Internal.SnakyRows009.named_envelope_580_25 ++ Internal.SnakyRows009.named_envelope_580_28
theorem Internal.SnakyRows009.named_envelope_580_24_chain : (named_envelope_580_24.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_580_25 Internal.SnakyRows009.named_envelope_580_28 (641 : ℤ) (642 : ℤ)
    Internal.SnakyRows009.named_envelope_580_25_chain Internal.SnakyRows009.named_envelope_580_28_chain Internal.SnakyRows009.named_envelope_580_25_last Internal.SnakyRows009.named_envelope_580_28_head (by decide)
theorem Internal.SnakyRows009.named_envelope_580_24_head : (named_envelope_580_24.map Internal.SnakyRows009.namedCellKey).head? = some (391 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_580_25 Internal.SnakyRows009.named_envelope_580_28 (391 : ℤ) Internal.SnakyRows009.named_envelope_580_25_head
theorem Internal.SnakyRows009.named_envelope_580_24_last : (named_envelope_580_24.map Internal.SnakyRows009.namedCellKey).getLast? = some (1026 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_580_25 Internal.SnakyRows009.named_envelope_580_28 (1026 : ℤ) Internal.SnakyRows009.named_envelope_580_28_last
def Internal.SnakyRows009.named_envelope_580_16 : List Cell := Internal.SnakyRows009.named_envelope_580_17 ++ Internal.SnakyRows009.named_envelope_580_24
theorem Internal.SnakyRows009.named_envelope_580_16_chain : (named_envelope_580_16.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_580_17 Internal.SnakyRows009.named_envelope_580_24 (390 : ℤ) (391 : ℤ)
    Internal.SnakyRows009.named_envelope_580_17_chain Internal.SnakyRows009.named_envelope_580_24_chain Internal.SnakyRows009.named_envelope_580_17_last Internal.SnakyRows009.named_envelope_580_24_head (by decide)
theorem Internal.SnakyRows009.named_envelope_580_16_head : (named_envelope_580_16.map Internal.SnakyRows009.namedCellKey).head? = some (10 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_580_17 Internal.SnakyRows009.named_envelope_580_24 (10 : ℤ) Internal.SnakyRows009.named_envelope_580_17_head
theorem Internal.SnakyRows009.named_envelope_580_16_last : (named_envelope_580_16.map Internal.SnakyRows009.namedCellKey).getLast? = some (1026 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_580_17 Internal.SnakyRows009.named_envelope_580_24 (1026 : ℤ) Internal.SnakyRows009.named_envelope_580_24_last
def Internal.SnakyRows009.named_envelope_580_0 : List Cell := Internal.SnakyRows009.named_envelope_580_1 ++ Internal.SnakyRows009.named_envelope_580_16
theorem Internal.SnakyRows009.named_envelope_580_0_chain : (named_envelope_580_0.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_580_1 Internal.SnakyRows009.named_envelope_580_16 (9 : ℤ) (10 : ℤ)
    Internal.SnakyRows009.named_envelope_580_1_chain Internal.SnakyRows009.named_envelope_580_16_chain Internal.SnakyRows009.named_envelope_580_1_last Internal.SnakyRows009.named_envelope_580_16_head (by decide)
theorem Internal.SnakyRows009.named_envelope_580_0_head : (named_envelope_580_0.map Internal.SnakyRows009.namedCellKey).head? = some (-894 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_580_1 Internal.SnakyRows009.named_envelope_580_16 (-894 : ℤ) Internal.SnakyRows009.named_envelope_580_1_head
theorem Internal.SnakyRows009.named_envelope_580_0_last : (named_envelope_580_0.map Internal.SnakyRows009.namedCellKey).getLast? = some (1026 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_580_1 Internal.SnakyRows009.named_envelope_580_16 (1026 : ℤ) Internal.SnakyRows009.named_envelope_580_16_last
theorem Internal.SnakyRows009.named_envelope_580_nodup : (Internal.SnakyRows009.named_envelope_580_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows009.named_nodup_of_chain Internal.SnakyRows009.named_envelope_580_0 Internal.SnakyRows009.named_envelope_580_0_chain
def envelope_580 : Finset Cell := ⟨(Internal.SnakyRows009.named_envelope_580_0 : Multiset Cell), Internal.SnakyRows009.named_envelope_580_nodup⟩
def childrenC_580 : Fin 2 → Finset Cell := ![(placedSet 7 (0, -2) required_2), (placedSet 0 (-1, -1) required_579)]
def childrenD_580 : Fin 2 → Finset Cell := ![(placedSet 7 (0, -2) envelope_2), (placedSet 0 (-1, -1) envelope_579)]
theorem common_sub_580 : commonEnvelope childrenD_580 ⊆ insert (0, 0) required_580 := by decide
theorem child_required_sub_580 : ∀ j, childrenC_580 j ⊆ insert (0, 0) required_580 := by decide
theorem Internal.SnakyRows009.containment_580_0 :
    placedSet 7 (0, -2) envelope_2 ⊆ envelope_580 := by decide
theorem Internal.SnakyRows009.containment_580_1 :
    placedSet 0 (-1, -1) envelope_579 ⊆ envelope_580 := by decide +kernel
theorem child_envelope_sub_580 : ∀ j, childrenD_580 j ⊆ envelope_580 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows009.containment_580_0
  · exact Internal.SnakyRows009.containment_580_1
theorem pivot_mem_580 : (0, 0) ∈ envelope_580 := by decide
theorem children_work_580 : ∀ j, Template HasSnaky 25 (childrenC_580 j) (childrenD_580 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_2 7 (0, -2)).mono (by decide)
  · exact (placed_template_map row_works_579 0 (-1, -1)).mono (by decide)
theorem row_works_580 : Template HasSnaky 26 required_580 envelope_580 := by
  refine compose HasSnaky 25 childrenC_580 childrenD_580 children_work_580 (0, 0)
    required_580 envelope_580 pivot_mem_580 child_required_sub_580 child_envelope_sub_580 ?_
  intro b hb; exact common_sub_580 (mem_commonEnvelope childrenD_580 b hb)
end SnakyConditional

end OAI
