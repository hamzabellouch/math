import OAI.GameTheory.SnakyConditional.Templates.Level17Part02
import OAI.GameTheory.SnakyConditional.Templates.Level30Part02

namespace OAI

namespace SnakyConditional
def required_601 : Finset Cell := ⟨(([(0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows011F.named_envelope_601_5 : List Cell := ([(-9, -3), (-9, -1), (-8, -3), (-8, -2), (-8, -1), (-7, -5), (-7, -4), (-7, -3)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_5_chain : (named_envelope_601_5.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_5_head : (named_envelope_601_5.map Internal.SnakyRows011F.namedCellKey).head? = some (-1155 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_5_last : (named_envelope_601_5.map Internal.SnakyRows011F.namedCellKey).getLast? = some (-899 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_6 : List Cell := ([(-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-6, -5), (-6, -4), (-6, -3)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_6_chain : (named_envelope_601_6.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_6_head : (named_envelope_601_6.map Internal.SnakyRows011F.namedCellKey).head? = some (-898 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_6_last : (named_envelope_601_6.map Internal.SnakyRows011F.namedCellKey).getLast? = some (-771 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_4 : List Cell := Internal.SnakyRows011F.named_envelope_601_5 ++ Internal.SnakyRows011F.named_envelope_601_6
theorem Internal.SnakyRows011F.named_envelope_601_4_chain : (named_envelope_601_4.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_5 Internal.SnakyRows011F.named_envelope_601_6 (-899 : ℤ) (-898 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_5_chain Internal.SnakyRows011F.named_envelope_601_6_chain Internal.SnakyRows011F.named_envelope_601_5_last Internal.SnakyRows011F.named_envelope_601_6_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_4_head : (named_envelope_601_4.map Internal.SnakyRows011F.namedCellKey).head? = some (-1155 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_5 Internal.SnakyRows011F.named_envelope_601_6 (-1155 : ℤ) Internal.SnakyRows011F.named_envelope_601_5_head
theorem Internal.SnakyRows011F.named_envelope_601_4_last : (named_envelope_601_4.map Internal.SnakyRows011F.namedCellKey).getLast? = some (-771 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_5 Internal.SnakyRows011F.named_envelope_601_6 (-771 : ℤ) Internal.SnakyRows011F.named_envelope_601_6_last
def Internal.SnakyRows011F.named_envelope_601_8 : List Cell := ([(-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 6), (-6, 7), (-6, 9)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_8_chain : (named_envelope_601_8.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_8_head : (named_envelope_601_8.map Internal.SnakyRows011F.namedCellKey).head? = some (-770 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_8_last : (named_envelope_601_8.map Internal.SnakyRows011F.namedCellKey).getLast? = some (-759 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_9 : List Cell := ([(-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_9_chain : (named_envelope_601_9.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_9_head : (named_envelope_601_9.map Internal.SnakyRows011F.namedCellKey).head? = some (-645 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_9_last : (named_envelope_601_9.map Internal.SnakyRows011F.namedCellKey).getLast? = some (-637 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_7 : List Cell := Internal.SnakyRows011F.named_envelope_601_8 ++ Internal.SnakyRows011F.named_envelope_601_9
theorem Internal.SnakyRows011F.named_envelope_601_7_chain : (named_envelope_601_7.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_8 Internal.SnakyRows011F.named_envelope_601_9 (-759 : ℤ) (-645 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_8_chain Internal.SnakyRows011F.named_envelope_601_9_chain Internal.SnakyRows011F.named_envelope_601_8_last Internal.SnakyRows011F.named_envelope_601_9_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_7_head : (named_envelope_601_7.map Internal.SnakyRows011F.namedCellKey).head? = some (-770 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_8 Internal.SnakyRows011F.named_envelope_601_9 (-770 : ℤ) Internal.SnakyRows011F.named_envelope_601_8_head
theorem Internal.SnakyRows011F.named_envelope_601_7_last : (named_envelope_601_7.map Internal.SnakyRows011F.namedCellKey).getLast? = some (-637 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_8 Internal.SnakyRows011F.named_envelope_601_9 (-637 : ℤ) Internal.SnakyRows011F.named_envelope_601_9_last
def Internal.SnakyRows011F.named_envelope_601_3 : List Cell := Internal.SnakyRows011F.named_envelope_601_4 ++ Internal.SnakyRows011F.named_envelope_601_7
theorem Internal.SnakyRows011F.named_envelope_601_3_chain : (named_envelope_601_3.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_4 Internal.SnakyRows011F.named_envelope_601_7 (-771 : ℤ) (-770 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_4_chain Internal.SnakyRows011F.named_envelope_601_7_chain Internal.SnakyRows011F.named_envelope_601_4_last Internal.SnakyRows011F.named_envelope_601_7_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_3_head : (named_envelope_601_3.map Internal.SnakyRows011F.namedCellKey).head? = some (-1155 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_4 Internal.SnakyRows011F.named_envelope_601_7 (-1155 : ℤ) Internal.SnakyRows011F.named_envelope_601_4_head
theorem Internal.SnakyRows011F.named_envelope_601_3_last : (named_envelope_601_3.map Internal.SnakyRows011F.namedCellKey).getLast? = some (-637 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_4 Internal.SnakyRows011F.named_envelope_601_7 (-637 : ℤ) Internal.SnakyRows011F.named_envelope_601_7_last
def Internal.SnakyRows011F.named_envelope_601_12 : List Cell := ([(-5, 4), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-4, -7), (-4, -6), (-4, -5)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_12_chain : (named_envelope_601_12.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_12_head : (named_envelope_601_12.map Internal.SnakyRows011F.namedCellKey).head? = some (-636 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_12_last : (named_envelope_601_12.map Internal.SnakyRows011F.namedCellKey).getLast? = some (-517 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_13 : List Cell := ([(-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_13_chain : (named_envelope_601_13.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_13_head : (named_envelope_601_13.map Internal.SnakyRows011F.namedCellKey).head? = some (-516 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_13_last : (named_envelope_601_13.map Internal.SnakyRows011F.namedCellKey).getLast? = some (-508 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_11 : List Cell := Internal.SnakyRows011F.named_envelope_601_12 ++ Internal.SnakyRows011F.named_envelope_601_13
theorem Internal.SnakyRows011F.named_envelope_601_11_chain : (named_envelope_601_11.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_12 Internal.SnakyRows011F.named_envelope_601_13 (-517 : ℤ) (-516 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_12_chain Internal.SnakyRows011F.named_envelope_601_13_chain Internal.SnakyRows011F.named_envelope_601_12_last Internal.SnakyRows011F.named_envelope_601_13_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_11_head : (named_envelope_601_11.map Internal.SnakyRows011F.namedCellKey).head? = some (-636 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_12 Internal.SnakyRows011F.named_envelope_601_13 (-636 : ℤ) Internal.SnakyRows011F.named_envelope_601_12_head
theorem Internal.SnakyRows011F.named_envelope_601_11_last : (named_envelope_601_11.map Internal.SnakyRows011F.namedCellKey).getLast? = some (-508 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_12 Internal.SnakyRows011F.named_envelope_601_13 (-508 : ℤ) Internal.SnakyRows011F.named_envelope_601_13_last
def Internal.SnakyRows011F.named_envelope_601_15 : List Cell := ([(-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-3, -7)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_15_chain : (named_envelope_601_15.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_15_head : (named_envelope_601_15.map Internal.SnakyRows011F.namedCellKey).head? = some (-507 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_15_last : (named_envelope_601_15.map Internal.SnakyRows011F.namedCellKey).getLast? = some (-391 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_16 : List Cell := ([(-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_16_chain : (named_envelope_601_16.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_16_head : (named_envelope_601_16.map Internal.SnakyRows011F.namedCellKey).head? = some (-390 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_16_last : (named_envelope_601_16.map Internal.SnakyRows011F.namedCellKey).getLast? = some (-382 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_14 : List Cell := Internal.SnakyRows011F.named_envelope_601_15 ++ Internal.SnakyRows011F.named_envelope_601_16
theorem Internal.SnakyRows011F.named_envelope_601_14_chain : (named_envelope_601_14.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_15 Internal.SnakyRows011F.named_envelope_601_16 (-391 : ℤ) (-390 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_15_chain Internal.SnakyRows011F.named_envelope_601_16_chain Internal.SnakyRows011F.named_envelope_601_15_last Internal.SnakyRows011F.named_envelope_601_16_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_14_head : (named_envelope_601_14.map Internal.SnakyRows011F.namedCellKey).head? = some (-507 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_15 Internal.SnakyRows011F.named_envelope_601_16 (-507 : ℤ) Internal.SnakyRows011F.named_envelope_601_15_head
theorem Internal.SnakyRows011F.named_envelope_601_14_last : (named_envelope_601_14.map Internal.SnakyRows011F.namedCellKey).getLast? = some (-382 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_15 Internal.SnakyRows011F.named_envelope_601_16 (-382 : ℤ) Internal.SnakyRows011F.named_envelope_601_16_last
def Internal.SnakyRows011F.named_envelope_601_10 : List Cell := Internal.SnakyRows011F.named_envelope_601_11 ++ Internal.SnakyRows011F.named_envelope_601_14
theorem Internal.SnakyRows011F.named_envelope_601_10_chain : (named_envelope_601_10.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_11 Internal.SnakyRows011F.named_envelope_601_14 (-508 : ℤ) (-507 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_11_chain Internal.SnakyRows011F.named_envelope_601_14_chain Internal.SnakyRows011F.named_envelope_601_11_last Internal.SnakyRows011F.named_envelope_601_14_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_10_head : (named_envelope_601_10.map Internal.SnakyRows011F.namedCellKey).head? = some (-636 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_11 Internal.SnakyRows011F.named_envelope_601_14 (-636 : ℤ) Internal.SnakyRows011F.named_envelope_601_11_head
theorem Internal.SnakyRows011F.named_envelope_601_10_last : (named_envelope_601_10.map Internal.SnakyRows011F.namedCellKey).getLast? = some (-382 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_11 Internal.SnakyRows011F.named_envelope_601_14 (-382 : ℤ) Internal.SnakyRows011F.named_envelope_601_14_last
def Internal.SnakyRows011F.named_envelope_601_2 : List Cell := Internal.SnakyRows011F.named_envelope_601_3 ++ Internal.SnakyRows011F.named_envelope_601_10
theorem Internal.SnakyRows011F.named_envelope_601_2_chain : (named_envelope_601_2.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_3 Internal.SnakyRows011F.named_envelope_601_10 (-637 : ℤ) (-636 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_3_chain Internal.SnakyRows011F.named_envelope_601_10_chain Internal.SnakyRows011F.named_envelope_601_3_last Internal.SnakyRows011F.named_envelope_601_10_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_2_head : (named_envelope_601_2.map Internal.SnakyRows011F.namedCellKey).head? = some (-1155 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_3 Internal.SnakyRows011F.named_envelope_601_10 (-1155 : ℤ) Internal.SnakyRows011F.named_envelope_601_3_head
theorem Internal.SnakyRows011F.named_envelope_601_2_last : (named_envelope_601_2.map Internal.SnakyRows011F.namedCellKey).getLast? = some (-382 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_3 Internal.SnakyRows011F.named_envelope_601_10 (-382 : ℤ) Internal.SnakyRows011F.named_envelope_601_10_last
def Internal.SnakyRows011F.named_envelope_601_20 : List Cell := ([(-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_20_chain : (named_envelope_601_20.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_20_head : (named_envelope_601_20.map Internal.SnakyRows011F.namedCellKey).head? = some (-381 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_20_last : (named_envelope_601_20.map Internal.SnakyRows011F.namedCellKey).getLast? = some (-374 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_21 : List Cell := ([(-3, 11), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_21_chain : (named_envelope_601_21.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_21_head : (named_envelope_601_21.map Internal.SnakyRows011F.namedCellKey).head? = some (-373 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_21_last : (named_envelope_601_21.map Internal.SnakyRows011F.namedCellKey).getLast? = some (-256 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_19 : List Cell := Internal.SnakyRows011F.named_envelope_601_20 ++ Internal.SnakyRows011F.named_envelope_601_21
theorem Internal.SnakyRows011F.named_envelope_601_19_chain : (named_envelope_601_19.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_20 Internal.SnakyRows011F.named_envelope_601_21 (-374 : ℤ) (-373 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_20_chain Internal.SnakyRows011F.named_envelope_601_21_chain Internal.SnakyRows011F.named_envelope_601_20_last Internal.SnakyRows011F.named_envelope_601_21_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_19_head : (named_envelope_601_19.map Internal.SnakyRows011F.namedCellKey).head? = some (-381 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_20 Internal.SnakyRows011F.named_envelope_601_21 (-381 : ℤ) Internal.SnakyRows011F.named_envelope_601_20_head
theorem Internal.SnakyRows011F.named_envelope_601_19_last : (named_envelope_601_19.map Internal.SnakyRows011F.namedCellKey).getLast? = some (-256 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_20 Internal.SnakyRows011F.named_envelope_601_21 (-256 : ℤ) Internal.SnakyRows011F.named_envelope_601_21_last
def Internal.SnakyRows011F.named_envelope_601_23 : List Cell := ([(-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_23_chain : (named_envelope_601_23.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_23_head : (named_envelope_601_23.map Internal.SnakyRows011F.namedCellKey).head? = some (-255 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_23_last : (named_envelope_601_23.map Internal.SnakyRows011F.namedCellKey).getLast? = some (-247 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_24 : List Cell := ([(-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-1, -5), (-1, -4), (-1, -3), (-1, -1)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_24_chain : (named_envelope_601_24.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_24_head : (named_envelope_601_24.map Internal.SnakyRows011F.namedCellKey).head? = some (-246 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_24_last : (named_envelope_601_24.map Internal.SnakyRows011F.namedCellKey).getLast? = some (-129 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_22 : List Cell := Internal.SnakyRows011F.named_envelope_601_23 ++ Internal.SnakyRows011F.named_envelope_601_24
theorem Internal.SnakyRows011F.named_envelope_601_22_chain : (named_envelope_601_22.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_23 Internal.SnakyRows011F.named_envelope_601_24 (-247 : ℤ) (-246 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_23_chain Internal.SnakyRows011F.named_envelope_601_24_chain Internal.SnakyRows011F.named_envelope_601_23_last Internal.SnakyRows011F.named_envelope_601_24_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_22_head : (named_envelope_601_22.map Internal.SnakyRows011F.namedCellKey).head? = some (-255 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_23 Internal.SnakyRows011F.named_envelope_601_24 (-255 : ℤ) Internal.SnakyRows011F.named_envelope_601_23_head
theorem Internal.SnakyRows011F.named_envelope_601_22_last : (named_envelope_601_22.map Internal.SnakyRows011F.namedCellKey).getLast? = some (-129 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_23 Internal.SnakyRows011F.named_envelope_601_24 (-129 : ℤ) Internal.SnakyRows011F.named_envelope_601_24_last
def Internal.SnakyRows011F.named_envelope_601_18 : List Cell := Internal.SnakyRows011F.named_envelope_601_19 ++ Internal.SnakyRows011F.named_envelope_601_22
theorem Internal.SnakyRows011F.named_envelope_601_18_chain : (named_envelope_601_18.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_19 Internal.SnakyRows011F.named_envelope_601_22 (-256 : ℤ) (-255 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_19_chain Internal.SnakyRows011F.named_envelope_601_22_chain Internal.SnakyRows011F.named_envelope_601_19_last Internal.SnakyRows011F.named_envelope_601_22_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_18_head : (named_envelope_601_18.map Internal.SnakyRows011F.namedCellKey).head? = some (-381 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_19 Internal.SnakyRows011F.named_envelope_601_22 (-381 : ℤ) Internal.SnakyRows011F.named_envelope_601_19_head
theorem Internal.SnakyRows011F.named_envelope_601_18_last : (named_envelope_601_18.map Internal.SnakyRows011F.namedCellKey).getLast? = some (-129 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_19 Internal.SnakyRows011F.named_envelope_601_22 (-129 : ℤ) Internal.SnakyRows011F.named_envelope_601_22_last
def Internal.SnakyRows011F.named_envelope_601_27 : List Cell := ([(-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_27_chain : (named_envelope_601_27.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_27_head : (named_envelope_601_27.map Internal.SnakyRows011F.namedCellKey).head? = some (-128 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_27_last : (named_envelope_601_27.map Internal.SnakyRows011F.namedCellKey).getLast? = some (-121 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_28 : List Cell := ([(-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -5), (0, -4), (0, -3)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_28_chain : (named_envelope_601_28.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_28_head : (named_envelope_601_28.map Internal.SnakyRows011F.namedCellKey).head? = some (-120 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_28_last : (named_envelope_601_28.map Internal.SnakyRows011F.namedCellKey).getLast? = some (-3 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_26 : List Cell := Internal.SnakyRows011F.named_envelope_601_27 ++ Internal.SnakyRows011F.named_envelope_601_28
theorem Internal.SnakyRows011F.named_envelope_601_26_chain : (named_envelope_601_26.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_27 Internal.SnakyRows011F.named_envelope_601_28 (-121 : ℤ) (-120 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_27_chain Internal.SnakyRows011F.named_envelope_601_28_chain Internal.SnakyRows011F.named_envelope_601_27_last Internal.SnakyRows011F.named_envelope_601_28_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_26_head : (named_envelope_601_26.map Internal.SnakyRows011F.namedCellKey).head? = some (-128 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_27 Internal.SnakyRows011F.named_envelope_601_28 (-128 : ℤ) Internal.SnakyRows011F.named_envelope_601_27_head
theorem Internal.SnakyRows011F.named_envelope_601_26_last : (named_envelope_601_26.map Internal.SnakyRows011F.namedCellKey).getLast? = some (-3 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_27 Internal.SnakyRows011F.named_envelope_601_28 (-3 : ℤ) Internal.SnakyRows011F.named_envelope_601_28_last
def Internal.SnakyRows011F.named_envelope_601_30 : List Cell := ([(0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_30_chain : (named_envelope_601_30.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_30_head : (named_envelope_601_30.map Internal.SnakyRows011F.namedCellKey).head? = some (-2 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_30_last : (named_envelope_601_30.map Internal.SnakyRows011F.namedCellKey).getLast? = some (6 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_31 : List Cell := ([(0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (1, -6)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_31_chain : (named_envelope_601_31.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_31_head : (named_envelope_601_31.map Internal.SnakyRows011F.namedCellKey).head? = some (7 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_31_last : (named_envelope_601_31.map Internal.SnakyRows011F.namedCellKey).getLast? = some (122 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_29 : List Cell := Internal.SnakyRows011F.named_envelope_601_30 ++ Internal.SnakyRows011F.named_envelope_601_31
theorem Internal.SnakyRows011F.named_envelope_601_29_chain : (named_envelope_601_29.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_30 Internal.SnakyRows011F.named_envelope_601_31 (6 : ℤ) (7 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_30_chain Internal.SnakyRows011F.named_envelope_601_31_chain Internal.SnakyRows011F.named_envelope_601_30_last Internal.SnakyRows011F.named_envelope_601_31_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_29_head : (named_envelope_601_29.map Internal.SnakyRows011F.namedCellKey).head? = some (-2 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_30 Internal.SnakyRows011F.named_envelope_601_31 (-2 : ℤ) Internal.SnakyRows011F.named_envelope_601_30_head
theorem Internal.SnakyRows011F.named_envelope_601_29_last : (named_envelope_601_29.map Internal.SnakyRows011F.namedCellKey).getLast? = some (122 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_30 Internal.SnakyRows011F.named_envelope_601_31 (122 : ℤ) Internal.SnakyRows011F.named_envelope_601_31_last
def Internal.SnakyRows011F.named_envelope_601_25 : List Cell := Internal.SnakyRows011F.named_envelope_601_26 ++ Internal.SnakyRows011F.named_envelope_601_29
theorem Internal.SnakyRows011F.named_envelope_601_25_chain : (named_envelope_601_25.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_26 Internal.SnakyRows011F.named_envelope_601_29 (-3 : ℤ) (-2 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_26_chain Internal.SnakyRows011F.named_envelope_601_29_chain Internal.SnakyRows011F.named_envelope_601_26_last Internal.SnakyRows011F.named_envelope_601_29_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_25_head : (named_envelope_601_25.map Internal.SnakyRows011F.namedCellKey).head? = some (-128 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_26 Internal.SnakyRows011F.named_envelope_601_29 (-128 : ℤ) Internal.SnakyRows011F.named_envelope_601_26_head
theorem Internal.SnakyRows011F.named_envelope_601_25_last : (named_envelope_601_25.map Internal.SnakyRows011F.namedCellKey).getLast? = some (122 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_26 Internal.SnakyRows011F.named_envelope_601_29 (122 : ℤ) Internal.SnakyRows011F.named_envelope_601_29_last
def Internal.SnakyRows011F.named_envelope_601_17 : List Cell := Internal.SnakyRows011F.named_envelope_601_18 ++ Internal.SnakyRows011F.named_envelope_601_25
theorem Internal.SnakyRows011F.named_envelope_601_17_chain : (named_envelope_601_17.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_18 Internal.SnakyRows011F.named_envelope_601_25 (-129 : ℤ) (-128 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_18_chain Internal.SnakyRows011F.named_envelope_601_25_chain Internal.SnakyRows011F.named_envelope_601_18_last Internal.SnakyRows011F.named_envelope_601_25_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_17_head : (named_envelope_601_17.map Internal.SnakyRows011F.namedCellKey).head? = some (-381 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_18 Internal.SnakyRows011F.named_envelope_601_25 (-381 : ℤ) Internal.SnakyRows011F.named_envelope_601_18_head
theorem Internal.SnakyRows011F.named_envelope_601_17_last : (named_envelope_601_17.map Internal.SnakyRows011F.namedCellKey).getLast? = some (122 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_18 Internal.SnakyRows011F.named_envelope_601_25 (122 : ℤ) Internal.SnakyRows011F.named_envelope_601_25_last
def Internal.SnakyRows011F.named_envelope_601_1 : List Cell := Internal.SnakyRows011F.named_envelope_601_2 ++ Internal.SnakyRows011F.named_envelope_601_17
theorem Internal.SnakyRows011F.named_envelope_601_1_chain : (named_envelope_601_1.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_2 Internal.SnakyRows011F.named_envelope_601_17 (-382 : ℤ) (-381 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_2_chain Internal.SnakyRows011F.named_envelope_601_17_chain Internal.SnakyRows011F.named_envelope_601_2_last Internal.SnakyRows011F.named_envelope_601_17_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_1_head : (named_envelope_601_1.map Internal.SnakyRows011F.namedCellKey).head? = some (-1155 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_2 Internal.SnakyRows011F.named_envelope_601_17 (-1155 : ℤ) Internal.SnakyRows011F.named_envelope_601_2_head
theorem Internal.SnakyRows011F.named_envelope_601_1_last : (named_envelope_601_1.map Internal.SnakyRows011F.namedCellKey).getLast? = some (122 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_2 Internal.SnakyRows011F.named_envelope_601_17 (122 : ℤ) Internal.SnakyRows011F.named_envelope_601_17_last
def Internal.SnakyRows011F.named_envelope_601_36 : List Cell := ([(1, -5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_36_chain : (named_envelope_601_36.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_36_head : (named_envelope_601_36.map Internal.SnakyRows011F.namedCellKey).head? = some (123 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_36_last : (named_envelope_601_36.map Internal.SnakyRows011F.namedCellKey).getLast? = some (131 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_37 : List Cell := ([(1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_37_chain : (named_envelope_601_37.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_37_head : (named_envelope_601_37.map Internal.SnakyRows011F.namedCellKey).head? = some (132 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_37_last : (named_envelope_601_37.map Internal.SnakyRows011F.namedCellKey).getLast? = some (140 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_35 : List Cell := Internal.SnakyRows011F.named_envelope_601_36 ++ Internal.SnakyRows011F.named_envelope_601_37
theorem Internal.SnakyRows011F.named_envelope_601_35_chain : (named_envelope_601_35.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_36 Internal.SnakyRows011F.named_envelope_601_37 (131 : ℤ) (132 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_36_chain Internal.SnakyRows011F.named_envelope_601_37_chain Internal.SnakyRows011F.named_envelope_601_36_last Internal.SnakyRows011F.named_envelope_601_37_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_35_head : (named_envelope_601_35.map Internal.SnakyRows011F.namedCellKey).head? = some (123 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_36 Internal.SnakyRows011F.named_envelope_601_37 (123 : ℤ) Internal.SnakyRows011F.named_envelope_601_36_head
theorem Internal.SnakyRows011F.named_envelope_601_35_last : (named_envelope_601_35.map Internal.SnakyRows011F.namedCellKey).getLast? = some (140 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_36 Internal.SnakyRows011F.named_envelope_601_37 (140 : ℤ) Internal.SnakyRows011F.named_envelope_601_37_last
def Internal.SnakyRows011F.named_envelope_601_39 : List Cell := ([(2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_39_chain : (named_envelope_601_39.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_39_head : (named_envelope_601_39.map Internal.SnakyRows011F.namedCellKey).head? = some (251 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_39_last : (named_envelope_601_39.map Internal.SnakyRows011F.namedCellKey).getLast? = some (259 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_40 : List Cell := ([(2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_40_chain : (named_envelope_601_40.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_40_head : (named_envelope_601_40.map Internal.SnakyRows011F.namedCellKey).head? = some (260 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_40_last : (named_envelope_601_40.map Internal.SnakyRows011F.namedCellKey).getLast? = some (268 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_38 : List Cell := Internal.SnakyRows011F.named_envelope_601_39 ++ Internal.SnakyRows011F.named_envelope_601_40
theorem Internal.SnakyRows011F.named_envelope_601_38_chain : (named_envelope_601_38.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_39 Internal.SnakyRows011F.named_envelope_601_40 (259 : ℤ) (260 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_39_chain Internal.SnakyRows011F.named_envelope_601_40_chain Internal.SnakyRows011F.named_envelope_601_39_last Internal.SnakyRows011F.named_envelope_601_40_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_38_head : (named_envelope_601_38.map Internal.SnakyRows011F.namedCellKey).head? = some (251 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_39 Internal.SnakyRows011F.named_envelope_601_40 (251 : ℤ) Internal.SnakyRows011F.named_envelope_601_39_head
theorem Internal.SnakyRows011F.named_envelope_601_38_last : (named_envelope_601_38.map Internal.SnakyRows011F.namedCellKey).getLast? = some (268 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_39 Internal.SnakyRows011F.named_envelope_601_40 (268 : ℤ) Internal.SnakyRows011F.named_envelope_601_40_last
def Internal.SnakyRows011F.named_envelope_601_34 : List Cell := Internal.SnakyRows011F.named_envelope_601_35 ++ Internal.SnakyRows011F.named_envelope_601_38
theorem Internal.SnakyRows011F.named_envelope_601_34_chain : (named_envelope_601_34.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_35 Internal.SnakyRows011F.named_envelope_601_38 (140 : ℤ) (251 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_35_chain Internal.SnakyRows011F.named_envelope_601_38_chain Internal.SnakyRows011F.named_envelope_601_35_last Internal.SnakyRows011F.named_envelope_601_38_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_34_head : (named_envelope_601_34.map Internal.SnakyRows011F.namedCellKey).head? = some (123 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_35 Internal.SnakyRows011F.named_envelope_601_38 (123 : ℤ) Internal.SnakyRows011F.named_envelope_601_35_head
theorem Internal.SnakyRows011F.named_envelope_601_34_last : (named_envelope_601_34.map Internal.SnakyRows011F.namedCellKey).getLast? = some (268 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_35 Internal.SnakyRows011F.named_envelope_601_38 (268 : ℤ) Internal.SnakyRows011F.named_envelope_601_38_last
def Internal.SnakyRows011F.named_envelope_601_43 : List Cell := ([(3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_43_chain : (named_envelope_601_43.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_43_head : (named_envelope_601_43.map Internal.SnakyRows011F.namedCellKey).head? = some (379 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_43_last : (named_envelope_601_43.map Internal.SnakyRows011F.namedCellKey).getLast? = some (386 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_44 : List Cell := ([(3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_44_chain : (named_envelope_601_44.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_44_head : (named_envelope_601_44.map Internal.SnakyRows011F.namedCellKey).head? = some (387 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_44_last : (named_envelope_601_44.map Internal.SnakyRows011F.namedCellKey).getLast? = some (395 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_42 : List Cell := Internal.SnakyRows011F.named_envelope_601_43 ++ Internal.SnakyRows011F.named_envelope_601_44
theorem Internal.SnakyRows011F.named_envelope_601_42_chain : (named_envelope_601_42.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_43 Internal.SnakyRows011F.named_envelope_601_44 (386 : ℤ) (387 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_43_chain Internal.SnakyRows011F.named_envelope_601_44_chain Internal.SnakyRows011F.named_envelope_601_43_last Internal.SnakyRows011F.named_envelope_601_44_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_42_head : (named_envelope_601_42.map Internal.SnakyRows011F.namedCellKey).head? = some (379 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_43 Internal.SnakyRows011F.named_envelope_601_44 (379 : ℤ) Internal.SnakyRows011F.named_envelope_601_43_head
theorem Internal.SnakyRows011F.named_envelope_601_42_last : (named_envelope_601_42.map Internal.SnakyRows011F.namedCellKey).getLast? = some (395 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_43 Internal.SnakyRows011F.named_envelope_601_44 (395 : ℤ) Internal.SnakyRows011F.named_envelope_601_44_last
def Internal.SnakyRows011F.named_envelope_601_46 : List Cell := ([(3, 12), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_46_chain : (named_envelope_601_46.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_46_head : (named_envelope_601_46.map Internal.SnakyRows011F.namedCellKey).head? = some (396 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_46_last : (named_envelope_601_46.map Internal.SnakyRows011F.namedCellKey).getLast? = some (514 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_47 : List Cell := ([(4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_47_chain : (named_envelope_601_47.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_47_head : (named_envelope_601_47.map Internal.SnakyRows011F.namedCellKey).head? = some (515 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_47_last : (named_envelope_601_47.map Internal.SnakyRows011F.namedCellKey).getLast? = some (523 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_45 : List Cell := Internal.SnakyRows011F.named_envelope_601_46 ++ Internal.SnakyRows011F.named_envelope_601_47
theorem Internal.SnakyRows011F.named_envelope_601_45_chain : (named_envelope_601_45.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_46 Internal.SnakyRows011F.named_envelope_601_47 (514 : ℤ) (515 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_46_chain Internal.SnakyRows011F.named_envelope_601_47_chain Internal.SnakyRows011F.named_envelope_601_46_last Internal.SnakyRows011F.named_envelope_601_47_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_45_head : (named_envelope_601_45.map Internal.SnakyRows011F.namedCellKey).head? = some (396 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_46 Internal.SnakyRows011F.named_envelope_601_47 (396 : ℤ) Internal.SnakyRows011F.named_envelope_601_46_head
theorem Internal.SnakyRows011F.named_envelope_601_45_last : (named_envelope_601_45.map Internal.SnakyRows011F.namedCellKey).getLast? = some (523 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_46 Internal.SnakyRows011F.named_envelope_601_47 (523 : ℤ) Internal.SnakyRows011F.named_envelope_601_47_last
def Internal.SnakyRows011F.named_envelope_601_41 : List Cell := Internal.SnakyRows011F.named_envelope_601_42 ++ Internal.SnakyRows011F.named_envelope_601_45
theorem Internal.SnakyRows011F.named_envelope_601_41_chain : (named_envelope_601_41.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_42 Internal.SnakyRows011F.named_envelope_601_45 (395 : ℤ) (396 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_42_chain Internal.SnakyRows011F.named_envelope_601_45_chain Internal.SnakyRows011F.named_envelope_601_42_last Internal.SnakyRows011F.named_envelope_601_45_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_41_head : (named_envelope_601_41.map Internal.SnakyRows011F.namedCellKey).head? = some (379 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_42 Internal.SnakyRows011F.named_envelope_601_45 (379 : ℤ) Internal.SnakyRows011F.named_envelope_601_42_head
theorem Internal.SnakyRows011F.named_envelope_601_41_last : (named_envelope_601_41.map Internal.SnakyRows011F.namedCellKey).getLast? = some (523 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_42 Internal.SnakyRows011F.named_envelope_601_45 (523 : ℤ) Internal.SnakyRows011F.named_envelope_601_45_last
def Internal.SnakyRows011F.named_envelope_601_33 : List Cell := Internal.SnakyRows011F.named_envelope_601_34 ++ Internal.SnakyRows011F.named_envelope_601_41
theorem Internal.SnakyRows011F.named_envelope_601_33_chain : (named_envelope_601_33.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_34 Internal.SnakyRows011F.named_envelope_601_41 (268 : ℤ) (379 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_34_chain Internal.SnakyRows011F.named_envelope_601_41_chain Internal.SnakyRows011F.named_envelope_601_34_last Internal.SnakyRows011F.named_envelope_601_41_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_33_head : (named_envelope_601_33.map Internal.SnakyRows011F.namedCellKey).head? = some (123 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_34 Internal.SnakyRows011F.named_envelope_601_41 (123 : ℤ) Internal.SnakyRows011F.named_envelope_601_34_head
theorem Internal.SnakyRows011F.named_envelope_601_33_last : (named_envelope_601_33.map Internal.SnakyRows011F.namedCellKey).getLast? = some (523 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_34 Internal.SnakyRows011F.named_envelope_601_41 (523 : ℤ) Internal.SnakyRows011F.named_envelope_601_41_last
def Internal.SnakyRows011F.named_envelope_601_51 : List Cell := ([(4, 12), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_51_chain : (named_envelope_601_51.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_51_head : (named_envelope_601_51.map Internal.SnakyRows011F.namedCellKey).head? = some (524 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_51_last : (named_envelope_601_51.map Internal.SnakyRows011F.namedCellKey).getLast? = some (642 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_52 : List Cell := ([(5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -2)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_52_chain : (named_envelope_601_52.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_52_head : (named_envelope_601_52.map Internal.SnakyRows011F.namedCellKey).head? = some (643 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_52_last : (named_envelope_601_52.map Internal.SnakyRows011F.namedCellKey).getLast? = some (766 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_50 : List Cell := Internal.SnakyRows011F.named_envelope_601_51 ++ Internal.SnakyRows011F.named_envelope_601_52
theorem Internal.SnakyRows011F.named_envelope_601_50_chain : (named_envelope_601_50.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_51 Internal.SnakyRows011F.named_envelope_601_52 (642 : ℤ) (643 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_51_chain Internal.SnakyRows011F.named_envelope_601_52_chain Internal.SnakyRows011F.named_envelope_601_51_last Internal.SnakyRows011F.named_envelope_601_52_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_50_head : (named_envelope_601_50.map Internal.SnakyRows011F.namedCellKey).head? = some (524 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_51 Internal.SnakyRows011F.named_envelope_601_52 (524 : ℤ) Internal.SnakyRows011F.named_envelope_601_51_head
theorem Internal.SnakyRows011F.named_envelope_601_50_last : (named_envelope_601_50.map Internal.SnakyRows011F.namedCellKey).getLast? = some (766 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_51 Internal.SnakyRows011F.named_envelope_601_52 (766 : ℤ) Internal.SnakyRows011F.named_envelope_601_52_last
def Internal.SnakyRows011F.named_envelope_601_54 : List Cell := ([(6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_54_chain : (named_envelope_601_54.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_54_head : (named_envelope_601_54.map Internal.SnakyRows011F.namedCellKey).head? = some (767 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_54_last : (named_envelope_601_54.map Internal.SnakyRows011F.namedCellKey).getLast? = some (775 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_55 : List Cell := ([(6, 8), (6, 9), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_55_chain : (named_envelope_601_55.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_55_head : (named_envelope_601_55.map Internal.SnakyRows011F.namedCellKey).head? = some (776 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_55_last : (named_envelope_601_55.map Internal.SnakyRows011F.namedCellKey).getLast? = some (900 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_53 : List Cell := Internal.SnakyRows011F.named_envelope_601_54 ++ Internal.SnakyRows011F.named_envelope_601_55
theorem Internal.SnakyRows011F.named_envelope_601_53_chain : (named_envelope_601_53.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_54 Internal.SnakyRows011F.named_envelope_601_55 (775 : ℤ) (776 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_54_chain Internal.SnakyRows011F.named_envelope_601_55_chain Internal.SnakyRows011F.named_envelope_601_54_last Internal.SnakyRows011F.named_envelope_601_55_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_53_head : (named_envelope_601_53.map Internal.SnakyRows011F.namedCellKey).head? = some (767 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_54 Internal.SnakyRows011F.named_envelope_601_55 (767 : ℤ) Internal.SnakyRows011F.named_envelope_601_54_head
theorem Internal.SnakyRows011F.named_envelope_601_53_last : (named_envelope_601_53.map Internal.SnakyRows011F.namedCellKey).getLast? = some (900 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_54 Internal.SnakyRows011F.named_envelope_601_55 (900 : ℤ) Internal.SnakyRows011F.named_envelope_601_55_last
def Internal.SnakyRows011F.named_envelope_601_49 : List Cell := Internal.SnakyRows011F.named_envelope_601_50 ++ Internal.SnakyRows011F.named_envelope_601_53
theorem Internal.SnakyRows011F.named_envelope_601_49_chain : (named_envelope_601_49.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_50 Internal.SnakyRows011F.named_envelope_601_53 (766 : ℤ) (767 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_50_chain Internal.SnakyRows011F.named_envelope_601_53_chain Internal.SnakyRows011F.named_envelope_601_50_last Internal.SnakyRows011F.named_envelope_601_53_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_49_head : (named_envelope_601_49.map Internal.SnakyRows011F.namedCellKey).head? = some (524 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_50 Internal.SnakyRows011F.named_envelope_601_53 (524 : ℤ) Internal.SnakyRows011F.named_envelope_601_50_head
theorem Internal.SnakyRows011F.named_envelope_601_49_last : (named_envelope_601_49.map Internal.SnakyRows011F.namedCellKey).getLast? = some (900 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_50 Internal.SnakyRows011F.named_envelope_601_53 (900 : ℤ) Internal.SnakyRows011F.named_envelope_601_53_last
def Internal.SnakyRows011F.named_envelope_601_58 : List Cell := ([(7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, -2), (8, -1), (8, 0)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_58_chain : (named_envelope_601_58.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_58_head : (named_envelope_601_58.map Internal.SnakyRows011F.namedCellKey).head? = some (901 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_58_last : (named_envelope_601_58.map Internal.SnakyRows011F.namedCellKey).getLast? = some (1024 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_59 : List Cell := ([(8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, 1)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_59_chain : (named_envelope_601_59.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_59_head : (named_envelope_601_59.map Internal.SnakyRows011F.namedCellKey).head? = some (1025 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_59_last : (named_envelope_601_59.map Internal.SnakyRows011F.namedCellKey).getLast? = some (1153 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_57 : List Cell := Internal.SnakyRows011F.named_envelope_601_58 ++ Internal.SnakyRows011F.named_envelope_601_59
theorem Internal.SnakyRows011F.named_envelope_601_57_chain : (named_envelope_601_57.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_58 Internal.SnakyRows011F.named_envelope_601_59 (1024 : ℤ) (1025 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_58_chain Internal.SnakyRows011F.named_envelope_601_59_chain Internal.SnakyRows011F.named_envelope_601_58_last Internal.SnakyRows011F.named_envelope_601_59_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_57_head : (named_envelope_601_57.map Internal.SnakyRows011F.namedCellKey).head? = some (901 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_58 Internal.SnakyRows011F.named_envelope_601_59 (901 : ℤ) Internal.SnakyRows011F.named_envelope_601_58_head
theorem Internal.SnakyRows011F.named_envelope_601_57_last : (named_envelope_601_57.map Internal.SnakyRows011F.namedCellKey).getLast? = some (1153 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_58 Internal.SnakyRows011F.named_envelope_601_59 (1153 : ℤ) Internal.SnakyRows011F.named_envelope_601_59_last
def Internal.SnakyRows011F.named_envelope_601_61 : List Cell := ([(9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (10, 1), (10, 2), (10, 3)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_61_chain : (named_envelope_601_61.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_61_head : (named_envelope_601_61.map Internal.SnakyRows011F.namedCellKey).head? = some (1154 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_61_last : (named_envelope_601_61.map Internal.SnakyRows011F.namedCellKey).getLast? = some (1283 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_62 : List Cell := ([(10, 4), (10, 5), (10, 6), (10, 7), (11, 1), (11, 2), (11, 3), (12, 1), (12, 3)] : List Cell)
theorem Internal.SnakyRows011F.named_envelope_601_62_chain : (named_envelope_601_62.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_62_head : (named_envelope_601_62.map Internal.SnakyRows011F.namedCellKey).head? = some (1284 : ℤ) := by decide
theorem Internal.SnakyRows011F.named_envelope_601_62_last : (named_envelope_601_62.map Internal.SnakyRows011F.namedCellKey).getLast? = some (1539 : ℤ) := by decide
def Internal.SnakyRows011F.named_envelope_601_60 : List Cell := Internal.SnakyRows011F.named_envelope_601_61 ++ Internal.SnakyRows011F.named_envelope_601_62
theorem Internal.SnakyRows011F.named_envelope_601_60_chain : (named_envelope_601_60.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_61 Internal.SnakyRows011F.named_envelope_601_62 (1283 : ℤ) (1284 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_61_chain Internal.SnakyRows011F.named_envelope_601_62_chain Internal.SnakyRows011F.named_envelope_601_61_last Internal.SnakyRows011F.named_envelope_601_62_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_60_head : (named_envelope_601_60.map Internal.SnakyRows011F.namedCellKey).head? = some (1154 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_61 Internal.SnakyRows011F.named_envelope_601_62 (1154 : ℤ) Internal.SnakyRows011F.named_envelope_601_61_head
theorem Internal.SnakyRows011F.named_envelope_601_60_last : (named_envelope_601_60.map Internal.SnakyRows011F.namedCellKey).getLast? = some (1539 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_61 Internal.SnakyRows011F.named_envelope_601_62 (1539 : ℤ) Internal.SnakyRows011F.named_envelope_601_62_last
def Internal.SnakyRows011F.named_envelope_601_56 : List Cell := Internal.SnakyRows011F.named_envelope_601_57 ++ Internal.SnakyRows011F.named_envelope_601_60
theorem Internal.SnakyRows011F.named_envelope_601_56_chain : (named_envelope_601_56.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_57 Internal.SnakyRows011F.named_envelope_601_60 (1153 : ℤ) (1154 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_57_chain Internal.SnakyRows011F.named_envelope_601_60_chain Internal.SnakyRows011F.named_envelope_601_57_last Internal.SnakyRows011F.named_envelope_601_60_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_56_head : (named_envelope_601_56.map Internal.SnakyRows011F.namedCellKey).head? = some (901 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_57 Internal.SnakyRows011F.named_envelope_601_60 (901 : ℤ) Internal.SnakyRows011F.named_envelope_601_57_head
theorem Internal.SnakyRows011F.named_envelope_601_56_last : (named_envelope_601_56.map Internal.SnakyRows011F.namedCellKey).getLast? = some (1539 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_57 Internal.SnakyRows011F.named_envelope_601_60 (1539 : ℤ) Internal.SnakyRows011F.named_envelope_601_60_last
def Internal.SnakyRows011F.named_envelope_601_48 : List Cell := Internal.SnakyRows011F.named_envelope_601_49 ++ Internal.SnakyRows011F.named_envelope_601_56
theorem Internal.SnakyRows011F.named_envelope_601_48_chain : (named_envelope_601_48.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_49 Internal.SnakyRows011F.named_envelope_601_56 (900 : ℤ) (901 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_49_chain Internal.SnakyRows011F.named_envelope_601_56_chain Internal.SnakyRows011F.named_envelope_601_49_last Internal.SnakyRows011F.named_envelope_601_56_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_48_head : (named_envelope_601_48.map Internal.SnakyRows011F.namedCellKey).head? = some (524 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_49 Internal.SnakyRows011F.named_envelope_601_56 (524 : ℤ) Internal.SnakyRows011F.named_envelope_601_49_head
theorem Internal.SnakyRows011F.named_envelope_601_48_last : (named_envelope_601_48.map Internal.SnakyRows011F.namedCellKey).getLast? = some (1539 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_49 Internal.SnakyRows011F.named_envelope_601_56 (1539 : ℤ) Internal.SnakyRows011F.named_envelope_601_56_last
def Internal.SnakyRows011F.named_envelope_601_32 : List Cell := Internal.SnakyRows011F.named_envelope_601_33 ++ Internal.SnakyRows011F.named_envelope_601_48
theorem Internal.SnakyRows011F.named_envelope_601_32_chain : (named_envelope_601_32.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_33 Internal.SnakyRows011F.named_envelope_601_48 (523 : ℤ) (524 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_33_chain Internal.SnakyRows011F.named_envelope_601_48_chain Internal.SnakyRows011F.named_envelope_601_33_last Internal.SnakyRows011F.named_envelope_601_48_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_32_head : (named_envelope_601_32.map Internal.SnakyRows011F.namedCellKey).head? = some (123 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_33 Internal.SnakyRows011F.named_envelope_601_48 (123 : ℤ) Internal.SnakyRows011F.named_envelope_601_33_head
theorem Internal.SnakyRows011F.named_envelope_601_32_last : (named_envelope_601_32.map Internal.SnakyRows011F.namedCellKey).getLast? = some (1539 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_33 Internal.SnakyRows011F.named_envelope_601_48 (1539 : ℤ) Internal.SnakyRows011F.named_envelope_601_48_last
def Internal.SnakyRows011F.named_envelope_601_0 : List Cell := Internal.SnakyRows011F.named_envelope_601_1 ++ Internal.SnakyRows011F.named_envelope_601_32
theorem Internal.SnakyRows011F.named_envelope_601_0_chain : (named_envelope_601_0.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011F.named_chain_append Internal.SnakyRows011F.named_envelope_601_1 Internal.SnakyRows011F.named_envelope_601_32 (122 : ℤ) (123 : ℤ)
    Internal.SnakyRows011F.named_envelope_601_1_chain Internal.SnakyRows011F.named_envelope_601_32_chain Internal.SnakyRows011F.named_envelope_601_1_last Internal.SnakyRows011F.named_envelope_601_32_head (by decide)
theorem Internal.SnakyRows011F.named_envelope_601_0_head : (named_envelope_601_0.map Internal.SnakyRows011F.namedCellKey).head? = some (-1155 : ℤ) :=
  Internal.SnakyRows011F.named_head_append Internal.SnakyRows011F.named_envelope_601_1 Internal.SnakyRows011F.named_envelope_601_32 (-1155 : ℤ) Internal.SnakyRows011F.named_envelope_601_1_head
theorem Internal.SnakyRows011F.named_envelope_601_0_last : (named_envelope_601_0.map Internal.SnakyRows011F.namedCellKey).getLast? = some (1539 : ℤ) :=
  Internal.SnakyRows011F.named_last_append Internal.SnakyRows011F.named_envelope_601_1 Internal.SnakyRows011F.named_envelope_601_32 (1539 : ℤ) Internal.SnakyRows011F.named_envelope_601_32_last
theorem Internal.SnakyRows011F.named_envelope_601_nodup : (Internal.SnakyRows011F.named_envelope_601_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows011F.named_nodup_of_chain Internal.SnakyRows011F.named_envelope_601_0 Internal.SnakyRows011F.named_envelope_601_0_chain
def envelope_601 : Finset Cell := ⟨(Internal.SnakyRows011F.named_envelope_601_0 : Multiset Cell), Internal.SnakyRows011F.named_envelope_601_nodup⟩
def childrenC_601 : Fin 5 → Finset Cell := ![(placedSet 6 (0, -3) required_437), (placedSet 0 (0, 1) required_553), (placedSet 0 (1, 1) required_592), (placedSet 4 (-1, 1) required_236), (placedSet 4 (0, -3) required_469)]
def childrenD_601 : Fin 5 → Finset Cell := ![(placedSet 6 (0, -3) envelope_437), (placedSet 0 (0, 1) envelope_553), (placedSet 0 (1, 1) envelope_592), (placedSet 4 (-1, 1) envelope_236), (placedSet 4 (0, -3) envelope_469)]
theorem common_sub_601 : commonEnvelope childrenD_601 ⊆ insert (0, 0) required_601 := by decide
theorem child_required_sub_601 : ∀ j, childrenC_601 j ⊆ insert (0, 0) required_601 := by decide
theorem Internal.SnakyRows011F.containment_601_0 :
    placedSet 6 (0, -3) envelope_437 ⊆ envelope_601 := by decide
theorem Internal.SnakyRows011F.containment_601_1 :
    placedSet 0 (0, 1) envelope_553 ⊆ envelope_601 := by decide +kernel
theorem Internal.SnakyRows011F.containment_601_2 :
    placedSet 0 (1, 1) envelope_592 ⊆ envelope_601 := by decide +kernel
theorem Internal.SnakyRows011F.containment_601_3 :
    placedSet 4 (-1, 1) envelope_236 ⊆ envelope_601 := by decide
theorem Internal.SnakyRows011F.containment_601_4 :
    placedSet 4 (0, -3) envelope_469 ⊆ envelope_601 := by decide
theorem child_envelope_sub_601 : ∀ j, childrenD_601 j ⊆ envelope_601 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows011F.containment_601_0
  · exact Internal.SnakyRows011F.containment_601_1
  · exact Internal.SnakyRows011F.containment_601_2
  · exact Internal.SnakyRows011F.containment_601_3
  · exact Internal.SnakyRows011F.containment_601_4
theorem pivot_mem_601 : (0, 0) ∈ envelope_601 := by decide
theorem children_work_601 : ∀ j, Template HasSnaky 28 (childrenC_601 j) (childrenD_601 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_437 6 (0, -3)).mono (by decide)
  · exact (placed_template_map row_works_553 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_592 0 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_236 4 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_469 4 (0, -3)).mono (by decide)
theorem row_works_601 : Template HasSnaky 29 required_601 envelope_601 := by
  refine compose HasSnaky 28 childrenC_601 childrenD_601 children_work_601 (0, 0)
    required_601 envelope_601 pivot_mem_601 child_required_sub_601 child_envelope_sub_601 ?_
  intro b hb; exact common_sub_601 (mem_commonEnvelope childrenD_601 b hb)
def required_602 : Finset Cell := ⟨(([(0, 1), (0, 2)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows011G.named_envelope_602_5 : List Cell := ([(-9, -1), (-9, 1), (-8, -1), (-8, 0), (-8, 1), (-7, -3), (-7, -2), (-7, -1)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_5_chain : (named_envelope_602_5.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_5_head : (named_envelope_602_5.map Internal.SnakyRows011G.namedCellKey).head? = some (-1153 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_5_last : (named_envelope_602_5.map Internal.SnakyRows011G.namedCellKey).getLast? = some (-897 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_6 : List Cell := ([(-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-6, -3), (-6, -2), (-6, -1)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_6_chain : (named_envelope_602_6.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_6_head : (named_envelope_602_6.map Internal.SnakyRows011G.namedCellKey).head? = some (-896 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_6_last : (named_envelope_602_6.map Internal.SnakyRows011G.namedCellKey).getLast? = some (-769 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_4 : List Cell := Internal.SnakyRows011G.named_envelope_602_5 ++ Internal.SnakyRows011G.named_envelope_602_6
theorem Internal.SnakyRows011G.named_envelope_602_4_chain : (named_envelope_602_4.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_5 Internal.SnakyRows011G.named_envelope_602_6 (-897 : ℤ) (-896 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_5_chain Internal.SnakyRows011G.named_envelope_602_6_chain Internal.SnakyRows011G.named_envelope_602_5_last Internal.SnakyRows011G.named_envelope_602_6_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_4_head : (named_envelope_602_4.map Internal.SnakyRows011G.namedCellKey).head? = some (-1153 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_5 Internal.SnakyRows011G.named_envelope_602_6 (-1153 : ℤ) Internal.SnakyRows011G.named_envelope_602_5_head
theorem Internal.SnakyRows011G.named_envelope_602_4_last : (named_envelope_602_4.map Internal.SnakyRows011G.namedCellKey).getLast? = some (-769 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_5 Internal.SnakyRows011G.named_envelope_602_6 (-769 : ℤ) Internal.SnakyRows011G.named_envelope_602_6_last
def Internal.SnakyRows011G.named_envelope_602_8 : List Cell := ([(-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 8), (-6, 9), (-6, 11)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_8_chain : (named_envelope_602_8.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_8_head : (named_envelope_602_8.map Internal.SnakyRows011G.namedCellKey).head? = some (-768 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_8_last : (named_envelope_602_8.map Internal.SnakyRows011G.namedCellKey).getLast? = some (-757 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_9 : List Cell := ([(-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_9_chain : (named_envelope_602_9.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_9_head : (named_envelope_602_9.map Internal.SnakyRows011G.namedCellKey).head? = some (-643 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_9_last : (named_envelope_602_9.map Internal.SnakyRows011G.namedCellKey).getLast? = some (-635 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_7 : List Cell := Internal.SnakyRows011G.named_envelope_602_8 ++ Internal.SnakyRows011G.named_envelope_602_9
theorem Internal.SnakyRows011G.named_envelope_602_7_chain : (named_envelope_602_7.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_8 Internal.SnakyRows011G.named_envelope_602_9 (-757 : ℤ) (-643 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_8_chain Internal.SnakyRows011G.named_envelope_602_9_chain Internal.SnakyRows011G.named_envelope_602_8_last Internal.SnakyRows011G.named_envelope_602_9_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_7_head : (named_envelope_602_7.map Internal.SnakyRows011G.namedCellKey).head? = some (-768 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_8 Internal.SnakyRows011G.named_envelope_602_9 (-768 : ℤ) Internal.SnakyRows011G.named_envelope_602_8_head
theorem Internal.SnakyRows011G.named_envelope_602_7_last : (named_envelope_602_7.map Internal.SnakyRows011G.namedCellKey).getLast? = some (-635 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_8 Internal.SnakyRows011G.named_envelope_602_9 (-635 : ℤ) Internal.SnakyRows011G.named_envelope_602_9_last
def Internal.SnakyRows011G.named_envelope_602_3 : List Cell := Internal.SnakyRows011G.named_envelope_602_4 ++ Internal.SnakyRows011G.named_envelope_602_7
theorem Internal.SnakyRows011G.named_envelope_602_3_chain : (named_envelope_602_3.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_4 Internal.SnakyRows011G.named_envelope_602_7 (-769 : ℤ) (-768 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_4_chain Internal.SnakyRows011G.named_envelope_602_7_chain Internal.SnakyRows011G.named_envelope_602_4_last Internal.SnakyRows011G.named_envelope_602_7_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_3_head : (named_envelope_602_3.map Internal.SnakyRows011G.namedCellKey).head? = some (-1153 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_4 Internal.SnakyRows011G.named_envelope_602_7 (-1153 : ℤ) Internal.SnakyRows011G.named_envelope_602_4_head
theorem Internal.SnakyRows011G.named_envelope_602_3_last : (named_envelope_602_3.map Internal.SnakyRows011G.namedCellKey).getLast? = some (-635 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_4 Internal.SnakyRows011G.named_envelope_602_7 (-635 : ℤ) Internal.SnakyRows011G.named_envelope_602_7_last
def Internal.SnakyRows011G.named_envelope_602_12 : List Cell := ([(-5, 6), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-4, -5), (-4, -4), (-4, -3)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_12_chain : (named_envelope_602_12.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_12_head : (named_envelope_602_12.map Internal.SnakyRows011G.namedCellKey).head? = some (-634 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_12_last : (named_envelope_602_12.map Internal.SnakyRows011G.namedCellKey).getLast? = some (-515 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_13 : List Cell := ([(-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_13_chain : (named_envelope_602_13.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_13_head : (named_envelope_602_13.map Internal.SnakyRows011G.namedCellKey).head? = some (-514 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_13_last : (named_envelope_602_13.map Internal.SnakyRows011G.namedCellKey).getLast? = some (-506 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_11 : List Cell := Internal.SnakyRows011G.named_envelope_602_12 ++ Internal.SnakyRows011G.named_envelope_602_13
theorem Internal.SnakyRows011G.named_envelope_602_11_chain : (named_envelope_602_11.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_12 Internal.SnakyRows011G.named_envelope_602_13 (-515 : ℤ) (-514 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_12_chain Internal.SnakyRows011G.named_envelope_602_13_chain Internal.SnakyRows011G.named_envelope_602_12_last Internal.SnakyRows011G.named_envelope_602_13_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_11_head : (named_envelope_602_11.map Internal.SnakyRows011G.namedCellKey).head? = some (-634 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_12 Internal.SnakyRows011G.named_envelope_602_13 (-634 : ℤ) Internal.SnakyRows011G.named_envelope_602_12_head
theorem Internal.SnakyRows011G.named_envelope_602_11_last : (named_envelope_602_11.map Internal.SnakyRows011G.namedCellKey).getLast? = some (-506 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_12 Internal.SnakyRows011G.named_envelope_602_13 (-506 : ℤ) Internal.SnakyRows011G.named_envelope_602_13_last
def Internal.SnakyRows011G.named_envelope_602_15 : List Cell := ([(-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-4, 13), (-4, 14), (-3, -5)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_15_chain : (named_envelope_602_15.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_15_head : (named_envelope_602_15.map Internal.SnakyRows011G.namedCellKey).head? = some (-505 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_15_last : (named_envelope_602_15.map Internal.SnakyRows011G.namedCellKey).getLast? = some (-389 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_16 : List Cell := ([(-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_16_chain : (named_envelope_602_16.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_16_head : (named_envelope_602_16.map Internal.SnakyRows011G.namedCellKey).head? = some (-388 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_16_last : (named_envelope_602_16.map Internal.SnakyRows011G.namedCellKey).getLast? = some (-380 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_14 : List Cell := Internal.SnakyRows011G.named_envelope_602_15 ++ Internal.SnakyRows011G.named_envelope_602_16
theorem Internal.SnakyRows011G.named_envelope_602_14_chain : (named_envelope_602_14.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_15 Internal.SnakyRows011G.named_envelope_602_16 (-389 : ℤ) (-388 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_15_chain Internal.SnakyRows011G.named_envelope_602_16_chain Internal.SnakyRows011G.named_envelope_602_15_last Internal.SnakyRows011G.named_envelope_602_16_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_14_head : (named_envelope_602_14.map Internal.SnakyRows011G.namedCellKey).head? = some (-505 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_15 Internal.SnakyRows011G.named_envelope_602_16 (-505 : ℤ) Internal.SnakyRows011G.named_envelope_602_15_head
theorem Internal.SnakyRows011G.named_envelope_602_14_last : (named_envelope_602_14.map Internal.SnakyRows011G.namedCellKey).getLast? = some (-380 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_15 Internal.SnakyRows011G.named_envelope_602_16 (-380 : ℤ) Internal.SnakyRows011G.named_envelope_602_16_last
def Internal.SnakyRows011G.named_envelope_602_10 : List Cell := Internal.SnakyRows011G.named_envelope_602_11 ++ Internal.SnakyRows011G.named_envelope_602_14
theorem Internal.SnakyRows011G.named_envelope_602_10_chain : (named_envelope_602_10.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_11 Internal.SnakyRows011G.named_envelope_602_14 (-506 : ℤ) (-505 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_11_chain Internal.SnakyRows011G.named_envelope_602_14_chain Internal.SnakyRows011G.named_envelope_602_11_last Internal.SnakyRows011G.named_envelope_602_14_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_10_head : (named_envelope_602_10.map Internal.SnakyRows011G.namedCellKey).head? = some (-634 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_11 Internal.SnakyRows011G.named_envelope_602_14 (-634 : ℤ) Internal.SnakyRows011G.named_envelope_602_11_head
theorem Internal.SnakyRows011G.named_envelope_602_10_last : (named_envelope_602_10.map Internal.SnakyRows011G.namedCellKey).getLast? = some (-380 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_11 Internal.SnakyRows011G.named_envelope_602_14 (-380 : ℤ) Internal.SnakyRows011G.named_envelope_602_14_last
def Internal.SnakyRows011G.named_envelope_602_2 : List Cell := Internal.SnakyRows011G.named_envelope_602_3 ++ Internal.SnakyRows011G.named_envelope_602_10
theorem Internal.SnakyRows011G.named_envelope_602_2_chain : (named_envelope_602_2.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_3 Internal.SnakyRows011G.named_envelope_602_10 (-635 : ℤ) (-634 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_3_chain Internal.SnakyRows011G.named_envelope_602_10_chain Internal.SnakyRows011G.named_envelope_602_3_last Internal.SnakyRows011G.named_envelope_602_10_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_2_head : (named_envelope_602_2.map Internal.SnakyRows011G.namedCellKey).head? = some (-1153 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_3 Internal.SnakyRows011G.named_envelope_602_10 (-1153 : ℤ) Internal.SnakyRows011G.named_envelope_602_3_head
theorem Internal.SnakyRows011G.named_envelope_602_2_last : (named_envelope_602_2.map Internal.SnakyRows011G.namedCellKey).getLast? = some (-380 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_3 Internal.SnakyRows011G.named_envelope_602_10 (-380 : ℤ) Internal.SnakyRows011G.named_envelope_602_10_last
def Internal.SnakyRows011G.named_envelope_602_20 : List Cell := ([(-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_20_chain : (named_envelope_602_20.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_20_head : (named_envelope_602_20.map Internal.SnakyRows011G.namedCellKey).head? = some (-379 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_20_last : (named_envelope_602_20.map Internal.SnakyRows011G.namedCellKey).getLast? = some (-372 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_21 : List Cell := ([(-3, 13), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_21_chain : (named_envelope_602_21.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_21_head : (named_envelope_602_21.map Internal.SnakyRows011G.namedCellKey).head? = some (-371 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_21_last : (named_envelope_602_21.map Internal.SnakyRows011G.namedCellKey).getLast? = some (-254 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_19 : List Cell := Internal.SnakyRows011G.named_envelope_602_20 ++ Internal.SnakyRows011G.named_envelope_602_21
theorem Internal.SnakyRows011G.named_envelope_602_19_chain : (named_envelope_602_19.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_20 Internal.SnakyRows011G.named_envelope_602_21 (-372 : ℤ) (-371 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_20_chain Internal.SnakyRows011G.named_envelope_602_21_chain Internal.SnakyRows011G.named_envelope_602_20_last Internal.SnakyRows011G.named_envelope_602_21_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_19_head : (named_envelope_602_19.map Internal.SnakyRows011G.namedCellKey).head? = some (-379 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_20 Internal.SnakyRows011G.named_envelope_602_21 (-379 : ℤ) Internal.SnakyRows011G.named_envelope_602_20_head
theorem Internal.SnakyRows011G.named_envelope_602_19_last : (named_envelope_602_19.map Internal.SnakyRows011G.namedCellKey).getLast? = some (-254 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_20 Internal.SnakyRows011G.named_envelope_602_21 (-254 : ℤ) Internal.SnakyRows011G.named_envelope_602_21_last
def Internal.SnakyRows011G.named_envelope_602_23 : List Cell := ([(-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_23_chain : (named_envelope_602_23.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_23_head : (named_envelope_602_23.map Internal.SnakyRows011G.namedCellKey).head? = some (-253 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_23_last : (named_envelope_602_23.map Internal.SnakyRows011G.namedCellKey).getLast? = some (-245 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_24 : List Cell := ([(-2, 12), (-2, 13), (-2, 14), (-2, 15), (-2, 16), (-1, -3), (-1, -2), (-1, -1), (-1, 1)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_24_chain : (named_envelope_602_24.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_24_head : (named_envelope_602_24.map Internal.SnakyRows011G.namedCellKey).head? = some (-244 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_24_last : (named_envelope_602_24.map Internal.SnakyRows011G.namedCellKey).getLast? = some (-127 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_22 : List Cell := Internal.SnakyRows011G.named_envelope_602_23 ++ Internal.SnakyRows011G.named_envelope_602_24
theorem Internal.SnakyRows011G.named_envelope_602_22_chain : (named_envelope_602_22.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_23 Internal.SnakyRows011G.named_envelope_602_24 (-245 : ℤ) (-244 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_23_chain Internal.SnakyRows011G.named_envelope_602_24_chain Internal.SnakyRows011G.named_envelope_602_23_last Internal.SnakyRows011G.named_envelope_602_24_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_22_head : (named_envelope_602_22.map Internal.SnakyRows011G.namedCellKey).head? = some (-253 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_23 Internal.SnakyRows011G.named_envelope_602_24 (-253 : ℤ) Internal.SnakyRows011G.named_envelope_602_23_head
theorem Internal.SnakyRows011G.named_envelope_602_22_last : (named_envelope_602_22.map Internal.SnakyRows011G.namedCellKey).getLast? = some (-127 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_23 Internal.SnakyRows011G.named_envelope_602_24 (-127 : ℤ) Internal.SnakyRows011G.named_envelope_602_24_last
def Internal.SnakyRows011G.named_envelope_602_18 : List Cell := Internal.SnakyRows011G.named_envelope_602_19 ++ Internal.SnakyRows011G.named_envelope_602_22
theorem Internal.SnakyRows011G.named_envelope_602_18_chain : (named_envelope_602_18.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_19 Internal.SnakyRows011G.named_envelope_602_22 (-254 : ℤ) (-253 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_19_chain Internal.SnakyRows011G.named_envelope_602_22_chain Internal.SnakyRows011G.named_envelope_602_19_last Internal.SnakyRows011G.named_envelope_602_22_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_18_head : (named_envelope_602_18.map Internal.SnakyRows011G.namedCellKey).head? = some (-379 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_19 Internal.SnakyRows011G.named_envelope_602_22 (-379 : ℤ) Internal.SnakyRows011G.named_envelope_602_19_head
theorem Internal.SnakyRows011G.named_envelope_602_18_last : (named_envelope_602_18.map Internal.SnakyRows011G.namedCellKey).getLast? = some (-127 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_19 Internal.SnakyRows011G.named_envelope_602_22 (-127 : ℤ) Internal.SnakyRows011G.named_envelope_602_22_last
def Internal.SnakyRows011G.named_envelope_602_27 : List Cell := ([(-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_27_chain : (named_envelope_602_27.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_27_head : (named_envelope_602_27.map Internal.SnakyRows011G.namedCellKey).head? = some (-126 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_27_last : (named_envelope_602_27.map Internal.SnakyRows011G.namedCellKey).getLast? = some (-119 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_28 : List Cell := ([(-1, 10), (-1, 11), (-1, 12), (-1, 13), (-1, 14), (-1, 15), (0, -3), (0, -2), (0, -1)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_28_chain : (named_envelope_602_28.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_28_head : (named_envelope_602_28.map Internal.SnakyRows011G.namedCellKey).head? = some (-118 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_28_last : (named_envelope_602_28.map Internal.SnakyRows011G.namedCellKey).getLast? = some (-1 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_26 : List Cell := Internal.SnakyRows011G.named_envelope_602_27 ++ Internal.SnakyRows011G.named_envelope_602_28
theorem Internal.SnakyRows011G.named_envelope_602_26_chain : (named_envelope_602_26.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_27 Internal.SnakyRows011G.named_envelope_602_28 (-119 : ℤ) (-118 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_27_chain Internal.SnakyRows011G.named_envelope_602_28_chain Internal.SnakyRows011G.named_envelope_602_27_last Internal.SnakyRows011G.named_envelope_602_28_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_26_head : (named_envelope_602_26.map Internal.SnakyRows011G.namedCellKey).head? = some (-126 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_27 Internal.SnakyRows011G.named_envelope_602_28 (-126 : ℤ) Internal.SnakyRows011G.named_envelope_602_27_head
theorem Internal.SnakyRows011G.named_envelope_602_26_last : (named_envelope_602_26.map Internal.SnakyRows011G.namedCellKey).getLast? = some (-1 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_27 Internal.SnakyRows011G.named_envelope_602_28 (-1 : ℤ) Internal.SnakyRows011G.named_envelope_602_28_last
def Internal.SnakyRows011G.named_envelope_602_30 : List Cell := ([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_30_chain : (named_envelope_602_30.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_30_head : (named_envelope_602_30.map Internal.SnakyRows011G.namedCellKey).head? = some (0 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_30_last : (named_envelope_602_30.map Internal.SnakyRows011G.namedCellKey).getLast? = some (8 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_31 : List Cell := ([(0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (0, 16), (1, -4)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_31_chain : (named_envelope_602_31.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_31_head : (named_envelope_602_31.map Internal.SnakyRows011G.namedCellKey).head? = some (9 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_31_last : (named_envelope_602_31.map Internal.SnakyRows011G.namedCellKey).getLast? = some (124 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_29 : List Cell := Internal.SnakyRows011G.named_envelope_602_30 ++ Internal.SnakyRows011G.named_envelope_602_31
theorem Internal.SnakyRows011G.named_envelope_602_29_chain : (named_envelope_602_29.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_30 Internal.SnakyRows011G.named_envelope_602_31 (8 : ℤ) (9 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_30_chain Internal.SnakyRows011G.named_envelope_602_31_chain Internal.SnakyRows011G.named_envelope_602_30_last Internal.SnakyRows011G.named_envelope_602_31_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_29_head : (named_envelope_602_29.map Internal.SnakyRows011G.namedCellKey).head? = some (0 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_30 Internal.SnakyRows011G.named_envelope_602_31 (0 : ℤ) Internal.SnakyRows011G.named_envelope_602_30_head
theorem Internal.SnakyRows011G.named_envelope_602_29_last : (named_envelope_602_29.map Internal.SnakyRows011G.namedCellKey).getLast? = some (124 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_30 Internal.SnakyRows011G.named_envelope_602_31 (124 : ℤ) Internal.SnakyRows011G.named_envelope_602_31_last
def Internal.SnakyRows011G.named_envelope_602_25 : List Cell := Internal.SnakyRows011G.named_envelope_602_26 ++ Internal.SnakyRows011G.named_envelope_602_29
theorem Internal.SnakyRows011G.named_envelope_602_25_chain : (named_envelope_602_25.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_26 Internal.SnakyRows011G.named_envelope_602_29 (-1 : ℤ) (0 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_26_chain Internal.SnakyRows011G.named_envelope_602_29_chain Internal.SnakyRows011G.named_envelope_602_26_last Internal.SnakyRows011G.named_envelope_602_29_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_25_head : (named_envelope_602_25.map Internal.SnakyRows011G.namedCellKey).head? = some (-126 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_26 Internal.SnakyRows011G.named_envelope_602_29 (-126 : ℤ) Internal.SnakyRows011G.named_envelope_602_26_head
theorem Internal.SnakyRows011G.named_envelope_602_25_last : (named_envelope_602_25.map Internal.SnakyRows011G.namedCellKey).getLast? = some (124 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_26 Internal.SnakyRows011G.named_envelope_602_29 (124 : ℤ) Internal.SnakyRows011G.named_envelope_602_29_last
def Internal.SnakyRows011G.named_envelope_602_17 : List Cell := Internal.SnakyRows011G.named_envelope_602_18 ++ Internal.SnakyRows011G.named_envelope_602_25
theorem Internal.SnakyRows011G.named_envelope_602_17_chain : (named_envelope_602_17.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_18 Internal.SnakyRows011G.named_envelope_602_25 (-127 : ℤ) (-126 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_18_chain Internal.SnakyRows011G.named_envelope_602_25_chain Internal.SnakyRows011G.named_envelope_602_18_last Internal.SnakyRows011G.named_envelope_602_25_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_17_head : (named_envelope_602_17.map Internal.SnakyRows011G.namedCellKey).head? = some (-379 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_18 Internal.SnakyRows011G.named_envelope_602_25 (-379 : ℤ) Internal.SnakyRows011G.named_envelope_602_18_head
theorem Internal.SnakyRows011G.named_envelope_602_17_last : (named_envelope_602_17.map Internal.SnakyRows011G.namedCellKey).getLast? = some (124 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_18 Internal.SnakyRows011G.named_envelope_602_25 (124 : ℤ) Internal.SnakyRows011G.named_envelope_602_25_last
def Internal.SnakyRows011G.named_envelope_602_1 : List Cell := Internal.SnakyRows011G.named_envelope_602_2 ++ Internal.SnakyRows011G.named_envelope_602_17
theorem Internal.SnakyRows011G.named_envelope_602_1_chain : (named_envelope_602_1.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_2 Internal.SnakyRows011G.named_envelope_602_17 (-380 : ℤ) (-379 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_2_chain Internal.SnakyRows011G.named_envelope_602_17_chain Internal.SnakyRows011G.named_envelope_602_2_last Internal.SnakyRows011G.named_envelope_602_17_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_1_head : (named_envelope_602_1.map Internal.SnakyRows011G.namedCellKey).head? = some (-1153 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_2 Internal.SnakyRows011G.named_envelope_602_17 (-1153 : ℤ) Internal.SnakyRows011G.named_envelope_602_2_head
theorem Internal.SnakyRows011G.named_envelope_602_1_last : (named_envelope_602_1.map Internal.SnakyRows011G.namedCellKey).getLast? = some (124 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_2 Internal.SnakyRows011G.named_envelope_602_17 (124 : ℤ) Internal.SnakyRows011G.named_envelope_602_17_last
def Internal.SnakyRows011G.named_envelope_602_36 : List Cell := ([(1, -3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_36_chain : (named_envelope_602_36.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_36_head : (named_envelope_602_36.map Internal.SnakyRows011G.namedCellKey).head? = some (125 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_36_last : (named_envelope_602_36.map Internal.SnakyRows011G.namedCellKey).getLast? = some (133 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_37 : List Cell := ([(1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (1, 14)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_37_chain : (named_envelope_602_37.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_37_head : (named_envelope_602_37.map Internal.SnakyRows011G.namedCellKey).head? = some (134 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_37_last : (named_envelope_602_37.map Internal.SnakyRows011G.namedCellKey).getLast? = some (142 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_35 : List Cell := Internal.SnakyRows011G.named_envelope_602_36 ++ Internal.SnakyRows011G.named_envelope_602_37
theorem Internal.SnakyRows011G.named_envelope_602_35_chain : (named_envelope_602_35.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_36 Internal.SnakyRows011G.named_envelope_602_37 (133 : ℤ) (134 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_36_chain Internal.SnakyRows011G.named_envelope_602_37_chain Internal.SnakyRows011G.named_envelope_602_36_last Internal.SnakyRows011G.named_envelope_602_37_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_35_head : (named_envelope_602_35.map Internal.SnakyRows011G.namedCellKey).head? = some (125 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_36 Internal.SnakyRows011G.named_envelope_602_37 (125 : ℤ) Internal.SnakyRows011G.named_envelope_602_36_head
theorem Internal.SnakyRows011G.named_envelope_602_35_last : (named_envelope_602_35.map Internal.SnakyRows011G.namedCellKey).getLast? = some (142 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_36 Internal.SnakyRows011G.named_envelope_602_37 (142 : ℤ) Internal.SnakyRows011G.named_envelope_602_37_last
def Internal.SnakyRows011G.named_envelope_602_39 : List Cell := ([(2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_39_chain : (named_envelope_602_39.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_39_head : (named_envelope_602_39.map Internal.SnakyRows011G.namedCellKey).head? = some (253 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_39_last : (named_envelope_602_39.map Internal.SnakyRows011G.namedCellKey).getLast? = some (261 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_40 : List Cell := ([(2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_40_chain : (named_envelope_602_40.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_40_head : (named_envelope_602_40.map Internal.SnakyRows011G.namedCellKey).head? = some (262 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_40_last : (named_envelope_602_40.map Internal.SnakyRows011G.namedCellKey).getLast? = some (270 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_38 : List Cell := Internal.SnakyRows011G.named_envelope_602_39 ++ Internal.SnakyRows011G.named_envelope_602_40
theorem Internal.SnakyRows011G.named_envelope_602_38_chain : (named_envelope_602_38.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_39 Internal.SnakyRows011G.named_envelope_602_40 (261 : ℤ) (262 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_39_chain Internal.SnakyRows011G.named_envelope_602_40_chain Internal.SnakyRows011G.named_envelope_602_39_last Internal.SnakyRows011G.named_envelope_602_40_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_38_head : (named_envelope_602_38.map Internal.SnakyRows011G.namedCellKey).head? = some (253 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_39 Internal.SnakyRows011G.named_envelope_602_40 (253 : ℤ) Internal.SnakyRows011G.named_envelope_602_39_head
theorem Internal.SnakyRows011G.named_envelope_602_38_last : (named_envelope_602_38.map Internal.SnakyRows011G.namedCellKey).getLast? = some (270 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_39 Internal.SnakyRows011G.named_envelope_602_40 (270 : ℤ) Internal.SnakyRows011G.named_envelope_602_40_last
def Internal.SnakyRows011G.named_envelope_602_34 : List Cell := Internal.SnakyRows011G.named_envelope_602_35 ++ Internal.SnakyRows011G.named_envelope_602_38
theorem Internal.SnakyRows011G.named_envelope_602_34_chain : (named_envelope_602_34.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_35 Internal.SnakyRows011G.named_envelope_602_38 (142 : ℤ) (253 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_35_chain Internal.SnakyRows011G.named_envelope_602_38_chain Internal.SnakyRows011G.named_envelope_602_35_last Internal.SnakyRows011G.named_envelope_602_38_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_34_head : (named_envelope_602_34.map Internal.SnakyRows011G.namedCellKey).head? = some (125 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_35 Internal.SnakyRows011G.named_envelope_602_38 (125 : ℤ) Internal.SnakyRows011G.named_envelope_602_35_head
theorem Internal.SnakyRows011G.named_envelope_602_34_last : (named_envelope_602_34.map Internal.SnakyRows011G.namedCellKey).getLast? = some (270 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_35 Internal.SnakyRows011G.named_envelope_602_38 (270 : ℤ) Internal.SnakyRows011G.named_envelope_602_38_last
def Internal.SnakyRows011G.named_envelope_602_43 : List Cell := ([(3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_43_chain : (named_envelope_602_43.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_43_head : (named_envelope_602_43.map Internal.SnakyRows011G.namedCellKey).head? = some (381 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_43_last : (named_envelope_602_43.map Internal.SnakyRows011G.namedCellKey).getLast? = some (388 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_44 : List Cell := ([(3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_44_chain : (named_envelope_602_44.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_44_head : (named_envelope_602_44.map Internal.SnakyRows011G.namedCellKey).head? = some (389 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_44_last : (named_envelope_602_44.map Internal.SnakyRows011G.namedCellKey).getLast? = some (397 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_42 : List Cell := Internal.SnakyRows011G.named_envelope_602_43 ++ Internal.SnakyRows011G.named_envelope_602_44
theorem Internal.SnakyRows011G.named_envelope_602_42_chain : (named_envelope_602_42.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_43 Internal.SnakyRows011G.named_envelope_602_44 (388 : ℤ) (389 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_43_chain Internal.SnakyRows011G.named_envelope_602_44_chain Internal.SnakyRows011G.named_envelope_602_43_last Internal.SnakyRows011G.named_envelope_602_44_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_42_head : (named_envelope_602_42.map Internal.SnakyRows011G.namedCellKey).head? = some (381 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_43 Internal.SnakyRows011G.named_envelope_602_44 (381 : ℤ) Internal.SnakyRows011G.named_envelope_602_43_head
theorem Internal.SnakyRows011G.named_envelope_602_42_last : (named_envelope_602_42.map Internal.SnakyRows011G.namedCellKey).getLast? = some (397 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_43 Internal.SnakyRows011G.named_envelope_602_44 (397 : ℤ) Internal.SnakyRows011G.named_envelope_602_44_last
def Internal.SnakyRows011G.named_envelope_602_46 : List Cell := ([(3, 14), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_46_chain : (named_envelope_602_46.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_46_head : (named_envelope_602_46.map Internal.SnakyRows011G.namedCellKey).head? = some (398 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_46_last : (named_envelope_602_46.map Internal.SnakyRows011G.namedCellKey).getLast? = some (516 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_47 : List Cell := ([(4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_47_chain : (named_envelope_602_47.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_47_head : (named_envelope_602_47.map Internal.SnakyRows011G.namedCellKey).head? = some (517 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_47_last : (named_envelope_602_47.map Internal.SnakyRows011G.namedCellKey).getLast? = some (525 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_45 : List Cell := Internal.SnakyRows011G.named_envelope_602_46 ++ Internal.SnakyRows011G.named_envelope_602_47
theorem Internal.SnakyRows011G.named_envelope_602_45_chain : (named_envelope_602_45.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_46 Internal.SnakyRows011G.named_envelope_602_47 (516 : ℤ) (517 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_46_chain Internal.SnakyRows011G.named_envelope_602_47_chain Internal.SnakyRows011G.named_envelope_602_46_last Internal.SnakyRows011G.named_envelope_602_47_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_45_head : (named_envelope_602_45.map Internal.SnakyRows011G.namedCellKey).head? = some (398 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_46 Internal.SnakyRows011G.named_envelope_602_47 (398 : ℤ) Internal.SnakyRows011G.named_envelope_602_46_head
theorem Internal.SnakyRows011G.named_envelope_602_45_last : (named_envelope_602_45.map Internal.SnakyRows011G.namedCellKey).getLast? = some (525 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_46 Internal.SnakyRows011G.named_envelope_602_47 (525 : ℤ) Internal.SnakyRows011G.named_envelope_602_47_last
def Internal.SnakyRows011G.named_envelope_602_41 : List Cell := Internal.SnakyRows011G.named_envelope_602_42 ++ Internal.SnakyRows011G.named_envelope_602_45
theorem Internal.SnakyRows011G.named_envelope_602_41_chain : (named_envelope_602_41.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_42 Internal.SnakyRows011G.named_envelope_602_45 (397 : ℤ) (398 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_42_chain Internal.SnakyRows011G.named_envelope_602_45_chain Internal.SnakyRows011G.named_envelope_602_42_last Internal.SnakyRows011G.named_envelope_602_45_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_41_head : (named_envelope_602_41.map Internal.SnakyRows011G.namedCellKey).head? = some (381 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_42 Internal.SnakyRows011G.named_envelope_602_45 (381 : ℤ) Internal.SnakyRows011G.named_envelope_602_42_head
theorem Internal.SnakyRows011G.named_envelope_602_41_last : (named_envelope_602_41.map Internal.SnakyRows011G.namedCellKey).getLast? = some (525 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_42 Internal.SnakyRows011G.named_envelope_602_45 (525 : ℤ) Internal.SnakyRows011G.named_envelope_602_45_last
def Internal.SnakyRows011G.named_envelope_602_33 : List Cell := Internal.SnakyRows011G.named_envelope_602_34 ++ Internal.SnakyRows011G.named_envelope_602_41
theorem Internal.SnakyRows011G.named_envelope_602_33_chain : (named_envelope_602_33.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_34 Internal.SnakyRows011G.named_envelope_602_41 (270 : ℤ) (381 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_34_chain Internal.SnakyRows011G.named_envelope_602_41_chain Internal.SnakyRows011G.named_envelope_602_34_last Internal.SnakyRows011G.named_envelope_602_41_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_33_head : (named_envelope_602_33.map Internal.SnakyRows011G.namedCellKey).head? = some (125 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_34 Internal.SnakyRows011G.named_envelope_602_41 (125 : ℤ) Internal.SnakyRows011G.named_envelope_602_34_head
theorem Internal.SnakyRows011G.named_envelope_602_33_last : (named_envelope_602_33.map Internal.SnakyRows011G.namedCellKey).getLast? = some (525 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_34 Internal.SnakyRows011G.named_envelope_602_41 (525 : ℤ) Internal.SnakyRows011G.named_envelope_602_41_last
def Internal.SnakyRows011G.named_envelope_602_51 : List Cell := ([(4, 14), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_51_chain : (named_envelope_602_51.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_51_head : (named_envelope_602_51.map Internal.SnakyRows011G.namedCellKey).head? = some (526 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_51_last : (named_envelope_602_51.map Internal.SnakyRows011G.namedCellKey).getLast? = some (644 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_52 : List Cell := ([(5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, 0)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_52_chain : (named_envelope_602_52.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_52_head : (named_envelope_602_52.map Internal.SnakyRows011G.namedCellKey).head? = some (645 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_52_last : (named_envelope_602_52.map Internal.SnakyRows011G.namedCellKey).getLast? = some (768 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_50 : List Cell := Internal.SnakyRows011G.named_envelope_602_51 ++ Internal.SnakyRows011G.named_envelope_602_52
theorem Internal.SnakyRows011G.named_envelope_602_50_chain : (named_envelope_602_50.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_51 Internal.SnakyRows011G.named_envelope_602_52 (644 : ℤ) (645 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_51_chain Internal.SnakyRows011G.named_envelope_602_52_chain Internal.SnakyRows011G.named_envelope_602_51_last Internal.SnakyRows011G.named_envelope_602_52_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_50_head : (named_envelope_602_50.map Internal.SnakyRows011G.namedCellKey).head? = some (526 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_51 Internal.SnakyRows011G.named_envelope_602_52 (526 : ℤ) Internal.SnakyRows011G.named_envelope_602_51_head
theorem Internal.SnakyRows011G.named_envelope_602_50_last : (named_envelope_602_50.map Internal.SnakyRows011G.namedCellKey).getLast? = some (768 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_51 Internal.SnakyRows011G.named_envelope_602_52 (768 : ℤ) Internal.SnakyRows011G.named_envelope_602_52_last
def Internal.SnakyRows011G.named_envelope_602_54 : List Cell := ([(6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_54_chain : (named_envelope_602_54.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_54_head : (named_envelope_602_54.map Internal.SnakyRows011G.namedCellKey).head? = some (769 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_54_last : (named_envelope_602_54.map Internal.SnakyRows011G.namedCellKey).getLast? = some (777 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_55 : List Cell := ([(6, 10), (6, 11), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_55_chain : (named_envelope_602_55.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_55_head : (named_envelope_602_55.map Internal.SnakyRows011G.namedCellKey).head? = some (778 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_55_last : (named_envelope_602_55.map Internal.SnakyRows011G.namedCellKey).getLast? = some (902 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_53 : List Cell := Internal.SnakyRows011G.named_envelope_602_54 ++ Internal.SnakyRows011G.named_envelope_602_55
theorem Internal.SnakyRows011G.named_envelope_602_53_chain : (named_envelope_602_53.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_54 Internal.SnakyRows011G.named_envelope_602_55 (777 : ℤ) (778 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_54_chain Internal.SnakyRows011G.named_envelope_602_55_chain Internal.SnakyRows011G.named_envelope_602_54_last Internal.SnakyRows011G.named_envelope_602_55_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_53_head : (named_envelope_602_53.map Internal.SnakyRows011G.namedCellKey).head? = some (769 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_54 Internal.SnakyRows011G.named_envelope_602_55 (769 : ℤ) Internal.SnakyRows011G.named_envelope_602_54_head
theorem Internal.SnakyRows011G.named_envelope_602_53_last : (named_envelope_602_53.map Internal.SnakyRows011G.namedCellKey).getLast? = some (902 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_54 Internal.SnakyRows011G.named_envelope_602_55 (902 : ℤ) Internal.SnakyRows011G.named_envelope_602_55_last
def Internal.SnakyRows011G.named_envelope_602_49 : List Cell := Internal.SnakyRows011G.named_envelope_602_50 ++ Internal.SnakyRows011G.named_envelope_602_53
theorem Internal.SnakyRows011G.named_envelope_602_49_chain : (named_envelope_602_49.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_50 Internal.SnakyRows011G.named_envelope_602_53 (768 : ℤ) (769 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_50_chain Internal.SnakyRows011G.named_envelope_602_53_chain Internal.SnakyRows011G.named_envelope_602_50_last Internal.SnakyRows011G.named_envelope_602_53_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_49_head : (named_envelope_602_49.map Internal.SnakyRows011G.namedCellKey).head? = some (526 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_50 Internal.SnakyRows011G.named_envelope_602_53 (526 : ℤ) Internal.SnakyRows011G.named_envelope_602_50_head
theorem Internal.SnakyRows011G.named_envelope_602_49_last : (named_envelope_602_49.map Internal.SnakyRows011G.namedCellKey).getLast? = some (902 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_50 Internal.SnakyRows011G.named_envelope_602_53 (902 : ℤ) Internal.SnakyRows011G.named_envelope_602_53_last
def Internal.SnakyRows011G.named_envelope_602_58 : List Cell := ([(7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 0), (8, 1), (8, 2)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_58_chain : (named_envelope_602_58.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_58_head : (named_envelope_602_58.map Internal.SnakyRows011G.namedCellKey).head? = some (903 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_58_last : (named_envelope_602_58.map Internal.SnakyRows011G.namedCellKey).getLast? = some (1026 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_59 : List Cell := ([(8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 3)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_59_chain : (named_envelope_602_59.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_59_head : (named_envelope_602_59.map Internal.SnakyRows011G.namedCellKey).head? = some (1027 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_59_last : (named_envelope_602_59.map Internal.SnakyRows011G.namedCellKey).getLast? = some (1155 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_57 : List Cell := Internal.SnakyRows011G.named_envelope_602_58 ++ Internal.SnakyRows011G.named_envelope_602_59
theorem Internal.SnakyRows011G.named_envelope_602_57_chain : (named_envelope_602_57.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_58 Internal.SnakyRows011G.named_envelope_602_59 (1026 : ℤ) (1027 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_58_chain Internal.SnakyRows011G.named_envelope_602_59_chain Internal.SnakyRows011G.named_envelope_602_58_last Internal.SnakyRows011G.named_envelope_602_59_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_57_head : (named_envelope_602_57.map Internal.SnakyRows011G.namedCellKey).head? = some (903 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_58 Internal.SnakyRows011G.named_envelope_602_59 (903 : ℤ) Internal.SnakyRows011G.named_envelope_602_58_head
theorem Internal.SnakyRows011G.named_envelope_602_57_last : (named_envelope_602_57.map Internal.SnakyRows011G.namedCellKey).getLast? = some (1155 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_58 Internal.SnakyRows011G.named_envelope_602_59 (1155 : ℤ) Internal.SnakyRows011G.named_envelope_602_59_last
def Internal.SnakyRows011G.named_envelope_602_61 : List Cell := ([(9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (10, 3), (10, 4), (10, 5)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_61_chain : (named_envelope_602_61.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_61_head : (named_envelope_602_61.map Internal.SnakyRows011G.namedCellKey).head? = some (1156 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_61_last : (named_envelope_602_61.map Internal.SnakyRows011G.namedCellKey).getLast? = some (1285 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_62 : List Cell := ([(10, 6), (10, 7), (10, 8), (10, 9), (11, 3), (11, 4), (11, 5), (12, 3), (12, 5)] : List Cell)
theorem Internal.SnakyRows011G.named_envelope_602_62_chain : (named_envelope_602_62.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_62_head : (named_envelope_602_62.map Internal.SnakyRows011G.namedCellKey).head? = some (1286 : ℤ) := by decide
theorem Internal.SnakyRows011G.named_envelope_602_62_last : (named_envelope_602_62.map Internal.SnakyRows011G.namedCellKey).getLast? = some (1541 : ℤ) := by decide
def Internal.SnakyRows011G.named_envelope_602_60 : List Cell := Internal.SnakyRows011G.named_envelope_602_61 ++ Internal.SnakyRows011G.named_envelope_602_62
theorem Internal.SnakyRows011G.named_envelope_602_60_chain : (named_envelope_602_60.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_61 Internal.SnakyRows011G.named_envelope_602_62 (1285 : ℤ) (1286 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_61_chain Internal.SnakyRows011G.named_envelope_602_62_chain Internal.SnakyRows011G.named_envelope_602_61_last Internal.SnakyRows011G.named_envelope_602_62_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_60_head : (named_envelope_602_60.map Internal.SnakyRows011G.namedCellKey).head? = some (1156 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_61 Internal.SnakyRows011G.named_envelope_602_62 (1156 : ℤ) Internal.SnakyRows011G.named_envelope_602_61_head
theorem Internal.SnakyRows011G.named_envelope_602_60_last : (named_envelope_602_60.map Internal.SnakyRows011G.namedCellKey).getLast? = some (1541 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_61 Internal.SnakyRows011G.named_envelope_602_62 (1541 : ℤ) Internal.SnakyRows011G.named_envelope_602_62_last
def Internal.SnakyRows011G.named_envelope_602_56 : List Cell := Internal.SnakyRows011G.named_envelope_602_57 ++ Internal.SnakyRows011G.named_envelope_602_60
theorem Internal.SnakyRows011G.named_envelope_602_56_chain : (named_envelope_602_56.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_57 Internal.SnakyRows011G.named_envelope_602_60 (1155 : ℤ) (1156 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_57_chain Internal.SnakyRows011G.named_envelope_602_60_chain Internal.SnakyRows011G.named_envelope_602_57_last Internal.SnakyRows011G.named_envelope_602_60_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_56_head : (named_envelope_602_56.map Internal.SnakyRows011G.namedCellKey).head? = some (903 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_57 Internal.SnakyRows011G.named_envelope_602_60 (903 : ℤ) Internal.SnakyRows011G.named_envelope_602_57_head
theorem Internal.SnakyRows011G.named_envelope_602_56_last : (named_envelope_602_56.map Internal.SnakyRows011G.namedCellKey).getLast? = some (1541 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_57 Internal.SnakyRows011G.named_envelope_602_60 (1541 : ℤ) Internal.SnakyRows011G.named_envelope_602_60_last
def Internal.SnakyRows011G.named_envelope_602_48 : List Cell := Internal.SnakyRows011G.named_envelope_602_49 ++ Internal.SnakyRows011G.named_envelope_602_56
theorem Internal.SnakyRows011G.named_envelope_602_48_chain : (named_envelope_602_48.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_49 Internal.SnakyRows011G.named_envelope_602_56 (902 : ℤ) (903 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_49_chain Internal.SnakyRows011G.named_envelope_602_56_chain Internal.SnakyRows011G.named_envelope_602_49_last Internal.SnakyRows011G.named_envelope_602_56_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_48_head : (named_envelope_602_48.map Internal.SnakyRows011G.namedCellKey).head? = some (526 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_49 Internal.SnakyRows011G.named_envelope_602_56 (526 : ℤ) Internal.SnakyRows011G.named_envelope_602_49_head
theorem Internal.SnakyRows011G.named_envelope_602_48_last : (named_envelope_602_48.map Internal.SnakyRows011G.namedCellKey).getLast? = some (1541 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_49 Internal.SnakyRows011G.named_envelope_602_56 (1541 : ℤ) Internal.SnakyRows011G.named_envelope_602_56_last
def Internal.SnakyRows011G.named_envelope_602_32 : List Cell := Internal.SnakyRows011G.named_envelope_602_33 ++ Internal.SnakyRows011G.named_envelope_602_48
theorem Internal.SnakyRows011G.named_envelope_602_32_chain : (named_envelope_602_32.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_33 Internal.SnakyRows011G.named_envelope_602_48 (525 : ℤ) (526 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_33_chain Internal.SnakyRows011G.named_envelope_602_48_chain Internal.SnakyRows011G.named_envelope_602_33_last Internal.SnakyRows011G.named_envelope_602_48_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_32_head : (named_envelope_602_32.map Internal.SnakyRows011G.namedCellKey).head? = some (125 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_33 Internal.SnakyRows011G.named_envelope_602_48 (125 : ℤ) Internal.SnakyRows011G.named_envelope_602_33_head
theorem Internal.SnakyRows011G.named_envelope_602_32_last : (named_envelope_602_32.map Internal.SnakyRows011G.namedCellKey).getLast? = some (1541 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_33 Internal.SnakyRows011G.named_envelope_602_48 (1541 : ℤ) Internal.SnakyRows011G.named_envelope_602_48_last
def Internal.SnakyRows011G.named_envelope_602_0 : List Cell := Internal.SnakyRows011G.named_envelope_602_1 ++ Internal.SnakyRows011G.named_envelope_602_32
theorem Internal.SnakyRows011G.named_envelope_602_0_chain : (named_envelope_602_0.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011G.named_chain_append Internal.SnakyRows011G.named_envelope_602_1 Internal.SnakyRows011G.named_envelope_602_32 (124 : ℤ) (125 : ℤ)
    Internal.SnakyRows011G.named_envelope_602_1_chain Internal.SnakyRows011G.named_envelope_602_32_chain Internal.SnakyRows011G.named_envelope_602_1_last Internal.SnakyRows011G.named_envelope_602_32_head (by decide)
theorem Internal.SnakyRows011G.named_envelope_602_0_head : (named_envelope_602_0.map Internal.SnakyRows011G.namedCellKey).head? = some (-1153 : ℤ) :=
  Internal.SnakyRows011G.named_head_append Internal.SnakyRows011G.named_envelope_602_1 Internal.SnakyRows011G.named_envelope_602_32 (-1153 : ℤ) Internal.SnakyRows011G.named_envelope_602_1_head
theorem Internal.SnakyRows011G.named_envelope_602_0_last : (named_envelope_602_0.map Internal.SnakyRows011G.namedCellKey).getLast? = some (1541 : ℤ) :=
  Internal.SnakyRows011G.named_last_append Internal.SnakyRows011G.named_envelope_602_1 Internal.SnakyRows011G.named_envelope_602_32 (1541 : ℤ) Internal.SnakyRows011G.named_envelope_602_32_last
theorem Internal.SnakyRows011G.named_envelope_602_nodup : (Internal.SnakyRows011G.named_envelope_602_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows011G.named_nodup_of_chain Internal.SnakyRows011G.named_envelope_602_0 Internal.SnakyRows011G.named_envelope_602_0_chain
def envelope_602 : Finset Cell := ⟨(Internal.SnakyRows011G.named_envelope_602_0 : Multiset Cell), Internal.SnakyRows011G.named_envelope_602_nodup⟩
def childrenC_602 : Fin 5 → Finset Cell := ![(placedSet 0 (0, 3) required_553), (placedSet 4 (0, -1) required_467), (placedSet 0 (1, 3) required_592), (placedSet 6 (0, -1) required_437), (placedSet 4 (-1, 3) required_236)]
def childrenD_602 : Fin 5 → Finset Cell := ![(placedSet 0 (0, 3) envelope_553), (placedSet 4 (0, -1) envelope_467), (placedSet 0 (1, 3) envelope_592), (placedSet 6 (0, -1) envelope_437), (placedSet 4 (-1, 3) envelope_236)]
theorem common_sub_602 : commonEnvelope childrenD_602 ⊆ insert (0, 0) required_602 := by decide
theorem child_required_sub_602 : ∀ j, childrenC_602 j ⊆ insert (0, 0) required_602 := by decide
theorem Internal.SnakyRows011G.containment_602_0 :
    placedSet 0 (0, 3) envelope_553 ⊆ envelope_602 := by decide +kernel
theorem Internal.SnakyRows011G.containment_602_1 :
    placedSet 4 (0, -1) envelope_467 ⊆ envelope_602 := by decide
theorem Internal.SnakyRows011G.containment_602_2 :
    placedSet 0 (1, 3) envelope_592 ⊆ envelope_602 := by decide +kernel
theorem Internal.SnakyRows011G.containment_602_3 :
    placedSet 6 (0, -1) envelope_437 ⊆ envelope_602 := by decide
theorem Internal.SnakyRows011G.containment_602_4 :
    placedSet 4 (-1, 3) envelope_236 ⊆ envelope_602 := by decide
theorem child_envelope_sub_602 : ∀ j, childrenD_602 j ⊆ envelope_602 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows011G.containment_602_0
  · exact Internal.SnakyRows011G.containment_602_1
  · exact Internal.SnakyRows011G.containment_602_2
  · exact Internal.SnakyRows011G.containment_602_3
  · exact Internal.SnakyRows011G.containment_602_4
theorem pivot_mem_602 : (0, 0) ∈ envelope_602 := by decide
theorem children_work_602 : ∀ j, Template HasSnaky 28 (childrenC_602 j) (childrenD_602 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_553 0 (0, 3)).mono (by decide)
  · exact (placed_template_map row_works_467 4 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_592 0 (1, 3)).mono (by decide)
  · exact (placed_template_map row_works_437 6 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_236 4 (-1, 3)).mono (by decide)
theorem row_works_602 : Template HasSnaky 29 required_602 envelope_602 := by
  refine compose HasSnaky 28 childrenC_602 childrenD_602 children_work_602 (0, 0)
    required_602 envelope_602 pivot_mem_602 child_required_sub_602 child_envelope_sub_602 ?_
  intro b hb; exact common_sub_602 (mem_commonEnvelope childrenD_602 b hb)
end SnakyConditional

end OAI
