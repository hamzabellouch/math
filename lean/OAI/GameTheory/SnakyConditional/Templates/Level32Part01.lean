import OAI.GameTheory.SnakyConditional.Templates.Level31Part01

namespace OAI

namespace SnakyConditional
def required_604 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-1, -2), (0, -2)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows011I.named_envelope_604_5 : List Cell := ([(-7, -1), (-6, -1), (-6, 0), (-6, 1), (-6, 6), (-6, 7), (-6, 9), (-5, -1)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_5_chain : (named_envelope_604_5.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_5_head : (named_envelope_604_5.map Internal.SnakyRows011I.namedCellKey).head? = some (-897 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_5_last : (named_envelope_604_5.map Internal.SnakyRows011I.namedCellKey).getLast? = some (-641 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_6 : List Cell := ([(-5, 0), (-5, 1), (-5, 2), (-5, 4), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-4, -1)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_6_chain : (named_envelope_604_6.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_6_head : (named_envelope_604_6.map Internal.SnakyRows011I.namedCellKey).head? = some (-640 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_6_last : (named_envelope_604_6.map Internal.SnakyRows011I.namedCellKey).getLast? = some (-513 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_4 : List Cell := Internal.SnakyRows011I.named_envelope_604_5 ++ Internal.SnakyRows011I.named_envelope_604_6
theorem Internal.SnakyRows011I.named_envelope_604_4_chain : (named_envelope_604_4.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_5 Internal.SnakyRows011I.named_envelope_604_6 (-641 : ℤ) (-640 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_5_chain Internal.SnakyRows011I.named_envelope_604_6_chain Internal.SnakyRows011I.named_envelope_604_5_last Internal.SnakyRows011I.named_envelope_604_6_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_4_head : (named_envelope_604_4.map Internal.SnakyRows011I.namedCellKey).head? = some (-897 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_5 Internal.SnakyRows011I.named_envelope_604_6 (-897 : ℤ) Internal.SnakyRows011I.named_envelope_604_5_head
theorem Internal.SnakyRows011I.named_envelope_604_4_last : (named_envelope_604_4.map Internal.SnakyRows011I.namedCellKey).getLast? = some (-513 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_5 Internal.SnakyRows011I.named_envelope_604_6 (-513 : ℤ) Internal.SnakyRows011I.named_envelope_604_6_last
def Internal.SnakyRows011I.named_envelope_604_8 : List Cell := ([(-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_8_chain : (named_envelope_604_8.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_8_head : (named_envelope_604_8.map Internal.SnakyRows011I.namedCellKey).head? = some (-512 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_8_last : (named_envelope_604_8.map Internal.SnakyRows011I.namedCellKey).getLast? = some (-504 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_9 : List Cell := ([(-4, 9), (-4, 10), (-4, 11), (-4, 12), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_9_chain : (named_envelope_604_9.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_9_head : (named_envelope_604_9.map Internal.SnakyRows011I.namedCellKey).head? = some (-503 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_9_last : (named_envelope_604_9.map Internal.SnakyRows011I.namedCellKey).getLast? = some (-381 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_7 : List Cell := Internal.SnakyRows011I.named_envelope_604_8 ++ Internal.SnakyRows011I.named_envelope_604_9
theorem Internal.SnakyRows011I.named_envelope_604_7_chain : (named_envelope_604_7.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_8 Internal.SnakyRows011I.named_envelope_604_9 (-504 : ℤ) (-503 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_8_chain Internal.SnakyRows011I.named_envelope_604_9_chain Internal.SnakyRows011I.named_envelope_604_8_last Internal.SnakyRows011I.named_envelope_604_9_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_7_head : (named_envelope_604_7.map Internal.SnakyRows011I.namedCellKey).head? = some (-512 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_8 Internal.SnakyRows011I.named_envelope_604_9 (-512 : ℤ) Internal.SnakyRows011I.named_envelope_604_8_head
theorem Internal.SnakyRows011I.named_envelope_604_7_last : (named_envelope_604_7.map Internal.SnakyRows011I.namedCellKey).getLast? = some (-381 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_8 Internal.SnakyRows011I.named_envelope_604_9 (-381 : ℤ) Internal.SnakyRows011I.named_envelope_604_9_last
def Internal.SnakyRows011I.named_envelope_604_3 : List Cell := Internal.SnakyRows011I.named_envelope_604_4 ++ Internal.SnakyRows011I.named_envelope_604_7
theorem Internal.SnakyRows011I.named_envelope_604_3_chain : (named_envelope_604_3.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_4 Internal.SnakyRows011I.named_envelope_604_7 (-513 : ℤ) (-512 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_4_chain Internal.SnakyRows011I.named_envelope_604_7_chain Internal.SnakyRows011I.named_envelope_604_4_last Internal.SnakyRows011I.named_envelope_604_7_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_3_head : (named_envelope_604_3.map Internal.SnakyRows011I.namedCellKey).head? = some (-897 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_4 Internal.SnakyRows011I.named_envelope_604_7 (-897 : ℤ) Internal.SnakyRows011I.named_envelope_604_4_head
theorem Internal.SnakyRows011I.named_envelope_604_3_last : (named_envelope_604_3.map Internal.SnakyRows011I.namedCellKey).getLast? = some (-381 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_4 Internal.SnakyRows011I.named_envelope_604_7 (-381 : ℤ) Internal.SnakyRows011I.named_envelope_604_7_last
def Internal.SnakyRows011I.named_envelope_604_12 : List Cell := ([(-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_12_chain : (named_envelope_604_12.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_12_head : (named_envelope_604_12.map Internal.SnakyRows011I.namedCellKey).head? = some (-380 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_12_last : (named_envelope_604_12.map Internal.SnakyRows011I.namedCellKey).getLast? = some (-373 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_13 : List Cell := ([(-2, -2), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_13_chain : (named_envelope_604_13.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_13_head : (named_envelope_604_13.map Internal.SnakyRows011I.namedCellKey).head? = some (-258 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_13_last : (named_envelope_604_13.map Internal.SnakyRows011I.namedCellKey).getLast? = some (-249 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_11 : List Cell := Internal.SnakyRows011I.named_envelope_604_12 ++ Internal.SnakyRows011I.named_envelope_604_13
theorem Internal.SnakyRows011I.named_envelope_604_11_chain : (named_envelope_604_11.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_12 Internal.SnakyRows011I.named_envelope_604_13 (-373 : ℤ) (-258 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_12_chain Internal.SnakyRows011I.named_envelope_604_13_chain Internal.SnakyRows011I.named_envelope_604_12_last Internal.SnakyRows011I.named_envelope_604_13_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_11_head : (named_envelope_604_11.map Internal.SnakyRows011I.namedCellKey).head? = some (-380 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_12 Internal.SnakyRows011I.named_envelope_604_13 (-380 : ℤ) Internal.SnakyRows011I.named_envelope_604_12_head
theorem Internal.SnakyRows011I.named_envelope_604_11_last : (named_envelope_604_11.map Internal.SnakyRows011I.namedCellKey).getLast? = some (-249 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_12 Internal.SnakyRows011I.named_envelope_604_13 (-249 : ℤ) Internal.SnakyRows011I.named_envelope_604_13_last
def Internal.SnakyRows011I.named_envelope_604_15 : List Cell := ([(-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-1, -7), (-1, -6)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_15_chain : (named_envelope_604_15.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_15_head : (named_envelope_604_15.map Internal.SnakyRows011I.namedCellKey).head? = some (-248 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_15_last : (named_envelope_604_15.map Internal.SnakyRows011I.namedCellKey).getLast? = some (-134 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_16 : List Cell := ([(-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_16_chain : (named_envelope_604_16.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_16_head : (named_envelope_604_16.map Internal.SnakyRows011I.namedCellKey).head? = some (-133 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_16_last : (named_envelope_604_16.map Internal.SnakyRows011I.namedCellKey).getLast? = some (-124 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_14 : List Cell := Internal.SnakyRows011I.named_envelope_604_15 ++ Internal.SnakyRows011I.named_envelope_604_16
theorem Internal.SnakyRows011I.named_envelope_604_14_chain : (named_envelope_604_14.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_15 Internal.SnakyRows011I.named_envelope_604_16 (-134 : ℤ) (-133 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_15_chain Internal.SnakyRows011I.named_envelope_604_16_chain Internal.SnakyRows011I.named_envelope_604_15_last Internal.SnakyRows011I.named_envelope_604_16_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_14_head : (named_envelope_604_14.map Internal.SnakyRows011I.namedCellKey).head? = some (-248 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_15 Internal.SnakyRows011I.named_envelope_604_16 (-248 : ℤ) Internal.SnakyRows011I.named_envelope_604_15_head
theorem Internal.SnakyRows011I.named_envelope_604_14_last : (named_envelope_604_14.map Internal.SnakyRows011I.namedCellKey).getLast? = some (-124 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_15 Internal.SnakyRows011I.named_envelope_604_16 (-124 : ℤ) Internal.SnakyRows011I.named_envelope_604_16_last
def Internal.SnakyRows011I.named_envelope_604_10 : List Cell := Internal.SnakyRows011I.named_envelope_604_11 ++ Internal.SnakyRows011I.named_envelope_604_14
theorem Internal.SnakyRows011I.named_envelope_604_10_chain : (named_envelope_604_10.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_11 Internal.SnakyRows011I.named_envelope_604_14 (-249 : ℤ) (-248 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_11_chain Internal.SnakyRows011I.named_envelope_604_14_chain Internal.SnakyRows011I.named_envelope_604_11_last Internal.SnakyRows011I.named_envelope_604_14_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_10_head : (named_envelope_604_10.map Internal.SnakyRows011I.namedCellKey).head? = some (-380 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_11 Internal.SnakyRows011I.named_envelope_604_14 (-380 : ℤ) Internal.SnakyRows011I.named_envelope_604_11_head
theorem Internal.SnakyRows011I.named_envelope_604_10_last : (named_envelope_604_10.map Internal.SnakyRows011I.namedCellKey).getLast? = some (-124 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_11 Internal.SnakyRows011I.named_envelope_604_14 (-124 : ℤ) Internal.SnakyRows011I.named_envelope_604_14_last
def Internal.SnakyRows011I.named_envelope_604_2 : List Cell := Internal.SnakyRows011I.named_envelope_604_3 ++ Internal.SnakyRows011I.named_envelope_604_10
theorem Internal.SnakyRows011I.named_envelope_604_2_chain : (named_envelope_604_2.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_3 Internal.SnakyRows011I.named_envelope_604_10 (-381 : ℤ) (-380 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_3_chain Internal.SnakyRows011I.named_envelope_604_10_chain Internal.SnakyRows011I.named_envelope_604_3_last Internal.SnakyRows011I.named_envelope_604_10_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_2_head : (named_envelope_604_2.map Internal.SnakyRows011I.namedCellKey).head? = some (-897 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_3 Internal.SnakyRows011I.named_envelope_604_10 (-897 : ℤ) Internal.SnakyRows011I.named_envelope_604_3_head
theorem Internal.SnakyRows011I.named_envelope_604_2_last : (named_envelope_604_2.map Internal.SnakyRows011I.namedCellKey).getLast? = some (-124 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_3 Internal.SnakyRows011I.named_envelope_604_10 (-124 : ℤ) Internal.SnakyRows011I.named_envelope_604_10_last
def Internal.SnakyRows011I.named_envelope_604_20 : List Cell := ([(-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_20_chain : (named_envelope_604_20.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_20_head : (named_envelope_604_20.map Internal.SnakyRows011I.namedCellKey).head? = some (-123 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_20_last : (named_envelope_604_20.map Internal.SnakyRows011I.namedCellKey).getLast? = some (-116 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_21 : List Cell := ([(-1, 13), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_21_chain : (named_envelope_604_21.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_21_head : (named_envelope_604_21.map Internal.SnakyRows011I.namedCellKey).head? = some (-115 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_21_last : (named_envelope_604_21.map Internal.SnakyRows011I.namedCellKey).getLast? = some (1 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_19 : List Cell := Internal.SnakyRows011I.named_envelope_604_20 ++ Internal.SnakyRows011I.named_envelope_604_21
theorem Internal.SnakyRows011I.named_envelope_604_19_chain : (named_envelope_604_19.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_20 Internal.SnakyRows011I.named_envelope_604_21 (-116 : ℤ) (-115 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_20_chain Internal.SnakyRows011I.named_envelope_604_21_chain Internal.SnakyRows011I.named_envelope_604_20_last Internal.SnakyRows011I.named_envelope_604_21_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_19_head : (named_envelope_604_19.map Internal.SnakyRows011I.namedCellKey).head? = some (-123 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_20 Internal.SnakyRows011I.named_envelope_604_21 (-123 : ℤ) Internal.SnakyRows011I.named_envelope_604_20_head
theorem Internal.SnakyRows011I.named_envelope_604_19_last : (named_envelope_604_19.map Internal.SnakyRows011I.namedCellKey).getLast? = some (1 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_20 Internal.SnakyRows011I.named_envelope_604_21 (1 : ℤ) Internal.SnakyRows011I.named_envelope_604_21_last
def Internal.SnakyRows011I.named_envelope_604_23 : List Cell := ([(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_23_chain : (named_envelope_604_23.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_23_head : (named_envelope_604_23.map Internal.SnakyRows011I.namedCellKey).head? = some (2 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_23_last : (named_envelope_604_23.map Internal.SnakyRows011I.namedCellKey).getLast? = some (10 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_24 : List Cell := ([(0, 11), (0, 12), (0, 13), (0, 14), (1, -6), (1, -5), (1, -4), (1, -3), (1, -1)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_24_chain : (named_envelope_604_24.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_24_head : (named_envelope_604_24.map Internal.SnakyRows011I.namedCellKey).head? = some (11 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_24_last : (named_envelope_604_24.map Internal.SnakyRows011I.namedCellKey).getLast? = some (127 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_22 : List Cell := Internal.SnakyRows011I.named_envelope_604_23 ++ Internal.SnakyRows011I.named_envelope_604_24
theorem Internal.SnakyRows011I.named_envelope_604_22_chain : (named_envelope_604_22.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_23 Internal.SnakyRows011I.named_envelope_604_24 (10 : ℤ) (11 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_23_chain Internal.SnakyRows011I.named_envelope_604_24_chain Internal.SnakyRows011I.named_envelope_604_23_last Internal.SnakyRows011I.named_envelope_604_24_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_22_head : (named_envelope_604_22.map Internal.SnakyRows011I.namedCellKey).head? = some (2 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_23 Internal.SnakyRows011I.named_envelope_604_24 (2 : ℤ) Internal.SnakyRows011I.named_envelope_604_23_head
theorem Internal.SnakyRows011I.named_envelope_604_22_last : (named_envelope_604_22.map Internal.SnakyRows011I.namedCellKey).getLast? = some (127 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_23 Internal.SnakyRows011I.named_envelope_604_24 (127 : ℤ) Internal.SnakyRows011I.named_envelope_604_24_last
def Internal.SnakyRows011I.named_envelope_604_18 : List Cell := Internal.SnakyRows011I.named_envelope_604_19 ++ Internal.SnakyRows011I.named_envelope_604_22
theorem Internal.SnakyRows011I.named_envelope_604_18_chain : (named_envelope_604_18.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_19 Internal.SnakyRows011I.named_envelope_604_22 (1 : ℤ) (2 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_19_chain Internal.SnakyRows011I.named_envelope_604_22_chain Internal.SnakyRows011I.named_envelope_604_19_last Internal.SnakyRows011I.named_envelope_604_22_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_18_head : (named_envelope_604_18.map Internal.SnakyRows011I.namedCellKey).head? = some (-123 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_19 Internal.SnakyRows011I.named_envelope_604_22 (-123 : ℤ) Internal.SnakyRows011I.named_envelope_604_19_head
theorem Internal.SnakyRows011I.named_envelope_604_18_last : (named_envelope_604_18.map Internal.SnakyRows011I.namedCellKey).getLast? = some (127 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_19 Internal.SnakyRows011I.named_envelope_604_22 (127 : ℤ) Internal.SnakyRows011I.named_envelope_604_22_last
def Internal.SnakyRows011I.named_envelope_604_27 : List Cell := ([(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_27_chain : (named_envelope_604_27.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_27_head : (named_envelope_604_27.map Internal.SnakyRows011I.namedCellKey).head? = some (128 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_27_last : (named_envelope_604_27.map Internal.SnakyRows011I.namedCellKey).getLast? = some (136 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_28 : List Cell := ([(1, 9), (1, 10), (1, 11), (1, 12), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_28_chain : (named_envelope_604_28.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_28_head : (named_envelope_604_28.map Internal.SnakyRows011I.namedCellKey).head? = some (137 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_28_last : (named_envelope_604_28.map Internal.SnakyRows011I.namedCellKey).getLast? = some (255 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_26 : List Cell := Internal.SnakyRows011I.named_envelope_604_27 ++ Internal.SnakyRows011I.named_envelope_604_28
theorem Internal.SnakyRows011I.named_envelope_604_26_chain : (named_envelope_604_26.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_27 Internal.SnakyRows011I.named_envelope_604_28 (136 : ℤ) (137 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_27_chain Internal.SnakyRows011I.named_envelope_604_28_chain Internal.SnakyRows011I.named_envelope_604_27_last Internal.SnakyRows011I.named_envelope_604_28_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_26_head : (named_envelope_604_26.map Internal.SnakyRows011I.namedCellKey).head? = some (128 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_27 Internal.SnakyRows011I.named_envelope_604_28 (128 : ℤ) Internal.SnakyRows011I.named_envelope_604_27_head
theorem Internal.SnakyRows011I.named_envelope_604_26_last : (named_envelope_604_26.map Internal.SnakyRows011I.namedCellKey).getLast? = some (255 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_27 Internal.SnakyRows011I.named_envelope_604_28 (255 : ℤ) Internal.SnakyRows011I.named_envelope_604_28_last
def Internal.SnakyRows011I.named_envelope_604_30 : List Cell := ([(2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_30_chain : (named_envelope_604_30.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_30_head : (named_envelope_604_30.map Internal.SnakyRows011I.namedCellKey).head? = some (256 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_30_last : (named_envelope_604_30.map Internal.SnakyRows011I.namedCellKey).getLast? = some (264 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_31 : List Cell := ([(2, 9), (2, 10), (2, 11), (2, 12), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_31_chain : (named_envelope_604_31.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_31_head : (named_envelope_604_31.map Internal.SnakyRows011I.namedCellKey).head? = some (265 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_31_last : (named_envelope_604_31.map Internal.SnakyRows011I.namedCellKey).getLast? = some (384 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_29 : List Cell := Internal.SnakyRows011I.named_envelope_604_30 ++ Internal.SnakyRows011I.named_envelope_604_31
theorem Internal.SnakyRows011I.named_envelope_604_29_chain : (named_envelope_604_29.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_30 Internal.SnakyRows011I.named_envelope_604_31 (264 : ℤ) (265 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_30_chain Internal.SnakyRows011I.named_envelope_604_31_chain Internal.SnakyRows011I.named_envelope_604_30_last Internal.SnakyRows011I.named_envelope_604_31_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_29_head : (named_envelope_604_29.map Internal.SnakyRows011I.namedCellKey).head? = some (256 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_30 Internal.SnakyRows011I.named_envelope_604_31 (256 : ℤ) Internal.SnakyRows011I.named_envelope_604_30_head
theorem Internal.SnakyRows011I.named_envelope_604_29_last : (named_envelope_604_29.map Internal.SnakyRows011I.namedCellKey).getLast? = some (384 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_30 Internal.SnakyRows011I.named_envelope_604_31 (384 : ℤ) Internal.SnakyRows011I.named_envelope_604_31_last
def Internal.SnakyRows011I.named_envelope_604_25 : List Cell := Internal.SnakyRows011I.named_envelope_604_26 ++ Internal.SnakyRows011I.named_envelope_604_29
theorem Internal.SnakyRows011I.named_envelope_604_25_chain : (named_envelope_604_25.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_26 Internal.SnakyRows011I.named_envelope_604_29 (255 : ℤ) (256 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_26_chain Internal.SnakyRows011I.named_envelope_604_29_chain Internal.SnakyRows011I.named_envelope_604_26_last Internal.SnakyRows011I.named_envelope_604_29_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_25_head : (named_envelope_604_25.map Internal.SnakyRows011I.namedCellKey).head? = some (128 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_26 Internal.SnakyRows011I.named_envelope_604_29 (128 : ℤ) Internal.SnakyRows011I.named_envelope_604_26_head
theorem Internal.SnakyRows011I.named_envelope_604_25_last : (named_envelope_604_25.map Internal.SnakyRows011I.namedCellKey).getLast? = some (384 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_26 Internal.SnakyRows011I.named_envelope_604_29 (384 : ℤ) Internal.SnakyRows011I.named_envelope_604_29_last
def Internal.SnakyRows011I.named_envelope_604_17 : List Cell := Internal.SnakyRows011I.named_envelope_604_18 ++ Internal.SnakyRows011I.named_envelope_604_25
theorem Internal.SnakyRows011I.named_envelope_604_17_chain : (named_envelope_604_17.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_18 Internal.SnakyRows011I.named_envelope_604_25 (127 : ℤ) (128 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_18_chain Internal.SnakyRows011I.named_envelope_604_25_chain Internal.SnakyRows011I.named_envelope_604_18_last Internal.SnakyRows011I.named_envelope_604_25_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_17_head : (named_envelope_604_17.map Internal.SnakyRows011I.namedCellKey).head? = some (-123 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_18 Internal.SnakyRows011I.named_envelope_604_25 (-123 : ℤ) Internal.SnakyRows011I.named_envelope_604_18_head
theorem Internal.SnakyRows011I.named_envelope_604_17_last : (named_envelope_604_17.map Internal.SnakyRows011I.namedCellKey).getLast? = some (384 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_18 Internal.SnakyRows011I.named_envelope_604_25 (384 : ℤ) Internal.SnakyRows011I.named_envelope_604_25_last
def Internal.SnakyRows011I.named_envelope_604_1 : List Cell := Internal.SnakyRows011I.named_envelope_604_2 ++ Internal.SnakyRows011I.named_envelope_604_17
theorem Internal.SnakyRows011I.named_envelope_604_1_chain : (named_envelope_604_1.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_2 Internal.SnakyRows011I.named_envelope_604_17 (-124 : ℤ) (-123 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_2_chain Internal.SnakyRows011I.named_envelope_604_17_chain Internal.SnakyRows011I.named_envelope_604_2_last Internal.SnakyRows011I.named_envelope_604_17_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_1_head : (named_envelope_604_1.map Internal.SnakyRows011I.namedCellKey).head? = some (-897 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_2 Internal.SnakyRows011I.named_envelope_604_17 (-897 : ℤ) Internal.SnakyRows011I.named_envelope_604_2_head
theorem Internal.SnakyRows011I.named_envelope_604_1_last : (named_envelope_604_1.map Internal.SnakyRows011I.namedCellKey).getLast? = some (384 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_2 Internal.SnakyRows011I.named_envelope_604_17 (384 : ℤ) Internal.SnakyRows011I.named_envelope_604_17_last
def Internal.SnakyRows011I.named_envelope_604_36 : List Cell := ([(3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_36_chain : (named_envelope_604_36.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_36_head : (named_envelope_604_36.map Internal.SnakyRows011I.namedCellKey).head? = some (385 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_36_last : (named_envelope_604_36.map Internal.SnakyRows011I.namedCellKey).getLast? = some (392 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_37 : List Cell := ([(3, 9), (3, 10), (3, 11), (3, 12), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_37_chain : (named_envelope_604_37.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_37_head : (named_envelope_604_37.map Internal.SnakyRows011I.namedCellKey).head? = some (393 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_37_last : (named_envelope_604_37.map Internal.SnakyRows011I.namedCellKey).getLast? = some (511 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_35 : List Cell := Internal.SnakyRows011I.named_envelope_604_36 ++ Internal.SnakyRows011I.named_envelope_604_37
theorem Internal.SnakyRows011I.named_envelope_604_35_chain : (named_envelope_604_35.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_36 Internal.SnakyRows011I.named_envelope_604_37 (392 : ℤ) (393 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_36_chain Internal.SnakyRows011I.named_envelope_604_37_chain Internal.SnakyRows011I.named_envelope_604_36_last Internal.SnakyRows011I.named_envelope_604_37_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_35_head : (named_envelope_604_35.map Internal.SnakyRows011I.namedCellKey).head? = some (385 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_36 Internal.SnakyRows011I.named_envelope_604_37 (385 : ℤ) Internal.SnakyRows011I.named_envelope_604_36_head
theorem Internal.SnakyRows011I.named_envelope_604_35_last : (named_envelope_604_35.map Internal.SnakyRows011I.namedCellKey).getLast? = some (511 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_36 Internal.SnakyRows011I.named_envelope_604_37 (511 : ℤ) Internal.SnakyRows011I.named_envelope_604_37_last
def Internal.SnakyRows011I.named_envelope_604_39 : List Cell := ([(4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_39_chain : (named_envelope_604_39.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_39_head : (named_envelope_604_39.map Internal.SnakyRows011I.namedCellKey).head? = some (512 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_39_last : (named_envelope_604_39.map Internal.SnakyRows011I.namedCellKey).getLast? = some (520 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_40 : List Cell := ([(4, 9), (4, 10), (4, 11), (4, 12), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_40_chain : (named_envelope_604_40.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_40_head : (named_envelope_604_40.map Internal.SnakyRows011I.namedCellKey).head? = some (521 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_40_last : (named_envelope_604_40.map Internal.SnakyRows011I.namedCellKey).getLast? = some (640 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_38 : List Cell := Internal.SnakyRows011I.named_envelope_604_39 ++ Internal.SnakyRows011I.named_envelope_604_40
theorem Internal.SnakyRows011I.named_envelope_604_38_chain : (named_envelope_604_38.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_39 Internal.SnakyRows011I.named_envelope_604_40 (520 : ℤ) (521 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_39_chain Internal.SnakyRows011I.named_envelope_604_40_chain Internal.SnakyRows011I.named_envelope_604_39_last Internal.SnakyRows011I.named_envelope_604_40_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_38_head : (named_envelope_604_38.map Internal.SnakyRows011I.namedCellKey).head? = some (512 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_39 Internal.SnakyRows011I.named_envelope_604_40 (512 : ℤ) Internal.SnakyRows011I.named_envelope_604_39_head
theorem Internal.SnakyRows011I.named_envelope_604_38_last : (named_envelope_604_38.map Internal.SnakyRows011I.namedCellKey).getLast? = some (640 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_39 Internal.SnakyRows011I.named_envelope_604_40 (640 : ℤ) Internal.SnakyRows011I.named_envelope_604_40_last
def Internal.SnakyRows011I.named_envelope_604_34 : List Cell := Internal.SnakyRows011I.named_envelope_604_35 ++ Internal.SnakyRows011I.named_envelope_604_38
theorem Internal.SnakyRows011I.named_envelope_604_34_chain : (named_envelope_604_34.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_35 Internal.SnakyRows011I.named_envelope_604_38 (511 : ℤ) (512 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_35_chain Internal.SnakyRows011I.named_envelope_604_38_chain Internal.SnakyRows011I.named_envelope_604_35_last Internal.SnakyRows011I.named_envelope_604_38_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_34_head : (named_envelope_604_34.map Internal.SnakyRows011I.namedCellKey).head? = some (385 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_35 Internal.SnakyRows011I.named_envelope_604_38 (385 : ℤ) Internal.SnakyRows011I.named_envelope_604_35_head
theorem Internal.SnakyRows011I.named_envelope_604_34_last : (named_envelope_604_34.map Internal.SnakyRows011I.namedCellKey).getLast? = some (640 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_35 Internal.SnakyRows011I.named_envelope_604_38 (640 : ℤ) Internal.SnakyRows011I.named_envelope_604_38_last
def Internal.SnakyRows011I.named_envelope_604_43 : List Cell := ([(5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_43_chain : (named_envelope_604_43.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_43_head : (named_envelope_604_43.map Internal.SnakyRows011I.namedCellKey).head? = some (641 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_43_last : (named_envelope_604_43.map Internal.SnakyRows011I.namedCellKey).getLast? = some (648 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_44 : List Cell := ([(5, 9), (5, 10), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_44_chain : (named_envelope_604_44.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_44_head : (named_envelope_604_44.map Internal.SnakyRows011I.namedCellKey).head? = some (649 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_44_last : (named_envelope_604_44.map Internal.SnakyRows011I.namedCellKey).getLast? = some (768 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_42 : List Cell := Internal.SnakyRows011I.named_envelope_604_43 ++ Internal.SnakyRows011I.named_envelope_604_44
theorem Internal.SnakyRows011I.named_envelope_604_42_chain : (named_envelope_604_42.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_43 Internal.SnakyRows011I.named_envelope_604_44 (648 : ℤ) (649 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_43_chain Internal.SnakyRows011I.named_envelope_604_44_chain Internal.SnakyRows011I.named_envelope_604_43_last Internal.SnakyRows011I.named_envelope_604_44_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_42_head : (named_envelope_604_42.map Internal.SnakyRows011I.namedCellKey).head? = some (641 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_43 Internal.SnakyRows011I.named_envelope_604_44 (641 : ℤ) Internal.SnakyRows011I.named_envelope_604_43_head
theorem Internal.SnakyRows011I.named_envelope_604_42_last : (named_envelope_604_42.map Internal.SnakyRows011I.namedCellKey).getLast? = some (768 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_43 Internal.SnakyRows011I.named_envelope_604_44 (768 : ℤ) Internal.SnakyRows011I.named_envelope_604_44_last
def Internal.SnakyRows011I.named_envelope_604_46 : List Cell := ([(6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_46_chain : (named_envelope_604_46.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_46_head : (named_envelope_604_46.map Internal.SnakyRows011I.namedCellKey).head? = some (769 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_46_last : (named_envelope_604_46.map Internal.SnakyRows011I.namedCellKey).getLast? = some (777 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_47 : List Cell := ([(6, 10), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_47_chain : (named_envelope_604_47.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_47_head : (named_envelope_604_47.map Internal.SnakyRows011I.namedCellKey).head? = some (778 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_47_last : (named_envelope_604_47.map Internal.SnakyRows011I.namedCellKey).getLast? = some (897 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_45 : List Cell := Internal.SnakyRows011I.named_envelope_604_46 ++ Internal.SnakyRows011I.named_envelope_604_47
theorem Internal.SnakyRows011I.named_envelope_604_45_chain : (named_envelope_604_45.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_46 Internal.SnakyRows011I.named_envelope_604_47 (777 : ℤ) (778 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_46_chain Internal.SnakyRows011I.named_envelope_604_47_chain Internal.SnakyRows011I.named_envelope_604_46_last Internal.SnakyRows011I.named_envelope_604_47_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_45_head : (named_envelope_604_45.map Internal.SnakyRows011I.namedCellKey).head? = some (769 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_46 Internal.SnakyRows011I.named_envelope_604_47 (769 : ℤ) Internal.SnakyRows011I.named_envelope_604_46_head
theorem Internal.SnakyRows011I.named_envelope_604_45_last : (named_envelope_604_45.map Internal.SnakyRows011I.namedCellKey).getLast? = some (897 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_46 Internal.SnakyRows011I.named_envelope_604_47 (897 : ℤ) Internal.SnakyRows011I.named_envelope_604_47_last
def Internal.SnakyRows011I.named_envelope_604_41 : List Cell := Internal.SnakyRows011I.named_envelope_604_42 ++ Internal.SnakyRows011I.named_envelope_604_45
theorem Internal.SnakyRows011I.named_envelope_604_41_chain : (named_envelope_604_41.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_42 Internal.SnakyRows011I.named_envelope_604_45 (768 : ℤ) (769 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_42_chain Internal.SnakyRows011I.named_envelope_604_45_chain Internal.SnakyRows011I.named_envelope_604_42_last Internal.SnakyRows011I.named_envelope_604_45_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_41_head : (named_envelope_604_41.map Internal.SnakyRows011I.namedCellKey).head? = some (641 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_42 Internal.SnakyRows011I.named_envelope_604_45 (641 : ℤ) Internal.SnakyRows011I.named_envelope_604_42_head
theorem Internal.SnakyRows011I.named_envelope_604_41_last : (named_envelope_604_41.map Internal.SnakyRows011I.namedCellKey).getLast? = some (897 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_42 Internal.SnakyRows011I.named_envelope_604_45 (897 : ℤ) Internal.SnakyRows011I.named_envelope_604_45_last
def Internal.SnakyRows011I.named_envelope_604_33 : List Cell := Internal.SnakyRows011I.named_envelope_604_34 ++ Internal.SnakyRows011I.named_envelope_604_41
theorem Internal.SnakyRows011I.named_envelope_604_33_chain : (named_envelope_604_33.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_34 Internal.SnakyRows011I.named_envelope_604_41 (640 : ℤ) (641 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_34_chain Internal.SnakyRows011I.named_envelope_604_41_chain Internal.SnakyRows011I.named_envelope_604_34_last Internal.SnakyRows011I.named_envelope_604_41_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_33_head : (named_envelope_604_33.map Internal.SnakyRows011I.namedCellKey).head? = some (385 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_34 Internal.SnakyRows011I.named_envelope_604_41 (385 : ℤ) Internal.SnakyRows011I.named_envelope_604_34_head
theorem Internal.SnakyRows011I.named_envelope_604_33_last : (named_envelope_604_33.map Internal.SnakyRows011I.namedCellKey).getLast? = some (897 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_34 Internal.SnakyRows011I.named_envelope_604_41 (897 : ℤ) Internal.SnakyRows011I.named_envelope_604_41_last
def Internal.SnakyRows011I.named_envelope_604_51 : List Cell := ([(7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_51_chain : (named_envelope_604_51.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_51_head : (named_envelope_604_51.map Internal.SnakyRows011I.namedCellKey).head? = some (898 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_51_last : (named_envelope_604_51.map Internal.SnakyRows011I.namedCellKey).getLast? = some (905 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_52 : List Cell := ([(7, 10), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_52_chain : (named_envelope_604_52.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_52_head : (named_envelope_604_52.map Internal.SnakyRows011I.namedCellKey).head? = some (906 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_52_last : (named_envelope_604_52.map Internal.SnakyRows011I.namedCellKey).getLast? = some (1026 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_50 : List Cell := Internal.SnakyRows011I.named_envelope_604_51 ++ Internal.SnakyRows011I.named_envelope_604_52
theorem Internal.SnakyRows011I.named_envelope_604_50_chain : (named_envelope_604_50.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_51 Internal.SnakyRows011I.named_envelope_604_52 (905 : ℤ) (906 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_51_chain Internal.SnakyRows011I.named_envelope_604_52_chain Internal.SnakyRows011I.named_envelope_604_51_last Internal.SnakyRows011I.named_envelope_604_52_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_50_head : (named_envelope_604_50.map Internal.SnakyRows011I.namedCellKey).head? = some (898 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_51 Internal.SnakyRows011I.named_envelope_604_52 (898 : ℤ) Internal.SnakyRows011I.named_envelope_604_51_head
theorem Internal.SnakyRows011I.named_envelope_604_50_last : (named_envelope_604_50.map Internal.SnakyRows011I.namedCellKey).getLast? = some (1026 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_51 Internal.SnakyRows011I.named_envelope_604_52 (1026 : ℤ) Internal.SnakyRows011I.named_envelope_604_52_last
def Internal.SnakyRows011I.named_envelope_604_54 : List Cell := ([(8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, -6), (9, -5), (9, -4)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_54_chain : (named_envelope_604_54.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_54_head : (named_envelope_604_54.map Internal.SnakyRows011I.namedCellKey).head? = some (1027 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_54_last : (named_envelope_604_54.map Internal.SnakyRows011I.namedCellKey).getLast? = some (1148 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_55 : List Cell := ([(9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_55_chain : (named_envelope_604_55.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_55_head : (named_envelope_604_55.map Internal.SnakyRows011I.namedCellKey).head? = some (1149 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_55_last : (named_envelope_604_55.map Internal.SnakyRows011I.namedCellKey).getLast? = some (1157 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_53 : List Cell := Internal.SnakyRows011I.named_envelope_604_54 ++ Internal.SnakyRows011I.named_envelope_604_55
theorem Internal.SnakyRows011I.named_envelope_604_53_chain : (named_envelope_604_53.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_54 Internal.SnakyRows011I.named_envelope_604_55 (1148 : ℤ) (1149 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_54_chain Internal.SnakyRows011I.named_envelope_604_55_chain Internal.SnakyRows011I.named_envelope_604_54_last Internal.SnakyRows011I.named_envelope_604_55_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_53_head : (named_envelope_604_53.map Internal.SnakyRows011I.namedCellKey).head? = some (1027 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_54 Internal.SnakyRows011I.named_envelope_604_55 (1027 : ℤ) Internal.SnakyRows011I.named_envelope_604_54_head
theorem Internal.SnakyRows011I.named_envelope_604_53_last : (named_envelope_604_53.map Internal.SnakyRows011I.namedCellKey).getLast? = some (1157 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_54 Internal.SnakyRows011I.named_envelope_604_55 (1157 : ℤ) Internal.SnakyRows011I.named_envelope_604_55_last
def Internal.SnakyRows011I.named_envelope_604_49 : List Cell := Internal.SnakyRows011I.named_envelope_604_50 ++ Internal.SnakyRows011I.named_envelope_604_53
theorem Internal.SnakyRows011I.named_envelope_604_49_chain : (named_envelope_604_49.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_50 Internal.SnakyRows011I.named_envelope_604_53 (1026 : ℤ) (1027 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_50_chain Internal.SnakyRows011I.named_envelope_604_53_chain Internal.SnakyRows011I.named_envelope_604_50_last Internal.SnakyRows011I.named_envelope_604_53_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_49_head : (named_envelope_604_49.map Internal.SnakyRows011I.namedCellKey).head? = some (898 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_50 Internal.SnakyRows011I.named_envelope_604_53 (898 : ℤ) Internal.SnakyRows011I.named_envelope_604_50_head
theorem Internal.SnakyRows011I.named_envelope_604_49_last : (named_envelope_604_49.map Internal.SnakyRows011I.namedCellKey).getLast? = some (1157 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_50 Internal.SnakyRows011I.named_envelope_604_53 (1157 : ℤ) Internal.SnakyRows011I.named_envelope_604_53_last
def Internal.SnakyRows011I.named_envelope_604_58 : List Cell := ([(9, 6), (9, 7), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_58_chain : (named_envelope_604_58.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_58_head : (named_envelope_604_58.map Internal.SnakyRows011I.namedCellKey).head? = some (1158 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_58_last : (named_envelope_604_58.map Internal.SnakyRows011I.namedCellKey).getLast? = some (1282 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_59 : List Cell := ([(10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (11, -4), (11, -3), (11, -2), (11, -1)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_59_chain : (named_envelope_604_59.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_59_head : (named_envelope_604_59.map Internal.SnakyRows011I.namedCellKey).head? = some (1283 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_59_last : (named_envelope_604_59.map Internal.SnakyRows011I.namedCellKey).getLast? = some (1407 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_57 : List Cell := Internal.SnakyRows011I.named_envelope_604_58 ++ Internal.SnakyRows011I.named_envelope_604_59
theorem Internal.SnakyRows011I.named_envelope_604_57_chain : (named_envelope_604_57.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_58 Internal.SnakyRows011I.named_envelope_604_59 (1282 : ℤ) (1283 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_58_chain Internal.SnakyRows011I.named_envelope_604_59_chain Internal.SnakyRows011I.named_envelope_604_58_last Internal.SnakyRows011I.named_envelope_604_59_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_57_head : (named_envelope_604_57.map Internal.SnakyRows011I.namedCellKey).head? = some (1158 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_58 Internal.SnakyRows011I.named_envelope_604_59 (1158 : ℤ) Internal.SnakyRows011I.named_envelope_604_58_head
theorem Internal.SnakyRows011I.named_envelope_604_57_last : (named_envelope_604_57.map Internal.SnakyRows011I.namedCellKey).getLast? = some (1407 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_58 Internal.SnakyRows011I.named_envelope_604_59 (1407 : ℤ) Internal.SnakyRows011I.named_envelope_604_59_last
def Internal.SnakyRows011I.named_envelope_604_61 : List Cell := ([(11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (12, -4), (12, -2), (12, -1), (12, 0)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_61_chain : (named_envelope_604_61.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_61_head : (named_envelope_604_61.map Internal.SnakyRows011I.namedCellKey).head? = some (1408 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_61_last : (named_envelope_604_61.map Internal.SnakyRows011I.namedCellKey).getLast? = some (1536 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_62 : List Cell := ([(12, 1), (12, 2), (12, 3), (12, 4), (13, -2), (13, -1), (13, 0), (14, -2), (14, 0)] : List Cell)
theorem Internal.SnakyRows011I.named_envelope_604_62_chain : (named_envelope_604_62.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_62_head : (named_envelope_604_62.map Internal.SnakyRows011I.namedCellKey).head? = some (1537 : ℤ) := by decide
theorem Internal.SnakyRows011I.named_envelope_604_62_last : (named_envelope_604_62.map Internal.SnakyRows011I.namedCellKey).getLast? = some (1792 : ℤ) := by decide
def Internal.SnakyRows011I.named_envelope_604_60 : List Cell := Internal.SnakyRows011I.named_envelope_604_61 ++ Internal.SnakyRows011I.named_envelope_604_62
theorem Internal.SnakyRows011I.named_envelope_604_60_chain : (named_envelope_604_60.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_61 Internal.SnakyRows011I.named_envelope_604_62 (1536 : ℤ) (1537 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_61_chain Internal.SnakyRows011I.named_envelope_604_62_chain Internal.SnakyRows011I.named_envelope_604_61_last Internal.SnakyRows011I.named_envelope_604_62_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_60_head : (named_envelope_604_60.map Internal.SnakyRows011I.namedCellKey).head? = some (1408 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_61 Internal.SnakyRows011I.named_envelope_604_62 (1408 : ℤ) Internal.SnakyRows011I.named_envelope_604_61_head
theorem Internal.SnakyRows011I.named_envelope_604_60_last : (named_envelope_604_60.map Internal.SnakyRows011I.namedCellKey).getLast? = some (1792 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_61 Internal.SnakyRows011I.named_envelope_604_62 (1792 : ℤ) Internal.SnakyRows011I.named_envelope_604_62_last
def Internal.SnakyRows011I.named_envelope_604_56 : List Cell := Internal.SnakyRows011I.named_envelope_604_57 ++ Internal.SnakyRows011I.named_envelope_604_60
theorem Internal.SnakyRows011I.named_envelope_604_56_chain : (named_envelope_604_56.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_57 Internal.SnakyRows011I.named_envelope_604_60 (1407 : ℤ) (1408 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_57_chain Internal.SnakyRows011I.named_envelope_604_60_chain Internal.SnakyRows011I.named_envelope_604_57_last Internal.SnakyRows011I.named_envelope_604_60_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_56_head : (named_envelope_604_56.map Internal.SnakyRows011I.namedCellKey).head? = some (1158 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_57 Internal.SnakyRows011I.named_envelope_604_60 (1158 : ℤ) Internal.SnakyRows011I.named_envelope_604_57_head
theorem Internal.SnakyRows011I.named_envelope_604_56_last : (named_envelope_604_56.map Internal.SnakyRows011I.namedCellKey).getLast? = some (1792 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_57 Internal.SnakyRows011I.named_envelope_604_60 (1792 : ℤ) Internal.SnakyRows011I.named_envelope_604_60_last
def Internal.SnakyRows011I.named_envelope_604_48 : List Cell := Internal.SnakyRows011I.named_envelope_604_49 ++ Internal.SnakyRows011I.named_envelope_604_56
theorem Internal.SnakyRows011I.named_envelope_604_48_chain : (named_envelope_604_48.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_49 Internal.SnakyRows011I.named_envelope_604_56 (1157 : ℤ) (1158 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_49_chain Internal.SnakyRows011I.named_envelope_604_56_chain Internal.SnakyRows011I.named_envelope_604_49_last Internal.SnakyRows011I.named_envelope_604_56_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_48_head : (named_envelope_604_48.map Internal.SnakyRows011I.namedCellKey).head? = some (898 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_49 Internal.SnakyRows011I.named_envelope_604_56 (898 : ℤ) Internal.SnakyRows011I.named_envelope_604_49_head
theorem Internal.SnakyRows011I.named_envelope_604_48_last : (named_envelope_604_48.map Internal.SnakyRows011I.namedCellKey).getLast? = some (1792 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_49 Internal.SnakyRows011I.named_envelope_604_56 (1792 : ℤ) Internal.SnakyRows011I.named_envelope_604_56_last
def Internal.SnakyRows011I.named_envelope_604_32 : List Cell := Internal.SnakyRows011I.named_envelope_604_33 ++ Internal.SnakyRows011I.named_envelope_604_48
theorem Internal.SnakyRows011I.named_envelope_604_32_chain : (named_envelope_604_32.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_33 Internal.SnakyRows011I.named_envelope_604_48 (897 : ℤ) (898 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_33_chain Internal.SnakyRows011I.named_envelope_604_48_chain Internal.SnakyRows011I.named_envelope_604_33_last Internal.SnakyRows011I.named_envelope_604_48_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_32_head : (named_envelope_604_32.map Internal.SnakyRows011I.namedCellKey).head? = some (385 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_33 Internal.SnakyRows011I.named_envelope_604_48 (385 : ℤ) Internal.SnakyRows011I.named_envelope_604_33_head
theorem Internal.SnakyRows011I.named_envelope_604_32_last : (named_envelope_604_32.map Internal.SnakyRows011I.namedCellKey).getLast? = some (1792 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_33 Internal.SnakyRows011I.named_envelope_604_48 (1792 : ℤ) Internal.SnakyRows011I.named_envelope_604_48_last
def Internal.SnakyRows011I.named_envelope_604_0 : List Cell := Internal.SnakyRows011I.named_envelope_604_1 ++ Internal.SnakyRows011I.named_envelope_604_32
theorem Internal.SnakyRows011I.named_envelope_604_0_chain : (named_envelope_604_0.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011I.named_chain_append Internal.SnakyRows011I.named_envelope_604_1 Internal.SnakyRows011I.named_envelope_604_32 (384 : ℤ) (385 : ℤ)
    Internal.SnakyRows011I.named_envelope_604_1_chain Internal.SnakyRows011I.named_envelope_604_32_chain Internal.SnakyRows011I.named_envelope_604_1_last Internal.SnakyRows011I.named_envelope_604_32_head (by decide)
theorem Internal.SnakyRows011I.named_envelope_604_0_head : (named_envelope_604_0.map Internal.SnakyRows011I.namedCellKey).head? = some (-897 : ℤ) :=
  Internal.SnakyRows011I.named_head_append Internal.SnakyRows011I.named_envelope_604_1 Internal.SnakyRows011I.named_envelope_604_32 (-897 : ℤ) Internal.SnakyRows011I.named_envelope_604_1_head
theorem Internal.SnakyRows011I.named_envelope_604_0_last : (named_envelope_604_0.map Internal.SnakyRows011I.namedCellKey).getLast? = some (1792 : ℤ) :=
  Internal.SnakyRows011I.named_last_append Internal.SnakyRows011I.named_envelope_604_1 Internal.SnakyRows011I.named_envelope_604_32 (1792 : ℤ) Internal.SnakyRows011I.named_envelope_604_32_last
theorem Internal.SnakyRows011I.named_envelope_604_nodup : (Internal.SnakyRows011I.named_envelope_604_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows011I.named_nodup_of_chain Internal.SnakyRows011I.named_envelope_604_0 Internal.SnakyRows011I.named_envelope_604_0_chain
def envelope_604 : Finset Cell := ⟨(Internal.SnakyRows011I.named_envelope_604_0 : Multiset Cell), Internal.SnakyRows011I.named_envelope_604_nodup⟩
def childrenC_604 : Fin 6 → Finset Cell := ![(placedSet 0 (-1, 0) required_597), (placedSet 2 (0, -1) required_375), (placedSet 1 (0, -1) required_597), (placedSet 3 (-1, 0) required_375), (placedSet 3 (0, -1) required_350), (placedSet 2 (-1, 0) required_350)]
def childrenD_604 : Fin 6 → Finset Cell := ![(placedSet 0 (-1, 0) envelope_597), (placedSet 2 (0, -1) envelope_375), (placedSet 1 (0, -1) envelope_597), (placedSet 3 (-1, 0) envelope_375), (placedSet 3 (0, -1) envelope_350), (placedSet 2 (-1, 0) envelope_350)]
theorem common_sub_604 : commonEnvelope childrenD_604 ⊆ insert (0, 0) required_604 := by decide
theorem child_required_sub_604 : ∀ j, childrenC_604 j ⊆ insert (0, 0) required_604 := by decide
theorem Internal.SnakyRows011I.containment_604_0 :
    placedSet 0 (-1, 0) envelope_597 ⊆ envelope_604 := by decide +kernel
theorem Internal.SnakyRows011I.containment_604_1 :
    placedSet 2 (0, -1) envelope_375 ⊆ envelope_604 := by decide
theorem Internal.SnakyRows011I.containment_604_2 :
    placedSet 1 (0, -1) envelope_597 ⊆ envelope_604 := by decide +kernel
theorem Internal.SnakyRows011I.containment_604_3 :
    placedSet 3 (-1, 0) envelope_375 ⊆ envelope_604 := by decide
theorem Internal.SnakyRows011I.containment_604_4 :
    placedSet 3 (0, -1) envelope_350 ⊆ envelope_604 := by decide
theorem Internal.SnakyRows011I.containment_604_5 :
    placedSet 2 (-1, 0) envelope_350 ⊆ envelope_604 := by decide
theorem child_envelope_sub_604 : ∀ j, childrenD_604 j ⊆ envelope_604 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows011I.containment_604_0
  · exact Internal.SnakyRows011I.containment_604_1
  · exact Internal.SnakyRows011I.containment_604_2
  · exact Internal.SnakyRows011I.containment_604_3
  · exact Internal.SnakyRows011I.containment_604_4
  · exact Internal.SnakyRows011I.containment_604_5
theorem pivot_mem_604 : (0, 0) ∈ envelope_604 := by decide
theorem children_work_604 : ∀ j, Template HasSnaky 29 (childrenC_604 j) (childrenD_604 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_597 0 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_375 2 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_597 1 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_375 3 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_350 3 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_350 2 (-1, 0)).mono (by decide)
theorem row_works_604 : Template HasSnaky 30 required_604 envelope_604 := by
  refine compose HasSnaky 29 childrenC_604 childrenD_604 children_work_604 (0, 0)
    required_604 envelope_604 pivot_mem_604 child_required_sub_604 child_envelope_sub_604 ?_
  intro b hb; exact common_sub_604 (mem_commonEnvelope childrenD_604 b hb)
end SnakyConditional

end OAI
