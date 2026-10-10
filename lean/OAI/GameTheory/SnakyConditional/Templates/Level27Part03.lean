import OAI.GameTheory.SnakyConditional.Templates.Level26Part04

namespace OAI

namespace SnakyConditional
def required_578 : Finset Cell := ⟨(([(0, -3), (0, -2), (1, 0), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows009.named_envelope_578_4 : List Cell := ([(-8, -1), (-8, 1), (-8, 3), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-6, -1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_578_4_chain : (named_envelope_578_4.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_578_4_head : (named_envelope_578_4.map Internal.SnakyRows009.namedCellKey).head? = some (-1025 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_578_4_last : (named_envelope_578_4.map Internal.SnakyRows009.namedCellKey).getLast? = some (-769 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_578_5 : List Cell := ([(-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-5, -3), (-5, -2), (-5, -1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_578_5_chain : (named_envelope_578_5.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_578_5_head : (named_envelope_578_5.map Internal.SnakyRows009.namedCellKey).head? = some (-768 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_578_5_last : (named_envelope_578_5.map Internal.SnakyRows009.namedCellKey).getLast? = some (-641 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_578_3 : List Cell := Internal.SnakyRows009.named_envelope_578_4 ++ Internal.SnakyRows009.named_envelope_578_5
theorem Internal.SnakyRows009.named_envelope_578_3_chain : (named_envelope_578_3.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_578_4 Internal.SnakyRows009.named_envelope_578_5 (-769 : ℤ) (-768 : ℤ)
    Internal.SnakyRows009.named_envelope_578_4_chain Internal.SnakyRows009.named_envelope_578_5_chain Internal.SnakyRows009.named_envelope_578_4_last Internal.SnakyRows009.named_envelope_578_5_head (by decide)
theorem Internal.SnakyRows009.named_envelope_578_3_head : (named_envelope_578_3.map Internal.SnakyRows009.namedCellKey).head? = some (-1025 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_578_4 Internal.SnakyRows009.named_envelope_578_5 (-1025 : ℤ) Internal.SnakyRows009.named_envelope_578_4_head
theorem Internal.SnakyRows009.named_envelope_578_3_last : (named_envelope_578_3.map Internal.SnakyRows009.namedCellKey).getLast? = some (-641 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_578_4 Internal.SnakyRows009.named_envelope_578_5 (-641 : ℤ) Internal.SnakyRows009.named_envelope_578_5_last
def Internal.SnakyRows009.named_envelope_578_7 : List Cell := ([(-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-4, -2), (-4, -1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_578_7_chain : (named_envelope_578_7.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_578_7_head : (named_envelope_578_7.map Internal.SnakyRows009.namedCellKey).head? = some (-640 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_578_7_last : (named_envelope_578_7.map Internal.SnakyRows009.namedCellKey).getLast? = some (-513 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_578_8 : List Cell := ([(-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_578_8_chain : (named_envelope_578_8.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_578_8_head : (named_envelope_578_8.map Internal.SnakyRows009.namedCellKey).head? = some (-512 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_578_8_last : (named_envelope_578_8.map Internal.SnakyRows009.namedCellKey).getLast? = some (-504 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_578_6 : List Cell := Internal.SnakyRows009.named_envelope_578_7 ++ Internal.SnakyRows009.named_envelope_578_8
theorem Internal.SnakyRows009.named_envelope_578_6_chain : (named_envelope_578_6.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_578_7 Internal.SnakyRows009.named_envelope_578_8 (-513 : ℤ) (-512 : ℤ)
    Internal.SnakyRows009.named_envelope_578_7_chain Internal.SnakyRows009.named_envelope_578_8_chain Internal.SnakyRows009.named_envelope_578_7_last Internal.SnakyRows009.named_envelope_578_8_head (by decide)
theorem Internal.SnakyRows009.named_envelope_578_6_head : (named_envelope_578_6.map Internal.SnakyRows009.namedCellKey).head? = some (-640 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_578_7 Internal.SnakyRows009.named_envelope_578_8 (-640 : ℤ) Internal.SnakyRows009.named_envelope_578_7_head
theorem Internal.SnakyRows009.named_envelope_578_6_last : (named_envelope_578_6.map Internal.SnakyRows009.namedCellKey).getLast? = some (-504 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_578_7 Internal.SnakyRows009.named_envelope_578_8 (-504 : ℤ) Internal.SnakyRows009.named_envelope_578_8_last
def Internal.SnakyRows009.named_envelope_578_2 : List Cell := Internal.SnakyRows009.named_envelope_578_3 ++ Internal.SnakyRows009.named_envelope_578_6
theorem Internal.SnakyRows009.named_envelope_578_2_chain : (named_envelope_578_2.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_578_3 Internal.SnakyRows009.named_envelope_578_6 (-641 : ℤ) (-640 : ℤ)
    Internal.SnakyRows009.named_envelope_578_3_chain Internal.SnakyRows009.named_envelope_578_6_chain Internal.SnakyRows009.named_envelope_578_3_last Internal.SnakyRows009.named_envelope_578_6_head (by decide)
theorem Internal.SnakyRows009.named_envelope_578_2_head : (named_envelope_578_2.map Internal.SnakyRows009.namedCellKey).head? = some (-1025 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_578_3 Internal.SnakyRows009.named_envelope_578_6 (-1025 : ℤ) Internal.SnakyRows009.named_envelope_578_3_head
theorem Internal.SnakyRows009.named_envelope_578_2_last : (named_envelope_578_2.map Internal.SnakyRows009.namedCellKey).getLast? = some (-504 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_578_3 Internal.SnakyRows009.named_envelope_578_6 (-504 : ℤ) Internal.SnakyRows009.named_envelope_578_6_last
def Internal.SnakyRows009.named_envelope_578_11 : List Cell := ([(-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_578_11_chain : (named_envelope_578_11.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_578_11_head : (named_envelope_578_11.map Internal.SnakyRows009.namedCellKey).head? = some (-387 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_578_11_last : (named_envelope_578_11.map Internal.SnakyRows009.namedCellKey).getLast? = some (-379 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_578_12 : List Cell := ([(-3, 6), (-3, 7), (-3, 8), (-3, 9), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_578_12_chain : (named_envelope_578_12.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_578_12_head : (named_envelope_578_12.map Internal.SnakyRows009.namedCellKey).head? = some (-378 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_578_12_last : (named_envelope_578_12.map Internal.SnakyRows009.namedCellKey).getLast? = some (-254 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_578_10 : List Cell := Internal.SnakyRows009.named_envelope_578_11 ++ Internal.SnakyRows009.named_envelope_578_12
theorem Internal.SnakyRows009.named_envelope_578_10_chain : (named_envelope_578_10.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_578_11 Internal.SnakyRows009.named_envelope_578_12 (-379 : ℤ) (-378 : ℤ)
    Internal.SnakyRows009.named_envelope_578_11_chain Internal.SnakyRows009.named_envelope_578_12_chain Internal.SnakyRows009.named_envelope_578_11_last Internal.SnakyRows009.named_envelope_578_12_head (by decide)
theorem Internal.SnakyRows009.named_envelope_578_10_head : (named_envelope_578_10.map Internal.SnakyRows009.namedCellKey).head? = some (-387 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_578_11 Internal.SnakyRows009.named_envelope_578_12 (-387 : ℤ) Internal.SnakyRows009.named_envelope_578_11_head
theorem Internal.SnakyRows009.named_envelope_578_10_last : (named_envelope_578_10.map Internal.SnakyRows009.namedCellKey).getLast? = some (-254 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_578_11 Internal.SnakyRows009.named_envelope_578_12 (-254 : ℤ) Internal.SnakyRows009.named_envelope_578_12_last
def Internal.SnakyRows009.named_envelope_578_14 : List Cell := ([(-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, -1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_578_14_chain : (named_envelope_578_14.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_578_14_head : (named_envelope_578_14.map Internal.SnakyRows009.namedCellKey).head? = some (-253 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_578_14_last : (named_envelope_578_14.map Internal.SnakyRows009.namedCellKey).getLast? = some (-129 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_578_15 : List Cell := ([(-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_578_15_chain : (named_envelope_578_15.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_578_15_head : (named_envelope_578_15.map Internal.SnakyRows009.namedCellKey).head? = some (-128 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_578_15_last : (named_envelope_578_15.map Internal.SnakyRows009.namedCellKey).getLast? = some (-119 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_578_13 : List Cell := Internal.SnakyRows009.named_envelope_578_14 ++ Internal.SnakyRows009.named_envelope_578_15
theorem Internal.SnakyRows009.named_envelope_578_13_chain : (named_envelope_578_13.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_578_14 Internal.SnakyRows009.named_envelope_578_15 (-129 : ℤ) (-128 : ℤ)
    Internal.SnakyRows009.named_envelope_578_14_chain Internal.SnakyRows009.named_envelope_578_15_chain Internal.SnakyRows009.named_envelope_578_14_last Internal.SnakyRows009.named_envelope_578_15_head (by decide)
theorem Internal.SnakyRows009.named_envelope_578_13_head : (named_envelope_578_13.map Internal.SnakyRows009.namedCellKey).head? = some (-253 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_578_14 Internal.SnakyRows009.named_envelope_578_15 (-253 : ℤ) Internal.SnakyRows009.named_envelope_578_14_head
theorem Internal.SnakyRows009.named_envelope_578_13_last : (named_envelope_578_13.map Internal.SnakyRows009.namedCellKey).getLast? = some (-119 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_578_14 Internal.SnakyRows009.named_envelope_578_15 (-119 : ℤ) Internal.SnakyRows009.named_envelope_578_15_last
def Internal.SnakyRows009.named_envelope_578_9 : List Cell := Internal.SnakyRows009.named_envelope_578_10 ++ Internal.SnakyRows009.named_envelope_578_13
theorem Internal.SnakyRows009.named_envelope_578_9_chain : (named_envelope_578_9.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_578_10 Internal.SnakyRows009.named_envelope_578_13 (-254 : ℤ) (-253 : ℤ)
    Internal.SnakyRows009.named_envelope_578_10_chain Internal.SnakyRows009.named_envelope_578_13_chain Internal.SnakyRows009.named_envelope_578_10_last Internal.SnakyRows009.named_envelope_578_13_head (by decide)
theorem Internal.SnakyRows009.named_envelope_578_9_head : (named_envelope_578_9.map Internal.SnakyRows009.namedCellKey).head? = some (-387 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_578_10 Internal.SnakyRows009.named_envelope_578_13 (-387 : ℤ) Internal.SnakyRows009.named_envelope_578_10_head
theorem Internal.SnakyRows009.named_envelope_578_9_last : (named_envelope_578_9.map Internal.SnakyRows009.namedCellKey).getLast? = some (-119 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_578_10 Internal.SnakyRows009.named_envelope_578_13 (-119 : ℤ) Internal.SnakyRows009.named_envelope_578_13_last
def Internal.SnakyRows009.named_envelope_578_1 : List Cell := Internal.SnakyRows009.named_envelope_578_2 ++ Internal.SnakyRows009.named_envelope_578_9
theorem Internal.SnakyRows009.named_envelope_578_1_chain : (named_envelope_578_1.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_578_2 Internal.SnakyRows009.named_envelope_578_9 (-504 : ℤ) (-387 : ℤ)
    Internal.SnakyRows009.named_envelope_578_2_chain Internal.SnakyRows009.named_envelope_578_9_chain Internal.SnakyRows009.named_envelope_578_2_last Internal.SnakyRows009.named_envelope_578_9_head (by decide)
theorem Internal.SnakyRows009.named_envelope_578_1_head : (named_envelope_578_1.map Internal.SnakyRows009.namedCellKey).head? = some (-1025 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_578_2 Internal.SnakyRows009.named_envelope_578_9 (-1025 : ℤ) Internal.SnakyRows009.named_envelope_578_2_head
theorem Internal.SnakyRows009.named_envelope_578_1_last : (named_envelope_578_1.map Internal.SnakyRows009.namedCellKey).getLast? = some (-119 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_578_2 Internal.SnakyRows009.named_envelope_578_9 (-119 : ℤ) Internal.SnakyRows009.named_envelope_578_9_last
def Internal.SnakyRows009.named_envelope_578_19 : List Cell := ([(-1, 10), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_578_19_chain : (named_envelope_578_19.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_578_19_head : (named_envelope_578_19.map Internal.SnakyRows009.namedCellKey).head? = some (-118 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_578_19_last : (named_envelope_578_19.map Internal.SnakyRows009.namedCellKey).getLast? = some (4 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_578_20 : List Cell := ([(0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, 0), (1, 1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_578_20_chain : (named_envelope_578_20.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_578_20_head : (named_envelope_578_20.map Internal.SnakyRows009.namedCellKey).head? = some (5 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_578_20_last : (named_envelope_578_20.map Internal.SnakyRows009.namedCellKey).getLast? = some (129 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_578_18 : List Cell := Internal.SnakyRows009.named_envelope_578_19 ++ Internal.SnakyRows009.named_envelope_578_20
theorem Internal.SnakyRows009.named_envelope_578_18_chain : (named_envelope_578_18.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_578_19 Internal.SnakyRows009.named_envelope_578_20 (4 : ℤ) (5 : ℤ)
    Internal.SnakyRows009.named_envelope_578_19_chain Internal.SnakyRows009.named_envelope_578_20_chain Internal.SnakyRows009.named_envelope_578_19_last Internal.SnakyRows009.named_envelope_578_20_head (by decide)
theorem Internal.SnakyRows009.named_envelope_578_18_head : (named_envelope_578_18.map Internal.SnakyRows009.namedCellKey).head? = some (-118 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_578_19 Internal.SnakyRows009.named_envelope_578_20 (-118 : ℤ) Internal.SnakyRows009.named_envelope_578_19_head
theorem Internal.SnakyRows009.named_envelope_578_18_last : (named_envelope_578_18.map Internal.SnakyRows009.namedCellKey).getLast? = some (129 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_578_19 Internal.SnakyRows009.named_envelope_578_20 (129 : ℤ) Internal.SnakyRows009.named_envelope_578_20_last
def Internal.SnakyRows009.named_envelope_578_22 : List Cell := ([(1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_578_22_chain : (named_envelope_578_22.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_578_22_head : (named_envelope_578_22.map Internal.SnakyRows009.namedCellKey).head? = some (130 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_578_22_last : (named_envelope_578_22.map Internal.SnakyRows009.namedCellKey).getLast? = some (138 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_578_23 : List Cell := ([(1, 11), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_578_23_chain : (named_envelope_578_23.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_578_23_head : (named_envelope_578_23.map Internal.SnakyRows009.namedCellKey).head? = some (139 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_578_23_last : (named_envelope_578_23.map Internal.SnakyRows009.namedCellKey).getLast? = some (265 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_578_21 : List Cell := Internal.SnakyRows009.named_envelope_578_22 ++ Internal.SnakyRows009.named_envelope_578_23
theorem Internal.SnakyRows009.named_envelope_578_21_chain : (named_envelope_578_21.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_578_22 Internal.SnakyRows009.named_envelope_578_23 (138 : ℤ) (139 : ℤ)
    Internal.SnakyRows009.named_envelope_578_22_chain Internal.SnakyRows009.named_envelope_578_23_chain Internal.SnakyRows009.named_envelope_578_22_last Internal.SnakyRows009.named_envelope_578_23_head (by decide)
theorem Internal.SnakyRows009.named_envelope_578_21_head : (named_envelope_578_21.map Internal.SnakyRows009.namedCellKey).head? = some (130 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_578_22 Internal.SnakyRows009.named_envelope_578_23 (130 : ℤ) Internal.SnakyRows009.named_envelope_578_22_head
theorem Internal.SnakyRows009.named_envelope_578_21_last : (named_envelope_578_21.map Internal.SnakyRows009.namedCellKey).getLast? = some (265 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_578_22 Internal.SnakyRows009.named_envelope_578_23 (265 : ℤ) Internal.SnakyRows009.named_envelope_578_23_last
def Internal.SnakyRows009.named_envelope_578_17 : List Cell := Internal.SnakyRows009.named_envelope_578_18 ++ Internal.SnakyRows009.named_envelope_578_21
theorem Internal.SnakyRows009.named_envelope_578_17_chain : (named_envelope_578_17.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_578_18 Internal.SnakyRows009.named_envelope_578_21 (129 : ℤ) (130 : ℤ)
    Internal.SnakyRows009.named_envelope_578_18_chain Internal.SnakyRows009.named_envelope_578_21_chain Internal.SnakyRows009.named_envelope_578_18_last Internal.SnakyRows009.named_envelope_578_21_head (by decide)
theorem Internal.SnakyRows009.named_envelope_578_17_head : (named_envelope_578_17.map Internal.SnakyRows009.namedCellKey).head? = some (-118 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_578_18 Internal.SnakyRows009.named_envelope_578_21 (-118 : ℤ) Internal.SnakyRows009.named_envelope_578_18_head
theorem Internal.SnakyRows009.named_envelope_578_17_last : (named_envelope_578_17.map Internal.SnakyRows009.namedCellKey).getLast? = some (265 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_578_18 Internal.SnakyRows009.named_envelope_578_21 (265 : ℤ) Internal.SnakyRows009.named_envelope_578_21_last
def Internal.SnakyRows009.named_envelope_578_26 : List Cell := ([(2, 10), (2, 11), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_578_26_chain : (named_envelope_578_26.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_578_26_head : (named_envelope_578_26.map Internal.SnakyRows009.namedCellKey).head? = some (266 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_578_26_last : (named_envelope_578_26.map Internal.SnakyRows009.namedCellKey).getLast? = some (391 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_578_27 : List Cell := ([(3, 8), (3, 9), (3, 10), (3, 11), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_578_27_chain : (named_envelope_578_27.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_578_27_head : (named_envelope_578_27.map Internal.SnakyRows009.namedCellKey).head? = some (392 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_578_27_last : (named_envelope_578_27.map Internal.SnakyRows009.namedCellKey).getLast? = some (516 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_578_25 : List Cell := Internal.SnakyRows009.named_envelope_578_26 ++ Internal.SnakyRows009.named_envelope_578_27
theorem Internal.SnakyRows009.named_envelope_578_25_chain : (named_envelope_578_25.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_578_26 Internal.SnakyRows009.named_envelope_578_27 (391 : ℤ) (392 : ℤ)
    Internal.SnakyRows009.named_envelope_578_26_chain Internal.SnakyRows009.named_envelope_578_27_chain Internal.SnakyRows009.named_envelope_578_26_last Internal.SnakyRows009.named_envelope_578_27_head (by decide)
theorem Internal.SnakyRows009.named_envelope_578_25_head : (named_envelope_578_25.map Internal.SnakyRows009.namedCellKey).head? = some (266 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_578_26 Internal.SnakyRows009.named_envelope_578_27 (266 : ℤ) Internal.SnakyRows009.named_envelope_578_26_head
theorem Internal.SnakyRows009.named_envelope_578_25_last : (named_envelope_578_25.map Internal.SnakyRows009.namedCellKey).getLast? = some (516 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_578_26 Internal.SnakyRows009.named_envelope_578_27 (516 : ℤ) Internal.SnakyRows009.named_envelope_578_27_last
def Internal.SnakyRows009.named_envelope_578_29 : List Cell := ([(4, 5), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_578_29_chain : (named_envelope_578_29.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_578_29_head : (named_envelope_578_29.map Internal.SnakyRows009.namedCellKey).head? = some (517 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_578_29_last : (named_envelope_578_29.map Internal.SnakyRows009.namedCellKey).getLast? = some (646 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_578_30 : List Cell := ([(5, 7), (5, 8), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 3), (7, 4), (7, 5)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_578_30_chain : (named_envelope_578_30.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_578_30_head : (named_envelope_578_30.map Internal.SnakyRows009.namedCellKey).head? = some (647 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_578_30_last : (named_envelope_578_30.map Internal.SnakyRows009.namedCellKey).getLast? = some (901 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_578_28 : List Cell := Internal.SnakyRows009.named_envelope_578_29 ++ Internal.SnakyRows009.named_envelope_578_30
theorem Internal.SnakyRows009.named_envelope_578_28_chain : (named_envelope_578_28.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_578_29 Internal.SnakyRows009.named_envelope_578_30 (646 : ℤ) (647 : ℤ)
    Internal.SnakyRows009.named_envelope_578_29_chain Internal.SnakyRows009.named_envelope_578_30_chain Internal.SnakyRows009.named_envelope_578_29_last Internal.SnakyRows009.named_envelope_578_30_head (by decide)
theorem Internal.SnakyRows009.named_envelope_578_28_head : (named_envelope_578_28.map Internal.SnakyRows009.namedCellKey).head? = some (517 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_578_29 Internal.SnakyRows009.named_envelope_578_30 (517 : ℤ) Internal.SnakyRows009.named_envelope_578_29_head
theorem Internal.SnakyRows009.named_envelope_578_28_last : (named_envelope_578_28.map Internal.SnakyRows009.namedCellKey).getLast? = some (901 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_578_29 Internal.SnakyRows009.named_envelope_578_30 (901 : ℤ) Internal.SnakyRows009.named_envelope_578_30_last
def Internal.SnakyRows009.named_envelope_578_24 : List Cell := Internal.SnakyRows009.named_envelope_578_25 ++ Internal.SnakyRows009.named_envelope_578_28
theorem Internal.SnakyRows009.named_envelope_578_24_chain : (named_envelope_578_24.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_578_25 Internal.SnakyRows009.named_envelope_578_28 (516 : ℤ) (517 : ℤ)
    Internal.SnakyRows009.named_envelope_578_25_chain Internal.SnakyRows009.named_envelope_578_28_chain Internal.SnakyRows009.named_envelope_578_25_last Internal.SnakyRows009.named_envelope_578_28_head (by decide)
theorem Internal.SnakyRows009.named_envelope_578_24_head : (named_envelope_578_24.map Internal.SnakyRows009.namedCellKey).head? = some (266 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_578_25 Internal.SnakyRows009.named_envelope_578_28 (266 : ℤ) Internal.SnakyRows009.named_envelope_578_25_head
theorem Internal.SnakyRows009.named_envelope_578_24_last : (named_envelope_578_24.map Internal.SnakyRows009.namedCellKey).getLast? = some (901 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_578_25 Internal.SnakyRows009.named_envelope_578_28 (901 : ℤ) Internal.SnakyRows009.named_envelope_578_28_last
def Internal.SnakyRows009.named_envelope_578_16 : List Cell := Internal.SnakyRows009.named_envelope_578_17 ++ Internal.SnakyRows009.named_envelope_578_24
theorem Internal.SnakyRows009.named_envelope_578_16_chain : (named_envelope_578_16.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_578_17 Internal.SnakyRows009.named_envelope_578_24 (265 : ℤ) (266 : ℤ)
    Internal.SnakyRows009.named_envelope_578_17_chain Internal.SnakyRows009.named_envelope_578_24_chain Internal.SnakyRows009.named_envelope_578_17_last Internal.SnakyRows009.named_envelope_578_24_head (by decide)
theorem Internal.SnakyRows009.named_envelope_578_16_head : (named_envelope_578_16.map Internal.SnakyRows009.namedCellKey).head? = some (-118 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_578_17 Internal.SnakyRows009.named_envelope_578_24 (-118 : ℤ) Internal.SnakyRows009.named_envelope_578_17_head
theorem Internal.SnakyRows009.named_envelope_578_16_last : (named_envelope_578_16.map Internal.SnakyRows009.namedCellKey).getLast? = some (901 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_578_17 Internal.SnakyRows009.named_envelope_578_24 (901 : ℤ) Internal.SnakyRows009.named_envelope_578_24_last
def Internal.SnakyRows009.named_envelope_578_0 : List Cell := Internal.SnakyRows009.named_envelope_578_1 ++ Internal.SnakyRows009.named_envelope_578_16
theorem Internal.SnakyRows009.named_envelope_578_0_chain : (named_envelope_578_0.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_578_1 Internal.SnakyRows009.named_envelope_578_16 (-119 : ℤ) (-118 : ℤ)
    Internal.SnakyRows009.named_envelope_578_1_chain Internal.SnakyRows009.named_envelope_578_16_chain Internal.SnakyRows009.named_envelope_578_1_last Internal.SnakyRows009.named_envelope_578_16_head (by decide)
theorem Internal.SnakyRows009.named_envelope_578_0_head : (named_envelope_578_0.map Internal.SnakyRows009.namedCellKey).head? = some (-1025 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_578_1 Internal.SnakyRows009.named_envelope_578_16 (-1025 : ℤ) Internal.SnakyRows009.named_envelope_578_1_head
theorem Internal.SnakyRows009.named_envelope_578_0_last : (named_envelope_578_0.map Internal.SnakyRows009.namedCellKey).getLast? = some (901 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_578_1 Internal.SnakyRows009.named_envelope_578_16 (901 : ℤ) Internal.SnakyRows009.named_envelope_578_16_last
theorem Internal.SnakyRows009.named_envelope_578_nodup : (Internal.SnakyRows009.named_envelope_578_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows009.named_nodup_of_chain Internal.SnakyRows009.named_envelope_578_0 Internal.SnakyRows009.named_envelope_578_0_chain
def envelope_578 : Finset Cell := ⟨(Internal.SnakyRows009.named_envelope_578_0 : Multiset Cell), Internal.SnakyRows009.named_envelope_578_nodup⟩
def childrenC_578 : Fin 2 → Finset Cell := ![(placedSet 4 (0, 1) required_574), (placedSet 1 (0, -1) required_2)]
def childrenD_578 : Fin 2 → Finset Cell := ![(placedSet 4 (0, 1) envelope_574), (placedSet 1 (0, -1) envelope_2)]
theorem common_sub_578 : commonEnvelope childrenD_578 ⊆ insert (0, 0) required_578 := by decide
theorem child_required_sub_578 : ∀ j, childrenC_578 j ⊆ insert (0, 0) required_578 := by decide
theorem Internal.SnakyRows009.containment_578_0 :
    placedSet 4 (0, 1) envelope_574 ⊆ envelope_578 := by decide +kernel
theorem Internal.SnakyRows009.containment_578_1 :
    placedSet 1 (0, -1) envelope_2 ⊆ envelope_578 := by decide
theorem child_envelope_sub_578 : ∀ j, childrenD_578 j ⊆ envelope_578 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows009.containment_578_0
  · exact Internal.SnakyRows009.containment_578_1
theorem pivot_mem_578 : (0, 0) ∈ envelope_578 := by decide
theorem children_work_578 : ∀ j, Template HasSnaky 24 (childrenC_578 j) (childrenD_578 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_574 4 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_2 1 (0, -1)).mono (by decide)
theorem row_works_578 : Template HasSnaky 25 required_578 envelope_578 := by
  refine compose HasSnaky 24 childrenC_578 childrenD_578 children_work_578 (0, 0)
    required_578 envelope_578 pivot_mem_578 child_required_sub_578 child_envelope_sub_578 ?_
  intro b hb; exact common_sub_578 (mem_commonEnvelope childrenD_578 b hb)
end SnakyConditional

end OAI
