import OAI.GameTheory.SnakyConditional.Templates.Level26Part07

namespace OAI

namespace SnakyConditional
def required_583 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (-1, 2)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows009.named_envelope_583_4 : List Cell := ([(-8, 5), (-8, 6), (-8, 8), (-7, 5), (-7, 6), (-7, 7), (-7, 8), (-6, 1), (-6, 3), (-6, 5)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_583_4_chain : (named_envelope_583_4.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_583_4_head : (named_envelope_583_4.map Internal.SnakyRows009.namedCellKey).head? = some (-1019 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_583_4_last : (named_envelope_583_4.map Internal.SnakyRows009.namedCellKey).getLast? = some (-763 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_583_5 : List Cell := ([(-6, 6), (-6, 7), (-6, 8), (-6, 9), (-6, 10), (-6, 11), (-5, 1), (-5, 2), (-5, 3), (-5, 4)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_583_5_chain : (named_envelope_583_5.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_583_5_head : (named_envelope_583_5.map Internal.SnakyRows009.namedCellKey).head? = some (-762 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_583_5_last : (named_envelope_583_5.map Internal.SnakyRows009.namedCellKey).getLast? = some (-636 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_583_3 : List Cell := Internal.SnakyRows009.named_envelope_583_4 ++ Internal.SnakyRows009.named_envelope_583_5
theorem Internal.SnakyRows009.named_envelope_583_3_chain : (named_envelope_583_3.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_583_4 Internal.SnakyRows009.named_envelope_583_5 (-763 : ℤ) (-762 : ℤ)
    Internal.SnakyRows009.named_envelope_583_4_chain Internal.SnakyRows009.named_envelope_583_5_chain Internal.SnakyRows009.named_envelope_583_4_last Internal.SnakyRows009.named_envelope_583_5_head (by decide)
theorem Internal.SnakyRows009.named_envelope_583_3_head : (named_envelope_583_3.map Internal.SnakyRows009.namedCellKey).head? = some (-1019 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_583_4 Internal.SnakyRows009.named_envelope_583_5 (-1019 : ℤ) Internal.SnakyRows009.named_envelope_583_4_head
theorem Internal.SnakyRows009.named_envelope_583_3_last : (named_envelope_583_3.map Internal.SnakyRows009.namedCellKey).getLast? = some (-636 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_583_4 Internal.SnakyRows009.named_envelope_583_5 (-636 : ℤ) Internal.SnakyRows009.named_envelope_583_5_last
def Internal.SnakyRows009.named_envelope_583_7 : List Cell := ([(-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-4, 1), (-4, 2), (-4, 3), (-4, 4)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_583_7_chain : (named_envelope_583_7.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_583_7_head : (named_envelope_583_7.map Internal.SnakyRows009.namedCellKey).head? = some (-635 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_583_7_last : (named_envelope_583_7.map Internal.SnakyRows009.namedCellKey).getLast? = some (-508 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_583_8 : List Cell := ([(-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-4, 13), (-3, 0), (-3, 1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_583_8_chain : (named_envelope_583_8.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_583_8_head : (named_envelope_583_8.map Internal.SnakyRows009.namedCellKey).head? = some (-507 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_583_8_last : (named_envelope_583_8.map Internal.SnakyRows009.namedCellKey).getLast? = some (-383 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_583_6 : List Cell := Internal.SnakyRows009.named_envelope_583_7 ++ Internal.SnakyRows009.named_envelope_583_8
theorem Internal.SnakyRows009.named_envelope_583_6_chain : (named_envelope_583_6.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_583_7 Internal.SnakyRows009.named_envelope_583_8 (-508 : ℤ) (-507 : ℤ)
    Internal.SnakyRows009.named_envelope_583_7_chain Internal.SnakyRows009.named_envelope_583_8_chain Internal.SnakyRows009.named_envelope_583_7_last Internal.SnakyRows009.named_envelope_583_8_head (by decide)
theorem Internal.SnakyRows009.named_envelope_583_6_head : (named_envelope_583_6.map Internal.SnakyRows009.namedCellKey).head? = some (-635 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_583_7 Internal.SnakyRows009.named_envelope_583_8 (-635 : ℤ) Internal.SnakyRows009.named_envelope_583_7_head
theorem Internal.SnakyRows009.named_envelope_583_6_last : (named_envelope_583_6.map Internal.SnakyRows009.namedCellKey).getLast? = some (-383 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_583_7 Internal.SnakyRows009.named_envelope_583_8 (-383 : ℤ) Internal.SnakyRows009.named_envelope_583_8_last
def Internal.SnakyRows009.named_envelope_583_2 : List Cell := Internal.SnakyRows009.named_envelope_583_3 ++ Internal.SnakyRows009.named_envelope_583_6
theorem Internal.SnakyRows009.named_envelope_583_2_chain : (named_envelope_583_2.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_583_3 Internal.SnakyRows009.named_envelope_583_6 (-636 : ℤ) (-635 : ℤ)
    Internal.SnakyRows009.named_envelope_583_3_chain Internal.SnakyRows009.named_envelope_583_6_chain Internal.SnakyRows009.named_envelope_583_3_last Internal.SnakyRows009.named_envelope_583_6_head (by decide)
theorem Internal.SnakyRows009.named_envelope_583_2_head : (named_envelope_583_2.map Internal.SnakyRows009.namedCellKey).head? = some (-1019 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_583_3 Internal.SnakyRows009.named_envelope_583_6 (-1019 : ℤ) Internal.SnakyRows009.named_envelope_583_3_head
theorem Internal.SnakyRows009.named_envelope_583_2_last : (named_envelope_583_2.map Internal.SnakyRows009.namedCellKey).getLast? = some (-383 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_583_3 Internal.SnakyRows009.named_envelope_583_6 (-383 : ℤ) Internal.SnakyRows009.named_envelope_583_6_last
def Internal.SnakyRows009.named_envelope_583_11 : List Cell := ([(-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_583_11_chain : (named_envelope_583_11.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_583_11_head : (named_envelope_583_11.map Internal.SnakyRows009.namedCellKey).head? = some (-382 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_583_11_last : (named_envelope_583_11.map Internal.SnakyRows009.namedCellKey).getLast? = some (-373 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_583_12 : List Cell := ([(-3, 12), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_583_12_chain : (named_envelope_583_12.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_583_12_head : (named_envelope_583_12.map Internal.SnakyRows009.namedCellKey).head? = some (-372 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_583_12_last : (named_envelope_583_12.map Internal.SnakyRows009.namedCellKey).getLast? = some (-246 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_583_10 : List Cell := Internal.SnakyRows009.named_envelope_583_11 ++ Internal.SnakyRows009.named_envelope_583_12
theorem Internal.SnakyRows009.named_envelope_583_10_chain : (named_envelope_583_10.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_583_11 Internal.SnakyRows009.named_envelope_583_12 (-373 : ℤ) (-372 : ℤ)
    Internal.SnakyRows009.named_envelope_583_11_chain Internal.SnakyRows009.named_envelope_583_12_chain Internal.SnakyRows009.named_envelope_583_11_last Internal.SnakyRows009.named_envelope_583_12_head (by decide)
theorem Internal.SnakyRows009.named_envelope_583_10_head : (named_envelope_583_10.map Internal.SnakyRows009.namedCellKey).head? = some (-382 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_583_11 Internal.SnakyRows009.named_envelope_583_12 (-382 : ℤ) Internal.SnakyRows009.named_envelope_583_11_head
theorem Internal.SnakyRows009.named_envelope_583_10_last : (named_envelope_583_10.map Internal.SnakyRows009.namedCellKey).getLast? = some (-246 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_583_11 Internal.SnakyRows009.named_envelope_583_12 (-246 : ℤ) Internal.SnakyRows009.named_envelope_583_12_last
def Internal.SnakyRows009.named_envelope_583_14 : List Cell := ([(-2, 11), (-2, 12), (-2, 13), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_583_14_chain : (named_envelope_583_14.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_583_14_head : (named_envelope_583_14.map Internal.SnakyRows009.namedCellKey).head? = some (-245 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_583_14_last : (named_envelope_583_14.map Internal.SnakyRows009.namedCellKey).getLast? = some (-122 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_583_15 : List Cell := ([(-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_583_15_chain : (named_envelope_583_15.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_583_15_head : (named_envelope_583_15.map Internal.SnakyRows009.namedCellKey).head? = some (-121 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_583_15_last : (named_envelope_583_15.map Internal.SnakyRows009.namedCellKey).getLast? = some (1 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_583_13 : List Cell := Internal.SnakyRows009.named_envelope_583_14 ++ Internal.SnakyRows009.named_envelope_583_15
theorem Internal.SnakyRows009.named_envelope_583_13_chain : (named_envelope_583_13.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_583_14 Internal.SnakyRows009.named_envelope_583_15 (-122 : ℤ) (-121 : ℤ)
    Internal.SnakyRows009.named_envelope_583_14_chain Internal.SnakyRows009.named_envelope_583_15_chain Internal.SnakyRows009.named_envelope_583_14_last Internal.SnakyRows009.named_envelope_583_15_head (by decide)
theorem Internal.SnakyRows009.named_envelope_583_13_head : (named_envelope_583_13.map Internal.SnakyRows009.namedCellKey).head? = some (-245 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_583_14 Internal.SnakyRows009.named_envelope_583_15 (-245 : ℤ) Internal.SnakyRows009.named_envelope_583_14_head
theorem Internal.SnakyRows009.named_envelope_583_13_last : (named_envelope_583_13.map Internal.SnakyRows009.namedCellKey).getLast? = some (1 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_583_14 Internal.SnakyRows009.named_envelope_583_15 (1 : ℤ) Internal.SnakyRows009.named_envelope_583_15_last
def Internal.SnakyRows009.named_envelope_583_9 : List Cell := Internal.SnakyRows009.named_envelope_583_10 ++ Internal.SnakyRows009.named_envelope_583_13
theorem Internal.SnakyRows009.named_envelope_583_9_chain : (named_envelope_583_9.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_583_10 Internal.SnakyRows009.named_envelope_583_13 (-246 : ℤ) (-245 : ℤ)
    Internal.SnakyRows009.named_envelope_583_10_chain Internal.SnakyRows009.named_envelope_583_13_chain Internal.SnakyRows009.named_envelope_583_10_last Internal.SnakyRows009.named_envelope_583_13_head (by decide)
theorem Internal.SnakyRows009.named_envelope_583_9_head : (named_envelope_583_9.map Internal.SnakyRows009.namedCellKey).head? = some (-382 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_583_10 Internal.SnakyRows009.named_envelope_583_13 (-382 : ℤ) Internal.SnakyRows009.named_envelope_583_10_head
theorem Internal.SnakyRows009.named_envelope_583_9_last : (named_envelope_583_9.map Internal.SnakyRows009.namedCellKey).getLast? = some (1 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_583_10 Internal.SnakyRows009.named_envelope_583_13 (1 : ℤ) Internal.SnakyRows009.named_envelope_583_13_last
def Internal.SnakyRows009.named_envelope_583_1 : List Cell := Internal.SnakyRows009.named_envelope_583_2 ++ Internal.SnakyRows009.named_envelope_583_9
theorem Internal.SnakyRows009.named_envelope_583_1_chain : (named_envelope_583_1.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_583_2 Internal.SnakyRows009.named_envelope_583_9 (-383 : ℤ) (-382 : ℤ)
    Internal.SnakyRows009.named_envelope_583_2_chain Internal.SnakyRows009.named_envelope_583_9_chain Internal.SnakyRows009.named_envelope_583_2_last Internal.SnakyRows009.named_envelope_583_9_head (by decide)
theorem Internal.SnakyRows009.named_envelope_583_1_head : (named_envelope_583_1.map Internal.SnakyRows009.namedCellKey).head? = some (-1019 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_583_2 Internal.SnakyRows009.named_envelope_583_9 (-1019 : ℤ) Internal.SnakyRows009.named_envelope_583_2_head
theorem Internal.SnakyRows009.named_envelope_583_1_last : (named_envelope_583_1.map Internal.SnakyRows009.namedCellKey).getLast? = some (1 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_583_2 Internal.SnakyRows009.named_envelope_583_9 (1 : ℤ) Internal.SnakyRows009.named_envelope_583_9_last
def Internal.SnakyRows009.named_envelope_583_19 : List Cell := ([(0, 2), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -5)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_583_19_chain : (named_envelope_583_19.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_583_19_head : (named_envelope_583_19.map Internal.SnakyRows009.namedCellKey).head? = some (2 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_583_19_last : (named_envelope_583_19.map Internal.SnakyRows009.namedCellKey).getLast? = some (123 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_583_20 : List Cell := ([(1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_583_20_chain : (named_envelope_583_20.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_583_20_head : (named_envelope_583_20.map Internal.SnakyRows009.namedCellKey).head? = some (124 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_583_20_last : (named_envelope_583_20.map Internal.SnakyRows009.namedCellKey).getLast? = some (134 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_583_18 : List Cell := Internal.SnakyRows009.named_envelope_583_19 ++ Internal.SnakyRows009.named_envelope_583_20
theorem Internal.SnakyRows009.named_envelope_583_18_chain : (named_envelope_583_18.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_583_19 Internal.SnakyRows009.named_envelope_583_20 (123 : ℤ) (124 : ℤ)
    Internal.SnakyRows009.named_envelope_583_19_chain Internal.SnakyRows009.named_envelope_583_20_chain Internal.SnakyRows009.named_envelope_583_19_last Internal.SnakyRows009.named_envelope_583_20_head (by decide)
theorem Internal.SnakyRows009.named_envelope_583_18_head : (named_envelope_583_18.map Internal.SnakyRows009.namedCellKey).head? = some (2 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_583_19 Internal.SnakyRows009.named_envelope_583_20 (2 : ℤ) Internal.SnakyRows009.named_envelope_583_19_head
theorem Internal.SnakyRows009.named_envelope_583_18_last : (named_envelope_583_18.map Internal.SnakyRows009.namedCellKey).getLast? = some (134 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_583_19 Internal.SnakyRows009.named_envelope_583_20 (134 : ℤ) Internal.SnakyRows009.named_envelope_583_20_last
def Internal.SnakyRows009.named_envelope_583_22 : List Cell := ([(1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_583_22_chain : (named_envelope_583_22.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_583_22_head : (named_envelope_583_22.map Internal.SnakyRows009.namedCellKey).head? = some (135 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_583_22_last : (named_envelope_583_22.map Internal.SnakyRows009.namedCellKey).getLast? = some (256 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_583_23 : List Cell := ([(2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_583_23_chain : (named_envelope_583_23.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_583_23_head : (named_envelope_583_23.map Internal.SnakyRows009.namedCellKey).head? = some (257 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_583_23_last : (named_envelope_583_23.map Internal.SnakyRows009.namedCellKey).getLast? = some (267 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_583_21 : List Cell := Internal.SnakyRows009.named_envelope_583_22 ++ Internal.SnakyRows009.named_envelope_583_23
theorem Internal.SnakyRows009.named_envelope_583_21_chain : (named_envelope_583_21.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_583_22 Internal.SnakyRows009.named_envelope_583_23 (256 : ℤ) (257 : ℤ)
    Internal.SnakyRows009.named_envelope_583_22_chain Internal.SnakyRows009.named_envelope_583_23_chain Internal.SnakyRows009.named_envelope_583_22_last Internal.SnakyRows009.named_envelope_583_23_head (by decide)
theorem Internal.SnakyRows009.named_envelope_583_21_head : (named_envelope_583_21.map Internal.SnakyRows009.namedCellKey).head? = some (135 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_583_22 Internal.SnakyRows009.named_envelope_583_23 (135 : ℤ) Internal.SnakyRows009.named_envelope_583_22_head
theorem Internal.SnakyRows009.named_envelope_583_21_last : (named_envelope_583_21.map Internal.SnakyRows009.namedCellKey).getLast? = some (267 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_583_22 Internal.SnakyRows009.named_envelope_583_23 (267 : ℤ) Internal.SnakyRows009.named_envelope_583_23_last
def Internal.SnakyRows009.named_envelope_583_17 : List Cell := Internal.SnakyRows009.named_envelope_583_18 ++ Internal.SnakyRows009.named_envelope_583_21
theorem Internal.SnakyRows009.named_envelope_583_17_chain : (named_envelope_583_17.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_583_18 Internal.SnakyRows009.named_envelope_583_21 (134 : ℤ) (135 : ℤ)
    Internal.SnakyRows009.named_envelope_583_18_chain Internal.SnakyRows009.named_envelope_583_21_chain Internal.SnakyRows009.named_envelope_583_18_last Internal.SnakyRows009.named_envelope_583_21_head (by decide)
theorem Internal.SnakyRows009.named_envelope_583_17_head : (named_envelope_583_17.map Internal.SnakyRows009.namedCellKey).head? = some (2 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_583_18 Internal.SnakyRows009.named_envelope_583_21 (2 : ℤ) Internal.SnakyRows009.named_envelope_583_18_head
theorem Internal.SnakyRows009.named_envelope_583_17_last : (named_envelope_583_17.map Internal.SnakyRows009.namedCellKey).getLast? = some (267 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_583_18 Internal.SnakyRows009.named_envelope_583_21 (267 : ℤ) Internal.SnakyRows009.named_envelope_583_21_last
def Internal.SnakyRows009.named_envelope_583_26 : List Cell := ([(3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_583_26_chain : (named_envelope_583_26.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_583_26_head : (named_envelope_583_26.map Internal.SnakyRows009.namedCellKey).head? = some (379 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_583_26_last : (named_envelope_583_26.map Internal.SnakyRows009.namedCellKey).getLast? = some (388 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_583_27 : List Cell := ([(3, 5), (3, 6), (3, 7), (3, 8), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_583_27_chain : (named_envelope_583_27.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_583_27_head : (named_envelope_583_27.map Internal.SnakyRows009.namedCellKey).head? = some (389 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_583_27_last : (named_envelope_583_27.map Internal.SnakyRows009.namedCellKey).getLast? = some (515 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_583_25 : List Cell := Internal.SnakyRows009.named_envelope_583_26 ++ Internal.SnakyRows009.named_envelope_583_27
theorem Internal.SnakyRows009.named_envelope_583_25_chain : (named_envelope_583_25.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_583_26 Internal.SnakyRows009.named_envelope_583_27 (388 : ℤ) (389 : ℤ)
    Internal.SnakyRows009.named_envelope_583_26_chain Internal.SnakyRows009.named_envelope_583_27_chain Internal.SnakyRows009.named_envelope_583_26_last Internal.SnakyRows009.named_envelope_583_27_head (by decide)
theorem Internal.SnakyRows009.named_envelope_583_25_head : (named_envelope_583_25.map Internal.SnakyRows009.namedCellKey).head? = some (379 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_583_26 Internal.SnakyRows009.named_envelope_583_27 (379 : ℤ) Internal.SnakyRows009.named_envelope_583_26_head
theorem Internal.SnakyRows009.named_envelope_583_25_last : (named_envelope_583_25.map Internal.SnakyRows009.namedCellKey).getLast? = some (515 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_583_26 Internal.SnakyRows009.named_envelope_583_27 (515 : ℤ) Internal.SnakyRows009.named_envelope_583_27_last
def Internal.SnakyRows009.named_envelope_583_29 : List Cell := ([(4, 6), (4, 8), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -3)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_583_29_chain : (named_envelope_583_29.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_583_29_head : (named_envelope_583_29.map Internal.SnakyRows009.namedCellKey).head? = some (518 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_583_29_last : (named_envelope_583_29.map Internal.SnakyRows009.namedCellKey).getLast? = some (765 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_583_30 : List Cell := ([(6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, 1), (7, 2), (7, 3), (8, 1), (8, 3)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_583_30_chain : (named_envelope_583_30.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_583_30_head : (named_envelope_583_30.map Internal.SnakyRows009.namedCellKey).head? = some (766 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_583_30_last : (named_envelope_583_30.map Internal.SnakyRows009.namedCellKey).getLast? = some (1027 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_583_28 : List Cell := Internal.SnakyRows009.named_envelope_583_29 ++ Internal.SnakyRows009.named_envelope_583_30
theorem Internal.SnakyRows009.named_envelope_583_28_chain : (named_envelope_583_28.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_583_29 Internal.SnakyRows009.named_envelope_583_30 (765 : ℤ) (766 : ℤ)
    Internal.SnakyRows009.named_envelope_583_29_chain Internal.SnakyRows009.named_envelope_583_30_chain Internal.SnakyRows009.named_envelope_583_29_last Internal.SnakyRows009.named_envelope_583_30_head (by decide)
theorem Internal.SnakyRows009.named_envelope_583_28_head : (named_envelope_583_28.map Internal.SnakyRows009.namedCellKey).head? = some (518 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_583_29 Internal.SnakyRows009.named_envelope_583_30 (518 : ℤ) Internal.SnakyRows009.named_envelope_583_29_head
theorem Internal.SnakyRows009.named_envelope_583_28_last : (named_envelope_583_28.map Internal.SnakyRows009.namedCellKey).getLast? = some (1027 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_583_29 Internal.SnakyRows009.named_envelope_583_30 (1027 : ℤ) Internal.SnakyRows009.named_envelope_583_30_last
def Internal.SnakyRows009.named_envelope_583_24 : List Cell := Internal.SnakyRows009.named_envelope_583_25 ++ Internal.SnakyRows009.named_envelope_583_28
theorem Internal.SnakyRows009.named_envelope_583_24_chain : (named_envelope_583_24.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_583_25 Internal.SnakyRows009.named_envelope_583_28 (515 : ℤ) (518 : ℤ)
    Internal.SnakyRows009.named_envelope_583_25_chain Internal.SnakyRows009.named_envelope_583_28_chain Internal.SnakyRows009.named_envelope_583_25_last Internal.SnakyRows009.named_envelope_583_28_head (by decide)
theorem Internal.SnakyRows009.named_envelope_583_24_head : (named_envelope_583_24.map Internal.SnakyRows009.namedCellKey).head? = some (379 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_583_25 Internal.SnakyRows009.named_envelope_583_28 (379 : ℤ) Internal.SnakyRows009.named_envelope_583_25_head
theorem Internal.SnakyRows009.named_envelope_583_24_last : (named_envelope_583_24.map Internal.SnakyRows009.namedCellKey).getLast? = some (1027 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_583_25 Internal.SnakyRows009.named_envelope_583_28 (1027 : ℤ) Internal.SnakyRows009.named_envelope_583_28_last
def Internal.SnakyRows009.named_envelope_583_16 : List Cell := Internal.SnakyRows009.named_envelope_583_17 ++ Internal.SnakyRows009.named_envelope_583_24
theorem Internal.SnakyRows009.named_envelope_583_16_chain : (named_envelope_583_16.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_583_17 Internal.SnakyRows009.named_envelope_583_24 (267 : ℤ) (379 : ℤ)
    Internal.SnakyRows009.named_envelope_583_17_chain Internal.SnakyRows009.named_envelope_583_24_chain Internal.SnakyRows009.named_envelope_583_17_last Internal.SnakyRows009.named_envelope_583_24_head (by decide)
theorem Internal.SnakyRows009.named_envelope_583_16_head : (named_envelope_583_16.map Internal.SnakyRows009.namedCellKey).head? = some (2 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_583_17 Internal.SnakyRows009.named_envelope_583_24 (2 : ℤ) Internal.SnakyRows009.named_envelope_583_17_head
theorem Internal.SnakyRows009.named_envelope_583_16_last : (named_envelope_583_16.map Internal.SnakyRows009.namedCellKey).getLast? = some (1027 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_583_17 Internal.SnakyRows009.named_envelope_583_24 (1027 : ℤ) Internal.SnakyRows009.named_envelope_583_24_last
def Internal.SnakyRows009.named_envelope_583_0 : List Cell := Internal.SnakyRows009.named_envelope_583_1 ++ Internal.SnakyRows009.named_envelope_583_16
theorem Internal.SnakyRows009.named_envelope_583_0_chain : (named_envelope_583_0.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_583_1 Internal.SnakyRows009.named_envelope_583_16 (1 : ℤ) (2 : ℤ)
    Internal.SnakyRows009.named_envelope_583_1_chain Internal.SnakyRows009.named_envelope_583_16_chain Internal.SnakyRows009.named_envelope_583_1_last Internal.SnakyRows009.named_envelope_583_16_head (by decide)
theorem Internal.SnakyRows009.named_envelope_583_0_head : (named_envelope_583_0.map Internal.SnakyRows009.namedCellKey).head? = some (-1019 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_583_1 Internal.SnakyRows009.named_envelope_583_16 (-1019 : ℤ) Internal.SnakyRows009.named_envelope_583_1_head
theorem Internal.SnakyRows009.named_envelope_583_0_last : (named_envelope_583_0.map Internal.SnakyRows009.namedCellKey).getLast? = some (1027 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_583_1 Internal.SnakyRows009.named_envelope_583_16 (1027 : ℤ) Internal.SnakyRows009.named_envelope_583_16_last
theorem Internal.SnakyRows009.named_envelope_583_nodup : (Internal.SnakyRows009.named_envelope_583_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows009.named_nodup_of_chain Internal.SnakyRows009.named_envelope_583_0 Internal.SnakyRows009.named_envelope_583_0_chain
def envelope_583 : Finset Cell := ⟨(Internal.SnakyRows009.named_envelope_583_0 : Multiset Cell), Internal.SnakyRows009.named_envelope_583_nodup⟩
def childrenC_583 : Fin 4 → Finset Cell := ![(placedSet 5 (0, -1) required_25), (placedSet 0 (1, 0) required_525), (placedSet 0 (-2, 4) required_582), (placedSet 3 (-1, 3) required_221)]
def childrenD_583 : Fin 4 → Finset Cell := ![(placedSet 5 (0, -1) envelope_25), (placedSet 0 (1, 0) envelope_525), (placedSet 0 (-2, 4) envelope_582), (placedSet 3 (-1, 3) envelope_221)]
theorem common_sub_583 : commonEnvelope childrenD_583 ⊆ insert (0, 0) required_583 := by decide
theorem child_required_sub_583 : ∀ j, childrenC_583 j ⊆ insert (0, 0) required_583 := by decide
theorem Internal.SnakyRows009.containment_583_0 :
    placedSet 5 (0, -1) envelope_25 ⊆ envelope_583 := by decide
theorem Internal.SnakyRows009.containment_583_1 :
    placedSet 0 (1, 0) envelope_525 ⊆ envelope_583 := by decide
theorem Internal.SnakyRows009.containment_583_2 :
    placedSet 0 (-2, 4) envelope_582 ⊆ envelope_583 := by decide +kernel
theorem Internal.SnakyRows009.containment_583_3 :
    placedSet 3 (-1, 3) envelope_221 ⊆ envelope_583 := by decide
theorem child_envelope_sub_583 : ∀ j, childrenD_583 j ⊆ envelope_583 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows009.containment_583_0
  · exact Internal.SnakyRows009.containment_583_1
  · exact Internal.SnakyRows009.containment_583_2
  · exact Internal.SnakyRows009.containment_583_3
theorem pivot_mem_583 : (0, 0) ∈ envelope_583 := by decide
theorem children_work_583 : ∀ j, Template HasSnaky 24 (childrenC_583 j) (childrenD_583 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_25 5 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_525 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_582 0 (-2, 4)).mono (by decide)
  · exact (placed_template_map row_works_221 3 (-1, 3)).mono (by decide)
theorem row_works_583 : Template HasSnaky 25 required_583 envelope_583 := by
  refine compose HasSnaky 24 childrenC_583 childrenD_583 children_work_583 (0, 0)
    required_583 envelope_583 pivot_mem_583 child_required_sub_583 child_envelope_sub_583 ?_
  intro b hb; exact common_sub_583 (mem_commonEnvelope childrenD_583 b hb)
end SnakyConditional

end OAI
