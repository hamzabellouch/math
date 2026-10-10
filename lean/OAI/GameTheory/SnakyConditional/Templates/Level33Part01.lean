import OAI.GameTheory.SnakyConditional.Templates.Level32Part02

namespace OAI

namespace SnakyConditional
def required_606 : Finset Cell := ⟨(([(-1, -3), (0, -3), (0, -2), (2, -2)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows012A.named_envelope_606_5 : List Cell := ([(-5, -1), (-5, 0), (-5, 1), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_5_chain : (named_envelope_606_5.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_5_head : (named_envelope_606_5.map Internal.SnakyRows012A.namedCellKey).head? = some (-641 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_5_last : (named_envelope_606_5.map Internal.SnakyRows012A.namedCellKey).getLast? = some (-509 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_6 : List Cell := ([(-4, 4), (-4, 6), (-4, 7), (-4, 9), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_6_chain : (named_envelope_606_6.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_6_head : (named_envelope_606_6.map Internal.SnakyRows012A.namedCellKey).head? = some (-508 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_6_last : (named_envelope_606_6.map Internal.SnakyRows012A.namedCellKey).getLast? = some (-381 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_4 : List Cell := Internal.SnakyRows012A.named_envelope_606_5 ++ Internal.SnakyRows012A.named_envelope_606_6
theorem Internal.SnakyRows012A.named_envelope_606_4_chain : (named_envelope_606_4.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_5 Internal.SnakyRows012A.named_envelope_606_6 (-509 : ℤ) (-508 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_5_chain Internal.SnakyRows012A.named_envelope_606_6_chain Internal.SnakyRows012A.named_envelope_606_5_last Internal.SnakyRows012A.named_envelope_606_6_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_4_head : (named_envelope_606_4.map Internal.SnakyRows012A.namedCellKey).head? = some (-641 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_5 Internal.SnakyRows012A.named_envelope_606_6 (-641 : ℤ) Internal.SnakyRows012A.named_envelope_606_5_head
theorem Internal.SnakyRows012A.named_envelope_606_4_last : (named_envelope_606_4.map Internal.SnakyRows012A.namedCellKey).getLast? = some (-381 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_5 Internal.SnakyRows012A.named_envelope_606_6 (-381 : ℤ) Internal.SnakyRows012A.named_envelope_606_6_last
def Internal.SnakyRows012A.named_envelope_606_8 : List Cell := ([(-3, 4), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-2, -1), (-2, 0), (-2, 1), (-2, 2)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_8_chain : (named_envelope_606_8.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_8_head : (named_envelope_606_8.map Internal.SnakyRows012A.namedCellKey).head? = some (-380 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_8_last : (named_envelope_606_8.map Internal.SnakyRows012A.namedCellKey).getLast? = some (-254 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_9 : List Cell := ([(-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_9_chain : (named_envelope_606_9.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_9_head : (named_envelope_606_9.map Internal.SnakyRows012A.namedCellKey).head? = some (-253 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_9_last : (named_envelope_606_9.map Internal.SnakyRows012A.namedCellKey).getLast? = some (-244 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_7 : List Cell := Internal.SnakyRows012A.named_envelope_606_8 ++ Internal.SnakyRows012A.named_envelope_606_9
theorem Internal.SnakyRows012A.named_envelope_606_7_chain : (named_envelope_606_7.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_8 Internal.SnakyRows012A.named_envelope_606_9 (-254 : ℤ) (-253 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_8_chain Internal.SnakyRows012A.named_envelope_606_9_chain Internal.SnakyRows012A.named_envelope_606_8_last Internal.SnakyRows012A.named_envelope_606_9_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_7_head : (named_envelope_606_7.map Internal.SnakyRows012A.namedCellKey).head? = some (-380 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_8 Internal.SnakyRows012A.named_envelope_606_9 (-380 : ℤ) Internal.SnakyRows012A.named_envelope_606_8_head
theorem Internal.SnakyRows012A.named_envelope_606_7_last : (named_envelope_606_7.map Internal.SnakyRows012A.namedCellKey).getLast? = some (-244 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_8 Internal.SnakyRows012A.named_envelope_606_9 (-244 : ℤ) Internal.SnakyRows012A.named_envelope_606_9_last
def Internal.SnakyRows012A.named_envelope_606_3 : List Cell := Internal.SnakyRows012A.named_envelope_606_4 ++ Internal.SnakyRows012A.named_envelope_606_7
theorem Internal.SnakyRows012A.named_envelope_606_3_chain : (named_envelope_606_3.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_4 Internal.SnakyRows012A.named_envelope_606_7 (-381 : ℤ) (-380 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_4_chain Internal.SnakyRows012A.named_envelope_606_7_chain Internal.SnakyRows012A.named_envelope_606_4_last Internal.SnakyRows012A.named_envelope_606_7_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_3_head : (named_envelope_606_3.map Internal.SnakyRows012A.namedCellKey).head? = some (-641 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_4 Internal.SnakyRows012A.named_envelope_606_7 (-641 : ℤ) Internal.SnakyRows012A.named_envelope_606_4_head
theorem Internal.SnakyRows012A.named_envelope_606_3_last : (named_envelope_606_3.map Internal.SnakyRows012A.namedCellKey).getLast? = some (-244 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_4 Internal.SnakyRows012A.named_envelope_606_7 (-244 : ℤ) Internal.SnakyRows012A.named_envelope_606_7_last
def Internal.SnakyRows012A.named_envelope_606_12 : List Cell := ([(-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_12_chain : (named_envelope_606_12.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_12_head : (named_envelope_606_12.map Internal.SnakyRows012A.namedCellKey).head? = some (-132 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_12_last : (named_envelope_606_12.map Internal.SnakyRows012A.namedCellKey).getLast? = some (-123 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_13 : List Cell := ([(-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -3), (0, -2), (0, -1)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_13_chain : (named_envelope_606_13.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_13_head : (named_envelope_606_13.map Internal.SnakyRows012A.namedCellKey).head? = some (-122 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_13_last : (named_envelope_606_13.map Internal.SnakyRows012A.namedCellKey).getLast? = some (-1 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_11 : List Cell := Internal.SnakyRows012A.named_envelope_606_12 ++ Internal.SnakyRows012A.named_envelope_606_13
theorem Internal.SnakyRows012A.named_envelope_606_11_chain : (named_envelope_606_11.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_12 Internal.SnakyRows012A.named_envelope_606_13 (-123 : ℤ) (-122 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_12_chain Internal.SnakyRows012A.named_envelope_606_13_chain Internal.SnakyRows012A.named_envelope_606_12_last Internal.SnakyRows012A.named_envelope_606_13_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_11_head : (named_envelope_606_11.map Internal.SnakyRows012A.namedCellKey).head? = some (-132 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_12 Internal.SnakyRows012A.named_envelope_606_13 (-132 : ℤ) Internal.SnakyRows012A.named_envelope_606_12_head
theorem Internal.SnakyRows012A.named_envelope_606_11_last : (named_envelope_606_11.map Internal.SnakyRows012A.namedCellKey).getLast? = some (-1 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_12 Internal.SnakyRows012A.named_envelope_606_13 (-1 : ℤ) Internal.SnakyRows012A.named_envelope_606_13_last
def Internal.SnakyRows012A.named_envelope_606_15 : List Cell := ([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_15_chain : (named_envelope_606_15.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_15_head : (named_envelope_606_15.map Internal.SnakyRows012A.namedCellKey).head? = some (0 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_15_last : (named_envelope_606_15.map Internal.SnakyRows012A.namedCellKey).getLast? = some (8 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_16 : List Cell := ([(0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (1, -7), (1, -6), (1, -5), (1, -4)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_16_chain : (named_envelope_606_16.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_16_head : (named_envelope_606_16.map Internal.SnakyRows012A.namedCellKey).head? = some (9 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_16_last : (named_envelope_606_16.map Internal.SnakyRows012A.namedCellKey).getLast? = some (124 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_14 : List Cell := Internal.SnakyRows012A.named_envelope_606_15 ++ Internal.SnakyRows012A.named_envelope_606_16
theorem Internal.SnakyRows012A.named_envelope_606_14_chain : (named_envelope_606_14.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_15 Internal.SnakyRows012A.named_envelope_606_16 (8 : ℤ) (9 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_15_chain Internal.SnakyRows012A.named_envelope_606_16_chain Internal.SnakyRows012A.named_envelope_606_15_last Internal.SnakyRows012A.named_envelope_606_16_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_14_head : (named_envelope_606_14.map Internal.SnakyRows012A.namedCellKey).head? = some (0 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_15 Internal.SnakyRows012A.named_envelope_606_16 (0 : ℤ) Internal.SnakyRows012A.named_envelope_606_15_head
theorem Internal.SnakyRows012A.named_envelope_606_14_last : (named_envelope_606_14.map Internal.SnakyRows012A.namedCellKey).getLast? = some (124 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_15 Internal.SnakyRows012A.named_envelope_606_16 (124 : ℤ) Internal.SnakyRows012A.named_envelope_606_16_last
def Internal.SnakyRows012A.named_envelope_606_10 : List Cell := Internal.SnakyRows012A.named_envelope_606_11 ++ Internal.SnakyRows012A.named_envelope_606_14
theorem Internal.SnakyRows012A.named_envelope_606_10_chain : (named_envelope_606_10.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_11 Internal.SnakyRows012A.named_envelope_606_14 (-1 : ℤ) (0 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_11_chain Internal.SnakyRows012A.named_envelope_606_14_chain Internal.SnakyRows012A.named_envelope_606_11_last Internal.SnakyRows012A.named_envelope_606_14_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_10_head : (named_envelope_606_10.map Internal.SnakyRows012A.namedCellKey).head? = some (-132 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_11 Internal.SnakyRows012A.named_envelope_606_14 (-132 : ℤ) Internal.SnakyRows012A.named_envelope_606_11_head
theorem Internal.SnakyRows012A.named_envelope_606_10_last : (named_envelope_606_10.map Internal.SnakyRows012A.namedCellKey).getLast? = some (124 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_11 Internal.SnakyRows012A.named_envelope_606_14 (124 : ℤ) Internal.SnakyRows012A.named_envelope_606_14_last
def Internal.SnakyRows012A.named_envelope_606_2 : List Cell := Internal.SnakyRows012A.named_envelope_606_3 ++ Internal.SnakyRows012A.named_envelope_606_10
theorem Internal.SnakyRows012A.named_envelope_606_2_chain : (named_envelope_606_2.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_3 Internal.SnakyRows012A.named_envelope_606_10 (-244 : ℤ) (-132 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_3_chain Internal.SnakyRows012A.named_envelope_606_10_chain Internal.SnakyRows012A.named_envelope_606_3_last Internal.SnakyRows012A.named_envelope_606_10_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_2_head : (named_envelope_606_2.map Internal.SnakyRows012A.namedCellKey).head? = some (-641 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_3 Internal.SnakyRows012A.named_envelope_606_10 (-641 : ℤ) Internal.SnakyRows012A.named_envelope_606_3_head
theorem Internal.SnakyRows012A.named_envelope_606_2_last : (named_envelope_606_2.map Internal.SnakyRows012A.namedCellKey).getLast? = some (124 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_3 Internal.SnakyRows012A.named_envelope_606_10 (124 : ℤ) Internal.SnakyRows012A.named_envelope_606_10_last
def Internal.SnakyRows012A.named_envelope_606_20 : List Cell := ([(1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_20_chain : (named_envelope_606_20.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_20_head : (named_envelope_606_20.map Internal.SnakyRows012A.namedCellKey).head? = some (125 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_20_last : (named_envelope_606_20.map Internal.SnakyRows012A.namedCellKey).getLast? = some (133 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_21 : List Cell := ([(1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (2, -6)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_21_chain : (named_envelope_606_21.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_21_head : (named_envelope_606_21.map Internal.SnakyRows012A.namedCellKey).head? = some (134 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_21_last : (named_envelope_606_21.map Internal.SnakyRows012A.namedCellKey).getLast? = some (250 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_19 : List Cell := Internal.SnakyRows012A.named_envelope_606_20 ++ Internal.SnakyRows012A.named_envelope_606_21
theorem Internal.SnakyRows012A.named_envelope_606_19_chain : (named_envelope_606_19.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_20 Internal.SnakyRows012A.named_envelope_606_21 (133 : ℤ) (134 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_20_chain Internal.SnakyRows012A.named_envelope_606_21_chain Internal.SnakyRows012A.named_envelope_606_20_last Internal.SnakyRows012A.named_envelope_606_21_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_19_head : (named_envelope_606_19.map Internal.SnakyRows012A.namedCellKey).head? = some (125 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_20 Internal.SnakyRows012A.named_envelope_606_21 (125 : ℤ) Internal.SnakyRows012A.named_envelope_606_20_head
theorem Internal.SnakyRows012A.named_envelope_606_19_last : (named_envelope_606_19.map Internal.SnakyRows012A.namedCellKey).getLast? = some (250 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_20 Internal.SnakyRows012A.named_envelope_606_21 (250 : ℤ) Internal.SnakyRows012A.named_envelope_606_21_last
def Internal.SnakyRows012A.named_envelope_606_23 : List Cell := ([(2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_23_chain : (named_envelope_606_23.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_23_head : (named_envelope_606_23.map Internal.SnakyRows012A.namedCellKey).head? = some (251 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_23_last : (named_envelope_606_23.map Internal.SnakyRows012A.namedCellKey).getLast? = some (259 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_24 : List Cell := ([(2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_24_chain : (named_envelope_606_24.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_24_head : (named_envelope_606_24.map Internal.SnakyRows012A.namedCellKey).head? = some (260 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_24_last : (named_envelope_606_24.map Internal.SnakyRows012A.namedCellKey).getLast? = some (269 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_22 : List Cell := Internal.SnakyRows012A.named_envelope_606_23 ++ Internal.SnakyRows012A.named_envelope_606_24
theorem Internal.SnakyRows012A.named_envelope_606_22_chain : (named_envelope_606_22.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_23 Internal.SnakyRows012A.named_envelope_606_24 (259 : ℤ) (260 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_23_chain Internal.SnakyRows012A.named_envelope_606_24_chain Internal.SnakyRows012A.named_envelope_606_23_last Internal.SnakyRows012A.named_envelope_606_24_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_22_head : (named_envelope_606_22.map Internal.SnakyRows012A.namedCellKey).head? = some (251 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_23 Internal.SnakyRows012A.named_envelope_606_24 (251 : ℤ) Internal.SnakyRows012A.named_envelope_606_23_head
theorem Internal.SnakyRows012A.named_envelope_606_22_last : (named_envelope_606_22.map Internal.SnakyRows012A.namedCellKey).getLast? = some (269 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_23 Internal.SnakyRows012A.named_envelope_606_24 (269 : ℤ) Internal.SnakyRows012A.named_envelope_606_24_last
def Internal.SnakyRows012A.named_envelope_606_18 : List Cell := Internal.SnakyRows012A.named_envelope_606_19 ++ Internal.SnakyRows012A.named_envelope_606_22
theorem Internal.SnakyRows012A.named_envelope_606_18_chain : (named_envelope_606_18.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_19 Internal.SnakyRows012A.named_envelope_606_22 (250 : ℤ) (251 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_19_chain Internal.SnakyRows012A.named_envelope_606_22_chain Internal.SnakyRows012A.named_envelope_606_19_last Internal.SnakyRows012A.named_envelope_606_22_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_18_head : (named_envelope_606_18.map Internal.SnakyRows012A.namedCellKey).head? = some (125 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_19 Internal.SnakyRows012A.named_envelope_606_22 (125 : ℤ) Internal.SnakyRows012A.named_envelope_606_19_head
theorem Internal.SnakyRows012A.named_envelope_606_18_last : (named_envelope_606_18.map Internal.SnakyRows012A.namedCellKey).getLast? = some (269 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_19 Internal.SnakyRows012A.named_envelope_606_22 (269 : ℤ) Internal.SnakyRows012A.named_envelope_606_22_last
def Internal.SnakyRows012A.named_envelope_606_27 : List Cell := ([(2, 14), (3, -7), (3, -6), (3, -5), (3, -4), (3, -3), (3, -1), (3, 0), (3, 1)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_27_chain : (named_envelope_606_27.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_27_head : (named_envelope_606_27.map Internal.SnakyRows012A.namedCellKey).head? = some (270 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_27_last : (named_envelope_606_27.map Internal.SnakyRows012A.namedCellKey).getLast? = some (385 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_28 : List Cell := ([(3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_28_chain : (named_envelope_606_28.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_28_head : (named_envelope_606_28.map Internal.SnakyRows012A.namedCellKey).head? = some (386 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_28_last : (named_envelope_606_28.map Internal.SnakyRows012A.namedCellKey).getLast? = some (395 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_26 : List Cell := Internal.SnakyRows012A.named_envelope_606_27 ++ Internal.SnakyRows012A.named_envelope_606_28
theorem Internal.SnakyRows012A.named_envelope_606_26_chain : (named_envelope_606_26.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_27 Internal.SnakyRows012A.named_envelope_606_28 (385 : ℤ) (386 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_27_chain Internal.SnakyRows012A.named_envelope_606_28_chain Internal.SnakyRows012A.named_envelope_606_27_last Internal.SnakyRows012A.named_envelope_606_28_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_26_head : (named_envelope_606_26.map Internal.SnakyRows012A.namedCellKey).head? = some (270 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_27 Internal.SnakyRows012A.named_envelope_606_28 (270 : ℤ) Internal.SnakyRows012A.named_envelope_606_27_head
theorem Internal.SnakyRows012A.named_envelope_606_26_last : (named_envelope_606_26.map Internal.SnakyRows012A.namedCellKey).getLast? = some (395 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_27 Internal.SnakyRows012A.named_envelope_606_28 (395 : ℤ) Internal.SnakyRows012A.named_envelope_606_28_last
def Internal.SnakyRows012A.named_envelope_606_30 : List Cell := ([(3, 12), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_30_chain : (named_envelope_606_30.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_30_head : (named_envelope_606_30.map Internal.SnakyRows012A.namedCellKey).head? = some (396 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_30_last : (named_envelope_606_30.map Internal.SnakyRows012A.namedCellKey).getLast? = some (513 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_31 : List Cell := ([(4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_31_chain : (named_envelope_606_31.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_31_head : (named_envelope_606_31.map Internal.SnakyRows012A.namedCellKey).head? = some (514 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_31_last : (named_envelope_606_31.map Internal.SnakyRows012A.namedCellKey).getLast? = some (523 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_29 : List Cell := Internal.SnakyRows012A.named_envelope_606_30 ++ Internal.SnakyRows012A.named_envelope_606_31
theorem Internal.SnakyRows012A.named_envelope_606_29_chain : (named_envelope_606_29.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_30 Internal.SnakyRows012A.named_envelope_606_31 (513 : ℤ) (514 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_30_chain Internal.SnakyRows012A.named_envelope_606_31_chain Internal.SnakyRows012A.named_envelope_606_30_last Internal.SnakyRows012A.named_envelope_606_31_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_29_head : (named_envelope_606_29.map Internal.SnakyRows012A.namedCellKey).head? = some (396 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_30 Internal.SnakyRows012A.named_envelope_606_31 (396 : ℤ) Internal.SnakyRows012A.named_envelope_606_30_head
theorem Internal.SnakyRows012A.named_envelope_606_29_last : (named_envelope_606_29.map Internal.SnakyRows012A.namedCellKey).getLast? = some (523 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_30 Internal.SnakyRows012A.named_envelope_606_31 (523 : ℤ) Internal.SnakyRows012A.named_envelope_606_31_last
def Internal.SnakyRows012A.named_envelope_606_25 : List Cell := Internal.SnakyRows012A.named_envelope_606_26 ++ Internal.SnakyRows012A.named_envelope_606_29
theorem Internal.SnakyRows012A.named_envelope_606_25_chain : (named_envelope_606_25.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_26 Internal.SnakyRows012A.named_envelope_606_29 (395 : ℤ) (396 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_26_chain Internal.SnakyRows012A.named_envelope_606_29_chain Internal.SnakyRows012A.named_envelope_606_26_last Internal.SnakyRows012A.named_envelope_606_29_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_25_head : (named_envelope_606_25.map Internal.SnakyRows012A.namedCellKey).head? = some (270 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_26 Internal.SnakyRows012A.named_envelope_606_29 (270 : ℤ) Internal.SnakyRows012A.named_envelope_606_26_head
theorem Internal.SnakyRows012A.named_envelope_606_25_last : (named_envelope_606_25.map Internal.SnakyRows012A.namedCellKey).getLast? = some (523 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_26 Internal.SnakyRows012A.named_envelope_606_29 (523 : ℤ) Internal.SnakyRows012A.named_envelope_606_29_last
def Internal.SnakyRows012A.named_envelope_606_17 : List Cell := Internal.SnakyRows012A.named_envelope_606_18 ++ Internal.SnakyRows012A.named_envelope_606_25
theorem Internal.SnakyRows012A.named_envelope_606_17_chain : (named_envelope_606_17.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_18 Internal.SnakyRows012A.named_envelope_606_25 (269 : ℤ) (270 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_18_chain Internal.SnakyRows012A.named_envelope_606_25_chain Internal.SnakyRows012A.named_envelope_606_18_last Internal.SnakyRows012A.named_envelope_606_25_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_17_head : (named_envelope_606_17.map Internal.SnakyRows012A.namedCellKey).head? = some (125 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_18 Internal.SnakyRows012A.named_envelope_606_25 (125 : ℤ) Internal.SnakyRows012A.named_envelope_606_18_head
theorem Internal.SnakyRows012A.named_envelope_606_17_last : (named_envelope_606_17.map Internal.SnakyRows012A.namedCellKey).getLast? = some (523 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_18 Internal.SnakyRows012A.named_envelope_606_25 (523 : ℤ) Internal.SnakyRows012A.named_envelope_606_25_last
def Internal.SnakyRows012A.named_envelope_606_1 : List Cell := Internal.SnakyRows012A.named_envelope_606_2 ++ Internal.SnakyRows012A.named_envelope_606_17
theorem Internal.SnakyRows012A.named_envelope_606_1_chain : (named_envelope_606_1.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_2 Internal.SnakyRows012A.named_envelope_606_17 (124 : ℤ) (125 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_2_chain Internal.SnakyRows012A.named_envelope_606_17_chain Internal.SnakyRows012A.named_envelope_606_2_last Internal.SnakyRows012A.named_envelope_606_17_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_1_head : (named_envelope_606_1.map Internal.SnakyRows012A.namedCellKey).head? = some (-641 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_2 Internal.SnakyRows012A.named_envelope_606_17 (-641 : ℤ) Internal.SnakyRows012A.named_envelope_606_2_head
theorem Internal.SnakyRows012A.named_envelope_606_1_last : (named_envelope_606_1.map Internal.SnakyRows012A.namedCellKey).getLast? = some (523 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_2 Internal.SnakyRows012A.named_envelope_606_17 (523 : ℤ) Internal.SnakyRows012A.named_envelope_606_17_last
def Internal.SnakyRows012A.named_envelope_606_36 : List Cell := ([(4, 12), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_36_chain : (named_envelope_606_36.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_36_head : (named_envelope_606_36.map Internal.SnakyRows012A.namedCellKey).head? = some (524 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_36_last : (named_envelope_606_36.map Internal.SnakyRows012A.namedCellKey).getLast? = some (642 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_37 : List Cell := ([(5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_37_chain : (named_envelope_606_37.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_37_head : (named_envelope_606_37.map Internal.SnakyRows012A.namedCellKey).head? = some (643 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_37_last : (named_envelope_606_37.map Internal.SnakyRows012A.namedCellKey).getLast? = some (651 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_35 : List Cell := Internal.SnakyRows012A.named_envelope_606_36 ++ Internal.SnakyRows012A.named_envelope_606_37
theorem Internal.SnakyRows012A.named_envelope_606_35_chain : (named_envelope_606_35.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_36 Internal.SnakyRows012A.named_envelope_606_37 (642 : ℤ) (643 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_36_chain Internal.SnakyRows012A.named_envelope_606_37_chain Internal.SnakyRows012A.named_envelope_606_36_last Internal.SnakyRows012A.named_envelope_606_37_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_35_head : (named_envelope_606_35.map Internal.SnakyRows012A.namedCellKey).head? = some (524 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_36 Internal.SnakyRows012A.named_envelope_606_37 (524 : ℤ) Internal.SnakyRows012A.named_envelope_606_36_head
theorem Internal.SnakyRows012A.named_envelope_606_35_last : (named_envelope_606_35.map Internal.SnakyRows012A.namedCellKey).getLast? = some (651 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_36 Internal.SnakyRows012A.named_envelope_606_37 (651 : ℤ) Internal.SnakyRows012A.named_envelope_606_37_last
def Internal.SnakyRows012A.named_envelope_606_39 : List Cell := ([(5, 12), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_39_chain : (named_envelope_606_39.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_39_head : (named_envelope_606_39.map Internal.SnakyRows012A.namedCellKey).head? = some (652 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_39_last : (named_envelope_606_39.map Internal.SnakyRows012A.namedCellKey).getLast? = some (769 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_40 : List Cell := ([(6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_40_chain : (named_envelope_606_40.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_40_head : (named_envelope_606_40.map Internal.SnakyRows012A.namedCellKey).head? = some (770 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_40_last : (named_envelope_606_40.map Internal.SnakyRows012A.namedCellKey).getLast? = some (779 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_38 : List Cell := Internal.SnakyRows012A.named_envelope_606_39 ++ Internal.SnakyRows012A.named_envelope_606_40
theorem Internal.SnakyRows012A.named_envelope_606_38_chain : (named_envelope_606_38.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_39 Internal.SnakyRows012A.named_envelope_606_40 (769 : ℤ) (770 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_39_chain Internal.SnakyRows012A.named_envelope_606_40_chain Internal.SnakyRows012A.named_envelope_606_39_last Internal.SnakyRows012A.named_envelope_606_40_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_38_head : (named_envelope_606_38.map Internal.SnakyRows012A.namedCellKey).head? = some (652 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_39 Internal.SnakyRows012A.named_envelope_606_40 (652 : ℤ) Internal.SnakyRows012A.named_envelope_606_39_head
theorem Internal.SnakyRows012A.named_envelope_606_38_last : (named_envelope_606_38.map Internal.SnakyRows012A.namedCellKey).getLast? = some (779 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_39 Internal.SnakyRows012A.named_envelope_606_40 (779 : ℤ) Internal.SnakyRows012A.named_envelope_606_40_last
def Internal.SnakyRows012A.named_envelope_606_34 : List Cell := Internal.SnakyRows012A.named_envelope_606_35 ++ Internal.SnakyRows012A.named_envelope_606_38
theorem Internal.SnakyRows012A.named_envelope_606_34_chain : (named_envelope_606_34.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_35 Internal.SnakyRows012A.named_envelope_606_38 (651 : ℤ) (652 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_35_chain Internal.SnakyRows012A.named_envelope_606_38_chain Internal.SnakyRows012A.named_envelope_606_35_last Internal.SnakyRows012A.named_envelope_606_38_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_34_head : (named_envelope_606_34.map Internal.SnakyRows012A.namedCellKey).head? = some (524 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_35 Internal.SnakyRows012A.named_envelope_606_38 (524 : ℤ) Internal.SnakyRows012A.named_envelope_606_35_head
theorem Internal.SnakyRows012A.named_envelope_606_34_last : (named_envelope_606_34.map Internal.SnakyRows012A.namedCellKey).getLast? = some (779 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_35 Internal.SnakyRows012A.named_envelope_606_38 (779 : ℤ) Internal.SnakyRows012A.named_envelope_606_38_last
def Internal.SnakyRows012A.named_envelope_606_43 : List Cell := ([(6, 12), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_43_chain : (named_envelope_606_43.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_43_head : (named_envelope_606_43.map Internal.SnakyRows012A.namedCellKey).head? = some (780 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_43_last : (named_envelope_606_43.map Internal.SnakyRows012A.namedCellKey).getLast? = some (899 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_44 : List Cell := ([(7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -6), (8, -5)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_44_chain : (named_envelope_606_44.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_44_head : (named_envelope_606_44.map Internal.SnakyRows012A.namedCellKey).head? = some (900 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_44_last : (named_envelope_606_44.map Internal.SnakyRows012A.namedCellKey).getLast? = some (1019 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_42 : List Cell := Internal.SnakyRows012A.named_envelope_606_43 ++ Internal.SnakyRows012A.named_envelope_606_44
theorem Internal.SnakyRows012A.named_envelope_606_42_chain : (named_envelope_606_42.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_43 Internal.SnakyRows012A.named_envelope_606_44 (899 : ℤ) (900 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_43_chain Internal.SnakyRows012A.named_envelope_606_44_chain Internal.SnakyRows012A.named_envelope_606_43_last Internal.SnakyRows012A.named_envelope_606_44_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_42_head : (named_envelope_606_42.map Internal.SnakyRows012A.namedCellKey).head? = some (780 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_43 Internal.SnakyRows012A.named_envelope_606_44 (780 : ℤ) Internal.SnakyRows012A.named_envelope_606_43_head
theorem Internal.SnakyRows012A.named_envelope_606_42_last : (named_envelope_606_42.map Internal.SnakyRows012A.namedCellKey).getLast? = some (1019 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_43 Internal.SnakyRows012A.named_envelope_606_44 (1019 : ℤ) Internal.SnakyRows012A.named_envelope_606_44_last
def Internal.SnakyRows012A.named_envelope_606_46 : List Cell := ([(8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_46_chain : (named_envelope_606_46.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_46_head : (named_envelope_606_46.map Internal.SnakyRows012A.namedCellKey).head? = some (1020 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_46_last : (named_envelope_606_46.map Internal.SnakyRows012A.namedCellKey).getLast? = some (1028 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_47 : List Cell := ([(8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, -6), (9, -5), (9, -4), (9, -3)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_47_chain : (named_envelope_606_47.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_47_head : (named_envelope_606_47.map Internal.SnakyRows012A.namedCellKey).head? = some (1029 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_47_last : (named_envelope_606_47.map Internal.SnakyRows012A.namedCellKey).getLast? = some (1149 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_45 : List Cell := Internal.SnakyRows012A.named_envelope_606_46 ++ Internal.SnakyRows012A.named_envelope_606_47
theorem Internal.SnakyRows012A.named_envelope_606_45_chain : (named_envelope_606_45.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_46 Internal.SnakyRows012A.named_envelope_606_47 (1028 : ℤ) (1029 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_46_chain Internal.SnakyRows012A.named_envelope_606_47_chain Internal.SnakyRows012A.named_envelope_606_46_last Internal.SnakyRows012A.named_envelope_606_47_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_45_head : (named_envelope_606_45.map Internal.SnakyRows012A.namedCellKey).head? = some (1020 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_46 Internal.SnakyRows012A.named_envelope_606_47 (1020 : ℤ) Internal.SnakyRows012A.named_envelope_606_46_head
theorem Internal.SnakyRows012A.named_envelope_606_45_last : (named_envelope_606_45.map Internal.SnakyRows012A.namedCellKey).getLast? = some (1149 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_46 Internal.SnakyRows012A.named_envelope_606_47 (1149 : ℤ) Internal.SnakyRows012A.named_envelope_606_47_last
def Internal.SnakyRows012A.named_envelope_606_41 : List Cell := Internal.SnakyRows012A.named_envelope_606_42 ++ Internal.SnakyRows012A.named_envelope_606_45
theorem Internal.SnakyRows012A.named_envelope_606_41_chain : (named_envelope_606_41.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_42 Internal.SnakyRows012A.named_envelope_606_45 (1019 : ℤ) (1020 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_42_chain Internal.SnakyRows012A.named_envelope_606_45_chain Internal.SnakyRows012A.named_envelope_606_42_last Internal.SnakyRows012A.named_envelope_606_45_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_41_head : (named_envelope_606_41.map Internal.SnakyRows012A.namedCellKey).head? = some (780 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_42 Internal.SnakyRows012A.named_envelope_606_45 (780 : ℤ) Internal.SnakyRows012A.named_envelope_606_42_head
theorem Internal.SnakyRows012A.named_envelope_606_41_last : (named_envelope_606_41.map Internal.SnakyRows012A.namedCellKey).getLast? = some (1149 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_42 Internal.SnakyRows012A.named_envelope_606_45 (1149 : ℤ) Internal.SnakyRows012A.named_envelope_606_45_last
def Internal.SnakyRows012A.named_envelope_606_33 : List Cell := Internal.SnakyRows012A.named_envelope_606_34 ++ Internal.SnakyRows012A.named_envelope_606_41
theorem Internal.SnakyRows012A.named_envelope_606_33_chain : (named_envelope_606_33.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_34 Internal.SnakyRows012A.named_envelope_606_41 (779 : ℤ) (780 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_34_chain Internal.SnakyRows012A.named_envelope_606_41_chain Internal.SnakyRows012A.named_envelope_606_34_last Internal.SnakyRows012A.named_envelope_606_41_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_33_head : (named_envelope_606_33.map Internal.SnakyRows012A.namedCellKey).head? = some (524 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_34 Internal.SnakyRows012A.named_envelope_606_41 (524 : ℤ) Internal.SnakyRows012A.named_envelope_606_34_head
theorem Internal.SnakyRows012A.named_envelope_606_33_last : (named_envelope_606_33.map Internal.SnakyRows012A.namedCellKey).getLast? = some (1149 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_34 Internal.SnakyRows012A.named_envelope_606_41 (1149 : ℤ) Internal.SnakyRows012A.named_envelope_606_41_last
def Internal.SnakyRows012A.named_envelope_606_51 : List Cell := ([(9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_51_chain : (named_envelope_606_51.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_51_head : (named_envelope_606_51.map Internal.SnakyRows012A.namedCellKey).head? = some (1150 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_51_last : (named_envelope_606_51.map Internal.SnakyRows012A.namedCellKey).getLast? = some (1158 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_52 : List Cell := ([(9, 7), (9, 8), (9, 9), (9, 10), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_52_chain : (named_envelope_606_52.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_52_head : (named_envelope_606_52.map Internal.SnakyRows012A.namedCellKey).head? = some (1159 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_52_last : (named_envelope_606_52.map Internal.SnakyRows012A.namedCellKey).getLast? = some (1279 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_50 : List Cell := Internal.SnakyRows012A.named_envelope_606_51 ++ Internal.SnakyRows012A.named_envelope_606_52
theorem Internal.SnakyRows012A.named_envelope_606_50_chain : (named_envelope_606_50.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_51 Internal.SnakyRows012A.named_envelope_606_52 (1158 : ℤ) (1159 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_51_chain Internal.SnakyRows012A.named_envelope_606_52_chain Internal.SnakyRows012A.named_envelope_606_51_last Internal.SnakyRows012A.named_envelope_606_52_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_50_head : (named_envelope_606_50.map Internal.SnakyRows012A.namedCellKey).head? = some (1150 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_51 Internal.SnakyRows012A.named_envelope_606_52 (1150 : ℤ) Internal.SnakyRows012A.named_envelope_606_51_head
theorem Internal.SnakyRows012A.named_envelope_606_50_last : (named_envelope_606_50.map Internal.SnakyRows012A.namedCellKey).getLast? = some (1279 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_51 Internal.SnakyRows012A.named_envelope_606_52 (1279 : ℤ) Internal.SnakyRows012A.named_envelope_606_52_last
def Internal.SnakyRows012A.named_envelope_606_54 : List Cell := ([(10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_54_chain : (named_envelope_606_54.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_54_head : (named_envelope_606_54.map Internal.SnakyRows012A.namedCellKey).head? = some (1280 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_54_last : (named_envelope_606_54.map Internal.SnakyRows012A.namedCellKey).getLast? = some (1288 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_55 : List Cell := ([(11, -6), (11, -5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_55_chain : (named_envelope_606_55.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_55_head : (named_envelope_606_55.map Internal.SnakyRows012A.namedCellKey).head? = some (1402 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_55_last : (named_envelope_606_55.map Internal.SnakyRows012A.namedCellKey).getLast? = some (1411 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_53 : List Cell := Internal.SnakyRows012A.named_envelope_606_54 ++ Internal.SnakyRows012A.named_envelope_606_55
theorem Internal.SnakyRows012A.named_envelope_606_53_chain : (named_envelope_606_53.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_54 Internal.SnakyRows012A.named_envelope_606_55 (1288 : ℤ) (1402 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_54_chain Internal.SnakyRows012A.named_envelope_606_55_chain Internal.SnakyRows012A.named_envelope_606_54_last Internal.SnakyRows012A.named_envelope_606_55_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_53_head : (named_envelope_606_53.map Internal.SnakyRows012A.namedCellKey).head? = some (1280 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_54 Internal.SnakyRows012A.named_envelope_606_55 (1280 : ℤ) Internal.SnakyRows012A.named_envelope_606_54_head
theorem Internal.SnakyRows012A.named_envelope_606_53_last : (named_envelope_606_53.map Internal.SnakyRows012A.namedCellKey).getLast? = some (1411 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_54 Internal.SnakyRows012A.named_envelope_606_55 (1411 : ℤ) Internal.SnakyRows012A.named_envelope_606_55_last
def Internal.SnakyRows012A.named_envelope_606_49 : List Cell := Internal.SnakyRows012A.named_envelope_606_50 ++ Internal.SnakyRows012A.named_envelope_606_53
theorem Internal.SnakyRows012A.named_envelope_606_49_chain : (named_envelope_606_49.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_50 Internal.SnakyRows012A.named_envelope_606_53 (1279 : ℤ) (1280 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_50_chain Internal.SnakyRows012A.named_envelope_606_53_chain Internal.SnakyRows012A.named_envelope_606_50_last Internal.SnakyRows012A.named_envelope_606_53_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_49_head : (named_envelope_606_49.map Internal.SnakyRows012A.namedCellKey).head? = some (1150 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_50 Internal.SnakyRows012A.named_envelope_606_53 (1150 : ℤ) Internal.SnakyRows012A.named_envelope_606_50_head
theorem Internal.SnakyRows012A.named_envelope_606_49_last : (named_envelope_606_49.map Internal.SnakyRows012A.namedCellKey).getLast? = some (1411 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_50 Internal.SnakyRows012A.named_envelope_606_53 (1411 : ℤ) Internal.SnakyRows012A.named_envelope_606_53_last
def Internal.SnakyRows012A.named_envelope_606_58 : List Cell := ([(11, 4), (11, 5), (11, 6), (11, 7), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_58_chain : (named_envelope_606_58.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_58_head : (named_envelope_606_58.map Internal.SnakyRows012A.namedCellKey).head? = some (1412 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_58_last : (named_envelope_606_58.map Internal.SnakyRows012A.namedCellKey).getLast? = some (1536 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_59 : List Cell := ([(12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (13, -4), (13, -3), (13, -2)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_59_chain : (named_envelope_606_59.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_59_head : (named_envelope_606_59.map Internal.SnakyRows012A.namedCellKey).head? = some (1537 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_59_last : (named_envelope_606_59.map Internal.SnakyRows012A.namedCellKey).getLast? = some (1662 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_57 : List Cell := Internal.SnakyRows012A.named_envelope_606_58 ++ Internal.SnakyRows012A.named_envelope_606_59
theorem Internal.SnakyRows012A.named_envelope_606_57_chain : (named_envelope_606_57.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_58 Internal.SnakyRows012A.named_envelope_606_59 (1536 : ℤ) (1537 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_58_chain Internal.SnakyRows012A.named_envelope_606_59_chain Internal.SnakyRows012A.named_envelope_606_58_last Internal.SnakyRows012A.named_envelope_606_59_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_57_head : (named_envelope_606_57.map Internal.SnakyRows012A.namedCellKey).head? = some (1412 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_58 Internal.SnakyRows012A.named_envelope_606_59 (1412 : ℤ) Internal.SnakyRows012A.named_envelope_606_58_head
theorem Internal.SnakyRows012A.named_envelope_606_57_last : (named_envelope_606_57.map Internal.SnakyRows012A.namedCellKey).getLast? = some (1662 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_58 Internal.SnakyRows012A.named_envelope_606_59 (1662 : ℤ) Internal.SnakyRows012A.named_envelope_606_59_last
def Internal.SnakyRows012A.named_envelope_606_61 : List Cell := ([(13, -1), (13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (14, -4), (14, -2), (14, -1)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_61_chain : (named_envelope_606_61.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_61_head : (named_envelope_606_61.map Internal.SnakyRows012A.namedCellKey).head? = some (1663 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_61_last : (named_envelope_606_61.map Internal.SnakyRows012A.namedCellKey).getLast? = some (1791 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_62 : List Cell := ([(14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (15, -2), (15, -1), (15, 0), (16, -2), (16, 0)] : List Cell)
theorem Internal.SnakyRows012A.named_envelope_606_62_chain : (named_envelope_606_62.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_62_head : (named_envelope_606_62.map Internal.SnakyRows012A.namedCellKey).head? = some (1792 : ℤ) := by decide
theorem Internal.SnakyRows012A.named_envelope_606_62_last : (named_envelope_606_62.map Internal.SnakyRows012A.namedCellKey).getLast? = some (2048 : ℤ) := by decide
def Internal.SnakyRows012A.named_envelope_606_60 : List Cell := Internal.SnakyRows012A.named_envelope_606_61 ++ Internal.SnakyRows012A.named_envelope_606_62
theorem Internal.SnakyRows012A.named_envelope_606_60_chain : (named_envelope_606_60.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_61 Internal.SnakyRows012A.named_envelope_606_62 (1791 : ℤ) (1792 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_61_chain Internal.SnakyRows012A.named_envelope_606_62_chain Internal.SnakyRows012A.named_envelope_606_61_last Internal.SnakyRows012A.named_envelope_606_62_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_60_head : (named_envelope_606_60.map Internal.SnakyRows012A.namedCellKey).head? = some (1663 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_61 Internal.SnakyRows012A.named_envelope_606_62 (1663 : ℤ) Internal.SnakyRows012A.named_envelope_606_61_head
theorem Internal.SnakyRows012A.named_envelope_606_60_last : (named_envelope_606_60.map Internal.SnakyRows012A.namedCellKey).getLast? = some (2048 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_61 Internal.SnakyRows012A.named_envelope_606_62 (2048 : ℤ) Internal.SnakyRows012A.named_envelope_606_62_last
def Internal.SnakyRows012A.named_envelope_606_56 : List Cell := Internal.SnakyRows012A.named_envelope_606_57 ++ Internal.SnakyRows012A.named_envelope_606_60
theorem Internal.SnakyRows012A.named_envelope_606_56_chain : (named_envelope_606_56.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_57 Internal.SnakyRows012A.named_envelope_606_60 (1662 : ℤ) (1663 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_57_chain Internal.SnakyRows012A.named_envelope_606_60_chain Internal.SnakyRows012A.named_envelope_606_57_last Internal.SnakyRows012A.named_envelope_606_60_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_56_head : (named_envelope_606_56.map Internal.SnakyRows012A.namedCellKey).head? = some (1412 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_57 Internal.SnakyRows012A.named_envelope_606_60 (1412 : ℤ) Internal.SnakyRows012A.named_envelope_606_57_head
theorem Internal.SnakyRows012A.named_envelope_606_56_last : (named_envelope_606_56.map Internal.SnakyRows012A.namedCellKey).getLast? = some (2048 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_57 Internal.SnakyRows012A.named_envelope_606_60 (2048 : ℤ) Internal.SnakyRows012A.named_envelope_606_60_last
def Internal.SnakyRows012A.named_envelope_606_48 : List Cell := Internal.SnakyRows012A.named_envelope_606_49 ++ Internal.SnakyRows012A.named_envelope_606_56
theorem Internal.SnakyRows012A.named_envelope_606_48_chain : (named_envelope_606_48.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_49 Internal.SnakyRows012A.named_envelope_606_56 (1411 : ℤ) (1412 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_49_chain Internal.SnakyRows012A.named_envelope_606_56_chain Internal.SnakyRows012A.named_envelope_606_49_last Internal.SnakyRows012A.named_envelope_606_56_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_48_head : (named_envelope_606_48.map Internal.SnakyRows012A.namedCellKey).head? = some (1150 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_49 Internal.SnakyRows012A.named_envelope_606_56 (1150 : ℤ) Internal.SnakyRows012A.named_envelope_606_49_head
theorem Internal.SnakyRows012A.named_envelope_606_48_last : (named_envelope_606_48.map Internal.SnakyRows012A.namedCellKey).getLast? = some (2048 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_49 Internal.SnakyRows012A.named_envelope_606_56 (2048 : ℤ) Internal.SnakyRows012A.named_envelope_606_56_last
def Internal.SnakyRows012A.named_envelope_606_32 : List Cell := Internal.SnakyRows012A.named_envelope_606_33 ++ Internal.SnakyRows012A.named_envelope_606_48
theorem Internal.SnakyRows012A.named_envelope_606_32_chain : (named_envelope_606_32.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_33 Internal.SnakyRows012A.named_envelope_606_48 (1149 : ℤ) (1150 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_33_chain Internal.SnakyRows012A.named_envelope_606_48_chain Internal.SnakyRows012A.named_envelope_606_33_last Internal.SnakyRows012A.named_envelope_606_48_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_32_head : (named_envelope_606_32.map Internal.SnakyRows012A.namedCellKey).head? = some (524 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_33 Internal.SnakyRows012A.named_envelope_606_48 (524 : ℤ) Internal.SnakyRows012A.named_envelope_606_33_head
theorem Internal.SnakyRows012A.named_envelope_606_32_last : (named_envelope_606_32.map Internal.SnakyRows012A.namedCellKey).getLast? = some (2048 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_33 Internal.SnakyRows012A.named_envelope_606_48 (2048 : ℤ) Internal.SnakyRows012A.named_envelope_606_48_last
def Internal.SnakyRows012A.named_envelope_606_0 : List Cell := Internal.SnakyRows012A.named_envelope_606_1 ++ Internal.SnakyRows012A.named_envelope_606_32
theorem Internal.SnakyRows012A.named_envelope_606_0_chain : (named_envelope_606_0.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012A.named_chain_append Internal.SnakyRows012A.named_envelope_606_1 Internal.SnakyRows012A.named_envelope_606_32 (523 : ℤ) (524 : ℤ)
    Internal.SnakyRows012A.named_envelope_606_1_chain Internal.SnakyRows012A.named_envelope_606_32_chain Internal.SnakyRows012A.named_envelope_606_1_last Internal.SnakyRows012A.named_envelope_606_32_head (by decide)
theorem Internal.SnakyRows012A.named_envelope_606_0_head : (named_envelope_606_0.map Internal.SnakyRows012A.namedCellKey).head? = some (-641 : ℤ) :=
  Internal.SnakyRows012A.named_head_append Internal.SnakyRows012A.named_envelope_606_1 Internal.SnakyRows012A.named_envelope_606_32 (-641 : ℤ) Internal.SnakyRows012A.named_envelope_606_1_head
theorem Internal.SnakyRows012A.named_envelope_606_0_last : (named_envelope_606_0.map Internal.SnakyRows012A.namedCellKey).getLast? = some (2048 : ℤ) :=
  Internal.SnakyRows012A.named_last_append Internal.SnakyRows012A.named_envelope_606_1 Internal.SnakyRows012A.named_envelope_606_32 (2048 : ℤ) Internal.SnakyRows012A.named_envelope_606_32_last
theorem Internal.SnakyRows012A.named_envelope_606_nodup : (Internal.SnakyRows012A.named_envelope_606_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows012A.named_nodup_of_chain Internal.SnakyRows012A.named_envelope_606_0 Internal.SnakyRows012A.named_envelope_606_0_chain
def envelope_606 : Finset Cell := ⟨(Internal.SnakyRows012A.named_envelope_606_0 : Multiset Cell), Internal.SnakyRows012A.named_envelope_606_nodup⟩
def childrenC_606 : Fin 4 → Finset Cell := ![(placedSet 1 (0, -1) required_123), (placedSet 0 (0, -1) required_274), (placedSet 0 (2, 0) required_605), (placedSet 1 (0, -1) required_119)]
def childrenD_606 : Fin 4 → Finset Cell := ![(placedSet 1 (0, -1) envelope_123), (placedSet 0 (0, -1) envelope_274), (placedSet 0 (2, 0) envelope_605), (placedSet 1 (0, -1) envelope_119)]
theorem common_sub_606 : commonEnvelope childrenD_606 ⊆ insert (0, 0) required_606 := by decide
theorem child_required_sub_606 : ∀ j, childrenC_606 j ⊆ insert (0, 0) required_606 := by decide
theorem Internal.SnakyRows012A.containment_606_0 :
    placedSet 1 (0, -1) envelope_123 ⊆ envelope_606 := by decide
theorem Internal.SnakyRows012A.containment_606_1 :
    placedSet 0 (0, -1) envelope_274 ⊆ envelope_606 := by decide
theorem Internal.SnakyRows012A.containment_606_2 :
    placedSet 0 (2, 0) envelope_605 ⊆ envelope_606 := by decide +kernel
theorem Internal.SnakyRows012A.containment_606_3 :
    placedSet 1 (0, -1) envelope_119 ⊆ envelope_606 := by decide
theorem child_envelope_sub_606 : ∀ j, childrenD_606 j ⊆ envelope_606 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows012A.containment_606_0
  · exact Internal.SnakyRows012A.containment_606_1
  · exact Internal.SnakyRows012A.containment_606_2
  · exact Internal.SnakyRows012A.containment_606_3
theorem pivot_mem_606 : (0, 0) ∈ envelope_606 := by decide
theorem children_work_606 : ∀ j, Template HasSnaky 30 (childrenC_606 j) (childrenD_606 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_123 1 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_274 0 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_605 0 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_119 1 (0, -1)).mono (by decide)
theorem row_works_606 : Template HasSnaky 31 required_606 envelope_606 := by
  refine compose HasSnaky 30 childrenC_606 childrenD_606 children_work_606 (0, 0)
    required_606 envelope_606 pivot_mem_606 child_required_sub_606 child_envelope_sub_606 ?_
  intro b hb; exact common_sub_606 (mem_commonEnvelope childrenD_606 b hb)
end SnakyConditional

end OAI
