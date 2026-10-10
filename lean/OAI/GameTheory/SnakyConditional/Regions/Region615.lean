import OAI.GameTheory.SnakyConditional.Model

namespace OAI

namespace SnakyConditional
def Internal.SnakyRows017.namedCellKey (p : Cell) : ℤ := 128 * p.1 + p.2
open Internal.SnakyRows017
theorem Internal.SnakyRows017.named_nodup_of_chain (xs : List Cell)
    (h : (xs.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·)) : (xs : Multiset Cell).Nodup :=
  Multiset.coe_nodup.mpr (List.Nodup.of_map Internal.SnakyRows017.namedCellKey h.pairwise.nodup)
theorem Internal.SnakyRows017.named_chain_append (xs ys : List Cell) (a b : ℤ)
    (hx : (xs.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·))
    (hy : (ys.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·))
    (hlast : (xs.map Internal.SnakyRows017.namedCellKey).getLast? = some a)
    (hhead : (ys.map Internal.SnakyRows017.namedCellKey).head? = some b) (hab : a < b) :
    ((xs ++ ys).map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by
  rw [List.map_append]
  apply hx.append hy
  intro x hx' y hy'
  have hax : a = x := by simpa only [hlast, Option.mem_some] using hx'
  have hby : b = y := by simpa only [hhead, Option.mem_some] using hy'
  subst x
  subst y
  exact hab
theorem Internal.SnakyRows017.named_head_append (xs ys : List Cell) (a : ℤ)
    (h : (xs.map Internal.SnakyRows017.namedCellKey).head? = some a) :
    ((xs ++ ys).map Internal.SnakyRows017.namedCellKey).head? = some a := by
  rw [List.map_append, List.head?_append, h]
  rfl
theorem Internal.SnakyRows017.named_last_append (xs ys : List Cell) (b : ℤ)
    (h : (ys.map Internal.SnakyRows017.namedCellKey).getLast? = some b) :
    ((xs ++ ys).map Internal.SnakyRows017.namedCellKey).getLast? = some b := by
  rw [List.map_append, List.getLast?_append, h]
  rfl
def required_615 : Finset Cell := ⟨(([(1, 0)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows017.named_envelope_615_6 : List Cell := ([(-15, 0), (-15, 2), (-14, 0), (-14, 1), (-14, 2), (-13, -4), (-13, -3), (-13, -2), (-13, -1), (-13, 0)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_6_chain : (named_envelope_615_6.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_6_last : (named_envelope_615_6.map Internal.SnakyRows017.namedCellKey).getLast? = some (-1664 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_7 : List Cell := ([(-13, 1), (-13, 2), (-13, 3), (-13, 4), (-12, -5), (-12, -4), (-12, -3), (-12, -2), (-12, -1), (-12, 0), (-12, 1)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_7_chain : (named_envelope_615_7.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_7_head : (named_envelope_615_7.map Internal.SnakyRows017.namedCellKey).head? = some (-1663 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_7_last : (named_envelope_615_7.map Internal.SnakyRows017.namedCellKey).getLast? = some (-1535 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_5 : List Cell := Internal.SnakyRows017.named_envelope_615_6 ++ Internal.SnakyRows017.named_envelope_615_7
theorem Internal.SnakyRows017.named_envelope_615_5_chain : (named_envelope_615_5.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_6 Internal.SnakyRows017.named_envelope_615_7 (-1664 : ℤ) (-1663 : ℤ)
    Internal.SnakyRows017.named_envelope_615_6_chain Internal.SnakyRows017.named_envelope_615_7_chain Internal.SnakyRows017.named_envelope_615_6_last Internal.SnakyRows017.named_envelope_615_7_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_5_last : (named_envelope_615_5.map Internal.SnakyRows017.namedCellKey).getLast? = some (-1535 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_6 Internal.SnakyRows017.named_envelope_615_7 (-1535 : ℤ) Internal.SnakyRows017.named_envelope_615_7_last
def Internal.SnakyRows017.named_envelope_615_9 : List Cell := ([(-12, 2), (-12, 3), (-12, 4), (-12, 5), (-11, -5), (-11, -4), (-11, -3), (-11, -2), (-11, -1), (-11, 0)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_9_chain : (named_envelope_615_9.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_9_head : (named_envelope_615_9.map Internal.SnakyRows017.namedCellKey).head? = some (-1534 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_9_last : (named_envelope_615_9.map Internal.SnakyRows017.namedCellKey).getLast? = some (-1408 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_10 : List Cell := ([(-11, 1), (-11, 2), (-11, 3), (-11, 4), (-11, 5), (-10, -9), (-10, -8), (-10, -7), (-10, -6), (-10, -5), (-10, -4)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_10_chain : (named_envelope_615_10.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_10_head : (named_envelope_615_10.map Internal.SnakyRows017.namedCellKey).head? = some (-1407 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_10_last : (named_envelope_615_10.map Internal.SnakyRows017.namedCellKey).getLast? = some (-1284 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_8 : List Cell := Internal.SnakyRows017.named_envelope_615_9 ++ Internal.SnakyRows017.named_envelope_615_10
theorem Internal.SnakyRows017.named_envelope_615_8_chain : (named_envelope_615_8.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_9 Internal.SnakyRows017.named_envelope_615_10 (-1408 : ℤ) (-1407 : ℤ)
    Internal.SnakyRows017.named_envelope_615_9_chain Internal.SnakyRows017.named_envelope_615_10_chain Internal.SnakyRows017.named_envelope_615_9_last Internal.SnakyRows017.named_envelope_615_10_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_8_head : (named_envelope_615_8.map Internal.SnakyRows017.namedCellKey).head? = some (-1534 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_9 Internal.SnakyRows017.named_envelope_615_10 (-1534 : ℤ) Internal.SnakyRows017.named_envelope_615_9_head
theorem Internal.SnakyRows017.named_envelope_615_8_last : (named_envelope_615_8.map Internal.SnakyRows017.namedCellKey).getLast? = some (-1284 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_9 Internal.SnakyRows017.named_envelope_615_10 (-1284 : ℤ) Internal.SnakyRows017.named_envelope_615_10_last
def Internal.SnakyRows017.named_envelope_615_4 : List Cell := Internal.SnakyRows017.named_envelope_615_5 ++ Internal.SnakyRows017.named_envelope_615_8
theorem Internal.SnakyRows017.named_envelope_615_4_chain : (named_envelope_615_4.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_5 Internal.SnakyRows017.named_envelope_615_8 (-1535 : ℤ) (-1534 : ℤ)
    Internal.SnakyRows017.named_envelope_615_5_chain Internal.SnakyRows017.named_envelope_615_8_chain Internal.SnakyRows017.named_envelope_615_5_last Internal.SnakyRows017.named_envelope_615_8_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_4_last : (named_envelope_615_4.map Internal.SnakyRows017.namedCellKey).getLast? = some (-1284 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_5 Internal.SnakyRows017.named_envelope_615_8 (-1284 : ℤ) Internal.SnakyRows017.named_envelope_615_8_last
def Internal.SnakyRows017.named_envelope_615_13 : List Cell := ([(-10, -3), (-10, -2), (-10, -1), (-10, 0), (-10, 1), (-10, 2), (-10, 3), (-10, 4), (-10, 5), (-10, 6)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_13_chain : (named_envelope_615_13.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_13_head : (named_envelope_615_13.map Internal.SnakyRows017.namedCellKey).head? = some (-1283 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_13_last : (named_envelope_615_13.map Internal.SnakyRows017.namedCellKey).getLast? = some (-1274 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_14 : List Cell := ([(-10, 7), (-10, 8), (-10, 9), (-9, -9), (-9, -8), (-9, -7), (-9, -6), (-9, -5), (-9, -4), (-9, -3), (-9, -2)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_14_chain : (named_envelope_615_14.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_14_head : (named_envelope_615_14.map Internal.SnakyRows017.namedCellKey).head? = some (-1273 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_14_last : (named_envelope_615_14.map Internal.SnakyRows017.namedCellKey).getLast? = some (-1154 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_12 : List Cell := Internal.SnakyRows017.named_envelope_615_13 ++ Internal.SnakyRows017.named_envelope_615_14
theorem Internal.SnakyRows017.named_envelope_615_12_chain : (named_envelope_615_12.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_13 Internal.SnakyRows017.named_envelope_615_14 (-1274 : ℤ) (-1273 : ℤ)
    Internal.SnakyRows017.named_envelope_615_13_chain Internal.SnakyRows017.named_envelope_615_14_chain Internal.SnakyRows017.named_envelope_615_13_last Internal.SnakyRows017.named_envelope_615_14_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_12_head : (named_envelope_615_12.map Internal.SnakyRows017.namedCellKey).head? = some (-1283 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_13 Internal.SnakyRows017.named_envelope_615_14 (-1283 : ℤ) Internal.SnakyRows017.named_envelope_615_13_head
theorem Internal.SnakyRows017.named_envelope_615_12_last : (named_envelope_615_12.map Internal.SnakyRows017.namedCellKey).getLast? = some (-1154 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_13 Internal.SnakyRows017.named_envelope_615_14 (-1154 : ℤ) Internal.SnakyRows017.named_envelope_615_14_last
def Internal.SnakyRows017.named_envelope_615_16 : List Cell := ([(-9, -1), (-9, 0), (-9, 1), (-9, 2), (-9, 3), (-9, 4), (-9, 5), (-9, 6), (-9, 7), (-9, 8), (-9, 9)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_16_chain : (named_envelope_615_16.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_16_head : (named_envelope_615_16.map Internal.SnakyRows017.namedCellKey).head? = some (-1153 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_16_last : (named_envelope_615_16.map Internal.SnakyRows017.namedCellKey).getLast? = some (-1143 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_17 : List Cell := ([(-8, -10), (-8, -9), (-8, -8), (-8, -7), (-8, -6), (-8, -5), (-8, -4), (-8, -3), (-8, -2), (-8, -1), (-8, 0)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_17_chain : (named_envelope_615_17.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_17_head : (named_envelope_615_17.map Internal.SnakyRows017.namedCellKey).head? = some (-1034 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_17_last : (named_envelope_615_17.map Internal.SnakyRows017.namedCellKey).getLast? = some (-1024 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_15 : List Cell := Internal.SnakyRows017.named_envelope_615_16 ++ Internal.SnakyRows017.named_envelope_615_17
theorem Internal.SnakyRows017.named_envelope_615_15_chain : (named_envelope_615_15.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_16 Internal.SnakyRows017.named_envelope_615_17 (-1143 : ℤ) (-1034 : ℤ)
    Internal.SnakyRows017.named_envelope_615_16_chain Internal.SnakyRows017.named_envelope_615_17_chain Internal.SnakyRows017.named_envelope_615_16_last Internal.SnakyRows017.named_envelope_615_17_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_15_head : (named_envelope_615_15.map Internal.SnakyRows017.namedCellKey).head? = some (-1153 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_16 Internal.SnakyRows017.named_envelope_615_17 (-1153 : ℤ) Internal.SnakyRows017.named_envelope_615_16_head
theorem Internal.SnakyRows017.named_envelope_615_15_last : (named_envelope_615_15.map Internal.SnakyRows017.namedCellKey).getLast? = some (-1024 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_16 Internal.SnakyRows017.named_envelope_615_17 (-1024 : ℤ) Internal.SnakyRows017.named_envelope_615_17_last
def Internal.SnakyRows017.named_envelope_615_11 : List Cell := Internal.SnakyRows017.named_envelope_615_12 ++ Internal.SnakyRows017.named_envelope_615_15
theorem Internal.SnakyRows017.named_envelope_615_11_chain : (named_envelope_615_11.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_12 Internal.SnakyRows017.named_envelope_615_15 (-1154 : ℤ) (-1153 : ℤ)
    Internal.SnakyRows017.named_envelope_615_12_chain Internal.SnakyRows017.named_envelope_615_15_chain Internal.SnakyRows017.named_envelope_615_12_last Internal.SnakyRows017.named_envelope_615_15_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_11_head : (named_envelope_615_11.map Internal.SnakyRows017.namedCellKey).head? = some (-1283 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_12 Internal.SnakyRows017.named_envelope_615_15 (-1283 : ℤ) Internal.SnakyRows017.named_envelope_615_12_head
theorem Internal.SnakyRows017.named_envelope_615_11_last : (named_envelope_615_11.map Internal.SnakyRows017.namedCellKey).getLast? = some (-1024 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_12 Internal.SnakyRows017.named_envelope_615_15 (-1024 : ℤ) Internal.SnakyRows017.named_envelope_615_15_last
def Internal.SnakyRows017.named_envelope_615_3 : List Cell := Internal.SnakyRows017.named_envelope_615_4 ++ Internal.SnakyRows017.named_envelope_615_11
theorem Internal.SnakyRows017.named_envelope_615_3_chain : (named_envelope_615_3.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_4 Internal.SnakyRows017.named_envelope_615_11 (-1284 : ℤ) (-1283 : ℤ)
    Internal.SnakyRows017.named_envelope_615_4_chain Internal.SnakyRows017.named_envelope_615_11_chain Internal.SnakyRows017.named_envelope_615_4_last Internal.SnakyRows017.named_envelope_615_11_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_3_last : (named_envelope_615_3.map Internal.SnakyRows017.namedCellKey).getLast? = some (-1024 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_4 Internal.SnakyRows017.named_envelope_615_11 (-1024 : ℤ) Internal.SnakyRows017.named_envelope_615_11_last
def Internal.SnakyRows017.named_envelope_615_21 : List Cell := ([(-8, 1), (-8, 2), (-8, 3), (-8, 4), (-8, 5), (-8, 6), (-8, 7), (-8, 8), (-8, 9), (-8, 10)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_21_chain : (named_envelope_615_21.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_21_head : (named_envelope_615_21.map Internal.SnakyRows017.namedCellKey).head? = some (-1023 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_21_last : (named_envelope_615_21.map Internal.SnakyRows017.namedCellKey).getLast? = some (-1014 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_22 : List Cell := ([(-7, -11), (-7, -10), (-7, -9), (-7, -8), (-7, -7), (-7, -6), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_22_chain : (named_envelope_615_22.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_22_head : (named_envelope_615_22.map Internal.SnakyRows017.namedCellKey).head? = some (-907 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_22_last : (named_envelope_615_22.map Internal.SnakyRows017.namedCellKey).getLast? = some (-897 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_20 : List Cell := Internal.SnakyRows017.named_envelope_615_21 ++ Internal.SnakyRows017.named_envelope_615_22
theorem Internal.SnakyRows017.named_envelope_615_20_chain : (named_envelope_615_20.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_21 Internal.SnakyRows017.named_envelope_615_22 (-1014 : ℤ) (-907 : ℤ)
    Internal.SnakyRows017.named_envelope_615_21_chain Internal.SnakyRows017.named_envelope_615_22_chain Internal.SnakyRows017.named_envelope_615_21_last Internal.SnakyRows017.named_envelope_615_22_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_20_head : (named_envelope_615_20.map Internal.SnakyRows017.namedCellKey).head? = some (-1023 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_21 Internal.SnakyRows017.named_envelope_615_22 (-1023 : ℤ) Internal.SnakyRows017.named_envelope_615_21_head
theorem Internal.SnakyRows017.named_envelope_615_20_last : (named_envelope_615_20.map Internal.SnakyRows017.namedCellKey).getLast? = some (-897 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_21 Internal.SnakyRows017.named_envelope_615_22 (-897 : ℤ) Internal.SnakyRows017.named_envelope_615_22_last
def Internal.SnakyRows017.named_envelope_615_24 : List Cell := ([(-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-7, 6), (-7, 7), (-7, 8), (-7, 9), (-7, 10)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_24_chain : (named_envelope_615_24.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_24_head : (named_envelope_615_24.map Internal.SnakyRows017.namedCellKey).head? = some (-896 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_24_last : (named_envelope_615_24.map Internal.SnakyRows017.namedCellKey).getLast? = some (-886 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_25 : List Cell := ([(-7, 11), (-6, -11), (-6, -10), (-6, -9), (-6, -8), (-6, -7), (-6, -6), (-6, -5), (-6, -4), (-6, -3), (-6, -2)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_25_chain : (named_envelope_615_25.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_25_head : (named_envelope_615_25.map Internal.SnakyRows017.namedCellKey).head? = some (-885 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_25_last : (named_envelope_615_25.map Internal.SnakyRows017.namedCellKey).getLast? = some (-770 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_23 : List Cell := Internal.SnakyRows017.named_envelope_615_24 ++ Internal.SnakyRows017.named_envelope_615_25
theorem Internal.SnakyRows017.named_envelope_615_23_chain : (named_envelope_615_23.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_24 Internal.SnakyRows017.named_envelope_615_25 (-886 : ℤ) (-885 : ℤ)
    Internal.SnakyRows017.named_envelope_615_24_chain Internal.SnakyRows017.named_envelope_615_25_chain Internal.SnakyRows017.named_envelope_615_24_last Internal.SnakyRows017.named_envelope_615_25_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_23_head : (named_envelope_615_23.map Internal.SnakyRows017.namedCellKey).head? = some (-896 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_24 Internal.SnakyRows017.named_envelope_615_25 (-896 : ℤ) Internal.SnakyRows017.named_envelope_615_24_head
theorem Internal.SnakyRows017.named_envelope_615_23_last : (named_envelope_615_23.map Internal.SnakyRows017.namedCellKey).getLast? = some (-770 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_24 Internal.SnakyRows017.named_envelope_615_25 (-770 : ℤ) Internal.SnakyRows017.named_envelope_615_25_last
def Internal.SnakyRows017.named_envelope_615_19 : List Cell := Internal.SnakyRows017.named_envelope_615_20 ++ Internal.SnakyRows017.named_envelope_615_23
theorem Internal.SnakyRows017.named_envelope_615_19_chain : (named_envelope_615_19.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_20 Internal.SnakyRows017.named_envelope_615_23 (-897 : ℤ) (-896 : ℤ)
    Internal.SnakyRows017.named_envelope_615_20_chain Internal.SnakyRows017.named_envelope_615_23_chain Internal.SnakyRows017.named_envelope_615_20_last Internal.SnakyRows017.named_envelope_615_23_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_19_head : (named_envelope_615_19.map Internal.SnakyRows017.namedCellKey).head? = some (-1023 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_20 Internal.SnakyRows017.named_envelope_615_23 (-1023 : ℤ) Internal.SnakyRows017.named_envelope_615_20_head
theorem Internal.SnakyRows017.named_envelope_615_19_last : (named_envelope_615_19.map Internal.SnakyRows017.namedCellKey).getLast? = some (-770 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_20 Internal.SnakyRows017.named_envelope_615_23 (-770 : ℤ) Internal.SnakyRows017.named_envelope_615_23_last
def Internal.SnakyRows017.named_envelope_615_28 : List Cell := ([(-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-6, 8)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_28_chain : (named_envelope_615_28.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_28_head : (named_envelope_615_28.map Internal.SnakyRows017.namedCellKey).head? = some (-769 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_28_last : (named_envelope_615_28.map Internal.SnakyRows017.namedCellKey).getLast? = some (-760 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_29 : List Cell := ([(-6, 9), (-6, 10), (-6, 11), (-5, -12), (-5, -11), (-5, -10), (-5, -9), (-5, -8), (-5, -7), (-5, -6), (-5, -5)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_29_chain : (named_envelope_615_29.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_29_head : (named_envelope_615_29.map Internal.SnakyRows017.namedCellKey).head? = some (-759 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_29_last : (named_envelope_615_29.map Internal.SnakyRows017.namedCellKey).getLast? = some (-645 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_27 : List Cell := Internal.SnakyRows017.named_envelope_615_28 ++ Internal.SnakyRows017.named_envelope_615_29
theorem Internal.SnakyRows017.named_envelope_615_27_chain : (named_envelope_615_27.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_28 Internal.SnakyRows017.named_envelope_615_29 (-760 : ℤ) (-759 : ℤ)
    Internal.SnakyRows017.named_envelope_615_28_chain Internal.SnakyRows017.named_envelope_615_29_chain Internal.SnakyRows017.named_envelope_615_28_last Internal.SnakyRows017.named_envelope_615_29_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_27_head : (named_envelope_615_27.map Internal.SnakyRows017.namedCellKey).head? = some (-769 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_28 Internal.SnakyRows017.named_envelope_615_29 (-769 : ℤ) Internal.SnakyRows017.named_envelope_615_28_head
theorem Internal.SnakyRows017.named_envelope_615_27_last : (named_envelope_615_27.map Internal.SnakyRows017.namedCellKey).getLast? = some (-645 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_28 Internal.SnakyRows017.named_envelope_615_29 (-645 : ℤ) Internal.SnakyRows017.named_envelope_615_29_last
def Internal.SnakyRows017.named_envelope_615_31 : List Cell := ([(-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_31_chain : (named_envelope_615_31.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_31_head : (named_envelope_615_31.map Internal.SnakyRows017.namedCellKey).head? = some (-644 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_31_last : (named_envelope_615_31.map Internal.SnakyRows017.namedCellKey).getLast? = some (-634 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_32 : List Cell := ([(-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-5, 12), (-4, -14), (-4, -13), (-4, -12), (-4, -11), (-4, -10)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_32_chain : (named_envelope_615_32.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_32_head : (named_envelope_615_32.map Internal.SnakyRows017.namedCellKey).head? = some (-633 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_32_last : (named_envelope_615_32.map Internal.SnakyRows017.namedCellKey).getLast? = some (-522 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_30 : List Cell := Internal.SnakyRows017.named_envelope_615_31 ++ Internal.SnakyRows017.named_envelope_615_32
theorem Internal.SnakyRows017.named_envelope_615_30_chain : (named_envelope_615_30.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_31 Internal.SnakyRows017.named_envelope_615_32 (-634 : ℤ) (-633 : ℤ)
    Internal.SnakyRows017.named_envelope_615_31_chain Internal.SnakyRows017.named_envelope_615_32_chain Internal.SnakyRows017.named_envelope_615_31_last Internal.SnakyRows017.named_envelope_615_32_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_30_head : (named_envelope_615_30.map Internal.SnakyRows017.namedCellKey).head? = some (-644 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_31 Internal.SnakyRows017.named_envelope_615_32 (-644 : ℤ) Internal.SnakyRows017.named_envelope_615_31_head
theorem Internal.SnakyRows017.named_envelope_615_30_last : (named_envelope_615_30.map Internal.SnakyRows017.namedCellKey).getLast? = some (-522 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_31 Internal.SnakyRows017.named_envelope_615_32 (-522 : ℤ) Internal.SnakyRows017.named_envelope_615_32_last
def Internal.SnakyRows017.named_envelope_615_26 : List Cell := Internal.SnakyRows017.named_envelope_615_27 ++ Internal.SnakyRows017.named_envelope_615_30
theorem Internal.SnakyRows017.named_envelope_615_26_chain : (named_envelope_615_26.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_27 Internal.SnakyRows017.named_envelope_615_30 (-645 : ℤ) (-644 : ℤ)
    Internal.SnakyRows017.named_envelope_615_27_chain Internal.SnakyRows017.named_envelope_615_30_chain Internal.SnakyRows017.named_envelope_615_27_last Internal.SnakyRows017.named_envelope_615_30_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_26_head : (named_envelope_615_26.map Internal.SnakyRows017.namedCellKey).head? = some (-769 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_27 Internal.SnakyRows017.named_envelope_615_30 (-769 : ℤ) Internal.SnakyRows017.named_envelope_615_27_head
theorem Internal.SnakyRows017.named_envelope_615_26_last : (named_envelope_615_26.map Internal.SnakyRows017.namedCellKey).getLast? = some (-522 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_27 Internal.SnakyRows017.named_envelope_615_30 (-522 : ℤ) Internal.SnakyRows017.named_envelope_615_30_last
def Internal.SnakyRows017.named_envelope_615_18 : List Cell := Internal.SnakyRows017.named_envelope_615_19 ++ Internal.SnakyRows017.named_envelope_615_26
theorem Internal.SnakyRows017.named_envelope_615_18_chain : (named_envelope_615_18.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_19 Internal.SnakyRows017.named_envelope_615_26 (-770 : ℤ) (-769 : ℤ)
    Internal.SnakyRows017.named_envelope_615_19_chain Internal.SnakyRows017.named_envelope_615_26_chain Internal.SnakyRows017.named_envelope_615_19_last Internal.SnakyRows017.named_envelope_615_26_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_18_head : (named_envelope_615_18.map Internal.SnakyRows017.namedCellKey).head? = some (-1023 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_19 Internal.SnakyRows017.named_envelope_615_26 (-1023 : ℤ) Internal.SnakyRows017.named_envelope_615_19_head
theorem Internal.SnakyRows017.named_envelope_615_18_last : (named_envelope_615_18.map Internal.SnakyRows017.namedCellKey).getLast? = some (-522 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_19 Internal.SnakyRows017.named_envelope_615_26 (-522 : ℤ) Internal.SnakyRows017.named_envelope_615_26_last
def Internal.SnakyRows017.named_envelope_615_2 : List Cell := Internal.SnakyRows017.named_envelope_615_3 ++ Internal.SnakyRows017.named_envelope_615_18
theorem Internal.SnakyRows017.named_envelope_615_2_chain : (named_envelope_615_2.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_3 Internal.SnakyRows017.named_envelope_615_18 (-1024 : ℤ) (-1023 : ℤ)
    Internal.SnakyRows017.named_envelope_615_3_chain Internal.SnakyRows017.named_envelope_615_18_chain Internal.SnakyRows017.named_envelope_615_3_last Internal.SnakyRows017.named_envelope_615_18_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_2_last : (named_envelope_615_2.map Internal.SnakyRows017.namedCellKey).getLast? = some (-522 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_3 Internal.SnakyRows017.named_envelope_615_18 (-522 : ℤ) Internal.SnakyRows017.named_envelope_615_18_last
def Internal.SnakyRows017.named_envelope_615_37 : List Cell := ([(-4, -9), (-4, -8), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_37_chain : (named_envelope_615_37.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_37_head : (named_envelope_615_37.map Internal.SnakyRows017.namedCellKey).head? = some (-521 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_37_last : (named_envelope_615_37.map Internal.SnakyRows017.namedCellKey).getLast? = some (-512 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_38 : List Cell := ([(-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_38_chain : (named_envelope_615_38.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_38_head : (named_envelope_615_38.map Internal.SnakyRows017.namedCellKey).head? = some (-511 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_38_last : (named_envelope_615_38.map Internal.SnakyRows017.namedCellKey).getLast? = some (-501 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_36 : List Cell := Internal.SnakyRows017.named_envelope_615_37 ++ Internal.SnakyRows017.named_envelope_615_38
theorem Internal.SnakyRows017.named_envelope_615_36_chain : (named_envelope_615_36.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_37 Internal.SnakyRows017.named_envelope_615_38 (-512 : ℤ) (-511 : ℤ)
    Internal.SnakyRows017.named_envelope_615_37_chain Internal.SnakyRows017.named_envelope_615_38_chain Internal.SnakyRows017.named_envelope_615_37_last Internal.SnakyRows017.named_envelope_615_38_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_36_head : (named_envelope_615_36.map Internal.SnakyRows017.namedCellKey).head? = some (-521 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_37 Internal.SnakyRows017.named_envelope_615_38 (-521 : ℤ) Internal.SnakyRows017.named_envelope_615_37_head
theorem Internal.SnakyRows017.named_envelope_615_36_last : (named_envelope_615_36.map Internal.SnakyRows017.namedCellKey).getLast? = some (-501 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_37 Internal.SnakyRows017.named_envelope_615_38 (-501 : ℤ) Internal.SnakyRows017.named_envelope_615_38_last
def Internal.SnakyRows017.named_envelope_615_40 : List Cell := ([(-4, 12), (-4, 13), (-4, 14), (-3, -14), (-3, -13), (-3, -12), (-3, -11), (-3, -10), (-3, -9), (-3, -8), (-3, -7)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_40_chain : (named_envelope_615_40.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_40_head : (named_envelope_615_40.map Internal.SnakyRows017.namedCellKey).head? = some (-500 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_40_last : (named_envelope_615_40.map Internal.SnakyRows017.namedCellKey).getLast? = some (-391 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_41 : List Cell := ([(-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_41_chain : (named_envelope_615_41.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_41_head : (named_envelope_615_41.map Internal.SnakyRows017.namedCellKey).head? = some (-390 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_41_last : (named_envelope_615_41.map Internal.SnakyRows017.namedCellKey).getLast? = some (-380 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_39 : List Cell := Internal.SnakyRows017.named_envelope_615_40 ++ Internal.SnakyRows017.named_envelope_615_41
theorem Internal.SnakyRows017.named_envelope_615_39_chain : (named_envelope_615_39.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_40 Internal.SnakyRows017.named_envelope_615_41 (-391 : ℤ) (-390 : ℤ)
    Internal.SnakyRows017.named_envelope_615_40_chain Internal.SnakyRows017.named_envelope_615_41_chain Internal.SnakyRows017.named_envelope_615_40_last Internal.SnakyRows017.named_envelope_615_41_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_39_head : (named_envelope_615_39.map Internal.SnakyRows017.namedCellKey).head? = some (-500 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_40 Internal.SnakyRows017.named_envelope_615_41 (-500 : ℤ) Internal.SnakyRows017.named_envelope_615_40_head
theorem Internal.SnakyRows017.named_envelope_615_39_last : (named_envelope_615_39.map Internal.SnakyRows017.namedCellKey).getLast? = some (-380 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_40 Internal.SnakyRows017.named_envelope_615_41 (-380 : ℤ) Internal.SnakyRows017.named_envelope_615_41_last
def Internal.SnakyRows017.named_envelope_615_35 : List Cell := Internal.SnakyRows017.named_envelope_615_36 ++ Internal.SnakyRows017.named_envelope_615_39
theorem Internal.SnakyRows017.named_envelope_615_35_chain : (named_envelope_615_35.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_36 Internal.SnakyRows017.named_envelope_615_39 (-501 : ℤ) (-500 : ℤ)
    Internal.SnakyRows017.named_envelope_615_36_chain Internal.SnakyRows017.named_envelope_615_39_chain Internal.SnakyRows017.named_envelope_615_36_last Internal.SnakyRows017.named_envelope_615_39_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_35_head : (named_envelope_615_35.map Internal.SnakyRows017.namedCellKey).head? = some (-521 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_36 Internal.SnakyRows017.named_envelope_615_39 (-521 : ℤ) Internal.SnakyRows017.named_envelope_615_36_head
theorem Internal.SnakyRows017.named_envelope_615_35_last : (named_envelope_615_35.map Internal.SnakyRows017.namedCellKey).getLast? = some (-380 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_36 Internal.SnakyRows017.named_envelope_615_39 (-380 : ℤ) Internal.SnakyRows017.named_envelope_615_39_last
def Internal.SnakyRows017.named_envelope_615_44 : List Cell := ([(-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-3, 14)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_44_chain : (named_envelope_615_44.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_44_head : (named_envelope_615_44.map Internal.SnakyRows017.namedCellKey).head? = some (-379 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_44_last : (named_envelope_615_44.map Internal.SnakyRows017.namedCellKey).getLast? = some (-370 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_45 : List Cell := ([(-2, -16), (-2, -15), (-2, -14), (-2, -13), (-2, -12), (-2, -11), (-2, -10), (-2, -9), (-2, -8), (-2, -7), (-2, -6)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_45_chain : (named_envelope_615_45.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_45_head : (named_envelope_615_45.map Internal.SnakyRows017.namedCellKey).head? = some (-272 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_45_last : (named_envelope_615_45.map Internal.SnakyRows017.namedCellKey).getLast? = some (-262 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_43 : List Cell := Internal.SnakyRows017.named_envelope_615_44 ++ Internal.SnakyRows017.named_envelope_615_45
theorem Internal.SnakyRows017.named_envelope_615_43_chain : (named_envelope_615_43.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_44 Internal.SnakyRows017.named_envelope_615_45 (-370 : ℤ) (-272 : ℤ)
    Internal.SnakyRows017.named_envelope_615_44_chain Internal.SnakyRows017.named_envelope_615_45_chain Internal.SnakyRows017.named_envelope_615_44_last Internal.SnakyRows017.named_envelope_615_45_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_43_head : (named_envelope_615_43.map Internal.SnakyRows017.namedCellKey).head? = some (-379 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_44 Internal.SnakyRows017.named_envelope_615_45 (-379 : ℤ) Internal.SnakyRows017.named_envelope_615_44_head
theorem Internal.SnakyRows017.named_envelope_615_43_last : (named_envelope_615_43.map Internal.SnakyRows017.namedCellKey).getLast? = some (-262 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_44 Internal.SnakyRows017.named_envelope_615_45 (-262 : ℤ) Internal.SnakyRows017.named_envelope_615_45_last
def Internal.SnakyRows017.named_envelope_615_47 : List Cell := ([(-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_47_chain : (named_envelope_615_47.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_47_head : (named_envelope_615_47.map Internal.SnakyRows017.namedCellKey).head? = some (-261 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_47_last : (named_envelope_615_47.map Internal.SnakyRows017.namedCellKey).getLast? = some (-251 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_48 : List Cell := ([(-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-2, 15), (-2, 16)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_48_chain : (named_envelope_615_48.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_48_head : (named_envelope_615_48.map Internal.SnakyRows017.namedCellKey).head? = some (-250 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_48_last : (named_envelope_615_48.map Internal.SnakyRows017.namedCellKey).getLast? = some (-240 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_46 : List Cell := Internal.SnakyRows017.named_envelope_615_47 ++ Internal.SnakyRows017.named_envelope_615_48
theorem Internal.SnakyRows017.named_envelope_615_46_chain : (named_envelope_615_46.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_47 Internal.SnakyRows017.named_envelope_615_48 (-251 : ℤ) (-250 : ℤ)
    Internal.SnakyRows017.named_envelope_615_47_chain Internal.SnakyRows017.named_envelope_615_48_chain Internal.SnakyRows017.named_envelope_615_47_last Internal.SnakyRows017.named_envelope_615_48_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_46_head : (named_envelope_615_46.map Internal.SnakyRows017.namedCellKey).head? = some (-261 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_47 Internal.SnakyRows017.named_envelope_615_48 (-261 : ℤ) Internal.SnakyRows017.named_envelope_615_47_head
theorem Internal.SnakyRows017.named_envelope_615_46_last : (named_envelope_615_46.map Internal.SnakyRows017.namedCellKey).getLast? = some (-240 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_47 Internal.SnakyRows017.named_envelope_615_48 (-240 : ℤ) Internal.SnakyRows017.named_envelope_615_48_last
def Internal.SnakyRows017.named_envelope_615_42 : List Cell := Internal.SnakyRows017.named_envelope_615_43 ++ Internal.SnakyRows017.named_envelope_615_46
theorem Internal.SnakyRows017.named_envelope_615_42_chain : (named_envelope_615_42.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_43 Internal.SnakyRows017.named_envelope_615_46 (-262 : ℤ) (-261 : ℤ)
    Internal.SnakyRows017.named_envelope_615_43_chain Internal.SnakyRows017.named_envelope_615_46_chain Internal.SnakyRows017.named_envelope_615_43_last Internal.SnakyRows017.named_envelope_615_46_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_42_head : (named_envelope_615_42.map Internal.SnakyRows017.namedCellKey).head? = some (-379 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_43 Internal.SnakyRows017.named_envelope_615_46 (-379 : ℤ) Internal.SnakyRows017.named_envelope_615_43_head
theorem Internal.SnakyRows017.named_envelope_615_42_last : (named_envelope_615_42.map Internal.SnakyRows017.namedCellKey).getLast? = some (-240 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_43 Internal.SnakyRows017.named_envelope_615_46 (-240 : ℤ) Internal.SnakyRows017.named_envelope_615_46_last
def Internal.SnakyRows017.named_envelope_615_34 : List Cell := Internal.SnakyRows017.named_envelope_615_35 ++ Internal.SnakyRows017.named_envelope_615_42
theorem Internal.SnakyRows017.named_envelope_615_34_chain : (named_envelope_615_34.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_35 Internal.SnakyRows017.named_envelope_615_42 (-380 : ℤ) (-379 : ℤ)
    Internal.SnakyRows017.named_envelope_615_35_chain Internal.SnakyRows017.named_envelope_615_42_chain Internal.SnakyRows017.named_envelope_615_35_last Internal.SnakyRows017.named_envelope_615_42_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_34_head : (named_envelope_615_34.map Internal.SnakyRows017.namedCellKey).head? = some (-521 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_35 Internal.SnakyRows017.named_envelope_615_42 (-521 : ℤ) Internal.SnakyRows017.named_envelope_615_35_head
theorem Internal.SnakyRows017.named_envelope_615_34_last : (named_envelope_615_34.map Internal.SnakyRows017.namedCellKey).getLast? = some (-240 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_35 Internal.SnakyRows017.named_envelope_615_42 (-240 : ℤ) Internal.SnakyRows017.named_envelope_615_42_last
def Internal.SnakyRows017.named_envelope_615_52 : List Cell := ([(-1, -15), (-1, -14), (-1, -13), (-1, -12), (-1, -11), (-1, -10), (-1, -9), (-1, -8), (-1, -7), (-1, -6)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_52_chain : (named_envelope_615_52.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_52_head : (named_envelope_615_52.map Internal.SnakyRows017.namedCellKey).head? = some (-143 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_52_last : (named_envelope_615_52.map Internal.SnakyRows017.namedCellKey).getLast? = some (-134 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_53 : List Cell := ([(-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_53_chain : (named_envelope_615_53.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_53_head : (named_envelope_615_53.map Internal.SnakyRows017.namedCellKey).head? = some (-133 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_53_last : (named_envelope_615_53.map Internal.SnakyRows017.namedCellKey).getLast? = some (-123 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_51 : List Cell := Internal.SnakyRows017.named_envelope_615_52 ++ Internal.SnakyRows017.named_envelope_615_53
theorem Internal.SnakyRows017.named_envelope_615_51_chain : (named_envelope_615_51.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_52 Internal.SnakyRows017.named_envelope_615_53 (-134 : ℤ) (-133 : ℤ)
    Internal.SnakyRows017.named_envelope_615_52_chain Internal.SnakyRows017.named_envelope_615_53_chain Internal.SnakyRows017.named_envelope_615_52_last Internal.SnakyRows017.named_envelope_615_53_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_51_head : (named_envelope_615_51.map Internal.SnakyRows017.namedCellKey).head? = some (-143 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_52 Internal.SnakyRows017.named_envelope_615_53 (-143 : ℤ) Internal.SnakyRows017.named_envelope_615_52_head
theorem Internal.SnakyRows017.named_envelope_615_51_last : (named_envelope_615_51.map Internal.SnakyRows017.namedCellKey).getLast? = some (-123 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_52 Internal.SnakyRows017.named_envelope_615_53 (-123 : ℤ) Internal.SnakyRows017.named_envelope_615_53_last
def Internal.SnakyRows017.named_envelope_615_55 : List Cell := ([(-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (-1, 14), (-1, 15), (0, -16)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_55_chain : (named_envelope_615_55.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_55_head : (named_envelope_615_55.map Internal.SnakyRows017.namedCellKey).head? = some (-122 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_55_last : (named_envelope_615_55.map Internal.SnakyRows017.namedCellKey).getLast? = some (-16 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_56 : List Cell := ([(0, -15), (0, -14), (0, -13), (0, -12), (0, -11), (0, -10), (0, -9), (0, -8), (0, -7), (0, -6), (0, -5)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_56_chain : (named_envelope_615_56.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_56_head : (named_envelope_615_56.map Internal.SnakyRows017.namedCellKey).head? = some (-15 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_56_last : (named_envelope_615_56.map Internal.SnakyRows017.namedCellKey).getLast? = some (-5 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_54 : List Cell := Internal.SnakyRows017.named_envelope_615_55 ++ Internal.SnakyRows017.named_envelope_615_56
theorem Internal.SnakyRows017.named_envelope_615_54_chain : (named_envelope_615_54.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_55 Internal.SnakyRows017.named_envelope_615_56 (-16 : ℤ) (-15 : ℤ)
    Internal.SnakyRows017.named_envelope_615_55_chain Internal.SnakyRows017.named_envelope_615_56_chain Internal.SnakyRows017.named_envelope_615_55_last Internal.SnakyRows017.named_envelope_615_56_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_54_head : (named_envelope_615_54.map Internal.SnakyRows017.namedCellKey).head? = some (-122 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_55 Internal.SnakyRows017.named_envelope_615_56 (-122 : ℤ) Internal.SnakyRows017.named_envelope_615_55_head
theorem Internal.SnakyRows017.named_envelope_615_54_last : (named_envelope_615_54.map Internal.SnakyRows017.namedCellKey).getLast? = some (-5 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_55 Internal.SnakyRows017.named_envelope_615_56 (-5 : ℤ) Internal.SnakyRows017.named_envelope_615_56_last
def Internal.SnakyRows017.named_envelope_615_50 : List Cell := Internal.SnakyRows017.named_envelope_615_51 ++ Internal.SnakyRows017.named_envelope_615_54
theorem Internal.SnakyRows017.named_envelope_615_50_chain : (named_envelope_615_50.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_51 Internal.SnakyRows017.named_envelope_615_54 (-123 : ℤ) (-122 : ℤ)
    Internal.SnakyRows017.named_envelope_615_51_chain Internal.SnakyRows017.named_envelope_615_54_chain Internal.SnakyRows017.named_envelope_615_51_last Internal.SnakyRows017.named_envelope_615_54_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_50_head : (named_envelope_615_50.map Internal.SnakyRows017.namedCellKey).head? = some (-143 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_51 Internal.SnakyRows017.named_envelope_615_54 (-143 : ℤ) Internal.SnakyRows017.named_envelope_615_51_head
theorem Internal.SnakyRows017.named_envelope_615_50_last : (named_envelope_615_50.map Internal.SnakyRows017.namedCellKey).getLast? = some (-5 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_51 Internal.SnakyRows017.named_envelope_615_54 (-5 : ℤ) Internal.SnakyRows017.named_envelope_615_54_last
def Internal.SnakyRows017.named_envelope_615_59 : List Cell := ([(0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_59_chain : (named_envelope_615_59.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_59_head : (named_envelope_615_59.map Internal.SnakyRows017.namedCellKey).head? = some (-4 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_59_last : (named_envelope_615_59.map Internal.SnakyRows017.namedCellKey).getLast? = some (5 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_60 : List Cell := ([(0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (0, 16)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_60_chain : (named_envelope_615_60.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_60_head : (named_envelope_615_60.map Internal.SnakyRows017.namedCellKey).head? = some (6 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_60_last : (named_envelope_615_60.map Internal.SnakyRows017.namedCellKey).getLast? = some (16 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_58 : List Cell := Internal.SnakyRows017.named_envelope_615_59 ++ Internal.SnakyRows017.named_envelope_615_60
theorem Internal.SnakyRows017.named_envelope_615_58_chain : (named_envelope_615_58.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_59 Internal.SnakyRows017.named_envelope_615_60 (5 : ℤ) (6 : ℤ)
    Internal.SnakyRows017.named_envelope_615_59_chain Internal.SnakyRows017.named_envelope_615_60_chain Internal.SnakyRows017.named_envelope_615_59_last Internal.SnakyRows017.named_envelope_615_60_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_58_head : (named_envelope_615_58.map Internal.SnakyRows017.namedCellKey).head? = some (-4 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_59 Internal.SnakyRows017.named_envelope_615_60 (-4 : ℤ) Internal.SnakyRows017.named_envelope_615_59_head
theorem Internal.SnakyRows017.named_envelope_615_58_last : (named_envelope_615_58.map Internal.SnakyRows017.namedCellKey).getLast? = some (16 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_59 Internal.SnakyRows017.named_envelope_615_60 (16 : ℤ) Internal.SnakyRows017.named_envelope_615_60_last
def Internal.SnakyRows017.named_envelope_615_62 : List Cell := ([(1, -15), (1, -14), (1, -13), (1, -12), (1, -11), (1, -10), (1, -9), (1, -8), (1, -7), (1, -6), (1, -5)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_62_chain : (named_envelope_615_62.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_62_head : (named_envelope_615_62.map Internal.SnakyRows017.namedCellKey).head? = some (113 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_62_last : (named_envelope_615_62.map Internal.SnakyRows017.namedCellKey).getLast? = some (123 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_63 : List Cell := ([(1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_63_chain : (named_envelope_615_63.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_63_head : (named_envelope_615_63.map Internal.SnakyRows017.namedCellKey).head? = some (124 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_63_last : (named_envelope_615_63.map Internal.SnakyRows017.namedCellKey).getLast? = some (135 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_61 : List Cell := Internal.SnakyRows017.named_envelope_615_62 ++ Internal.SnakyRows017.named_envelope_615_63
theorem Internal.SnakyRows017.named_envelope_615_61_chain : (named_envelope_615_61.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_62 Internal.SnakyRows017.named_envelope_615_63 (123 : ℤ) (124 : ℤ)
    Internal.SnakyRows017.named_envelope_615_62_chain Internal.SnakyRows017.named_envelope_615_63_chain Internal.SnakyRows017.named_envelope_615_62_last Internal.SnakyRows017.named_envelope_615_63_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_61_head : (named_envelope_615_61.map Internal.SnakyRows017.namedCellKey).head? = some (113 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_62 Internal.SnakyRows017.named_envelope_615_63 (113 : ℤ) Internal.SnakyRows017.named_envelope_615_62_head
theorem Internal.SnakyRows017.named_envelope_615_61_last : (named_envelope_615_61.map Internal.SnakyRows017.namedCellKey).getLast? = some (135 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_62 Internal.SnakyRows017.named_envelope_615_63 (135 : ℤ) Internal.SnakyRows017.named_envelope_615_63_last
def Internal.SnakyRows017.named_envelope_615_57 : List Cell := Internal.SnakyRows017.named_envelope_615_58 ++ Internal.SnakyRows017.named_envelope_615_61
theorem Internal.SnakyRows017.named_envelope_615_57_chain : (named_envelope_615_57.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_58 Internal.SnakyRows017.named_envelope_615_61 (16 : ℤ) (113 : ℤ)
    Internal.SnakyRows017.named_envelope_615_58_chain Internal.SnakyRows017.named_envelope_615_61_chain Internal.SnakyRows017.named_envelope_615_58_last Internal.SnakyRows017.named_envelope_615_61_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_57_head : (named_envelope_615_57.map Internal.SnakyRows017.namedCellKey).head? = some (-4 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_58 Internal.SnakyRows017.named_envelope_615_61 (-4 : ℤ) Internal.SnakyRows017.named_envelope_615_58_head
theorem Internal.SnakyRows017.named_envelope_615_57_last : (named_envelope_615_57.map Internal.SnakyRows017.namedCellKey).getLast? = some (135 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_58 Internal.SnakyRows017.named_envelope_615_61 (135 : ℤ) Internal.SnakyRows017.named_envelope_615_61_last
def Internal.SnakyRows017.named_envelope_615_49 : List Cell := Internal.SnakyRows017.named_envelope_615_50 ++ Internal.SnakyRows017.named_envelope_615_57
theorem Internal.SnakyRows017.named_envelope_615_49_chain : (named_envelope_615_49.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_50 Internal.SnakyRows017.named_envelope_615_57 (-5 : ℤ) (-4 : ℤ)
    Internal.SnakyRows017.named_envelope_615_50_chain Internal.SnakyRows017.named_envelope_615_57_chain Internal.SnakyRows017.named_envelope_615_50_last Internal.SnakyRows017.named_envelope_615_57_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_49_head : (named_envelope_615_49.map Internal.SnakyRows017.namedCellKey).head? = some (-143 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_50 Internal.SnakyRows017.named_envelope_615_57 (-143 : ℤ) Internal.SnakyRows017.named_envelope_615_50_head
theorem Internal.SnakyRows017.named_envelope_615_49_last : (named_envelope_615_49.map Internal.SnakyRows017.namedCellKey).getLast? = some (135 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_50 Internal.SnakyRows017.named_envelope_615_57 (135 : ℤ) Internal.SnakyRows017.named_envelope_615_57_last
def Internal.SnakyRows017.named_envelope_615_33 : List Cell := Internal.SnakyRows017.named_envelope_615_34 ++ Internal.SnakyRows017.named_envelope_615_49
theorem Internal.SnakyRows017.named_envelope_615_33_chain : (named_envelope_615_33.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_34 Internal.SnakyRows017.named_envelope_615_49 (-240 : ℤ) (-143 : ℤ)
    Internal.SnakyRows017.named_envelope_615_34_chain Internal.SnakyRows017.named_envelope_615_49_chain Internal.SnakyRows017.named_envelope_615_34_last Internal.SnakyRows017.named_envelope_615_49_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_33_head : (named_envelope_615_33.map Internal.SnakyRows017.namedCellKey).head? = some (-521 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_34 Internal.SnakyRows017.named_envelope_615_49 (-521 : ℤ) Internal.SnakyRows017.named_envelope_615_34_head
theorem Internal.SnakyRows017.named_envelope_615_33_last : (named_envelope_615_33.map Internal.SnakyRows017.namedCellKey).getLast? = some (135 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_34 Internal.SnakyRows017.named_envelope_615_49 (135 : ℤ) Internal.SnakyRows017.named_envelope_615_49_last
def Internal.SnakyRows017.named_envelope_615_1 : List Cell := Internal.SnakyRows017.named_envelope_615_2 ++ Internal.SnakyRows017.named_envelope_615_33
theorem Internal.SnakyRows017.named_envelope_615_1_chain : (named_envelope_615_1.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_2 Internal.SnakyRows017.named_envelope_615_33 (-522 : ℤ) (-521 : ℤ)
    Internal.SnakyRows017.named_envelope_615_2_chain Internal.SnakyRows017.named_envelope_615_33_chain Internal.SnakyRows017.named_envelope_615_2_last Internal.SnakyRows017.named_envelope_615_33_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_1_last : (named_envelope_615_1.map Internal.SnakyRows017.namedCellKey).getLast? = some (135 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_2 Internal.SnakyRows017.named_envelope_615_33 (135 : ℤ) Internal.SnakyRows017.named_envelope_615_33_last
def Internal.SnakyRows017.named_envelope_615_69 : List Cell := ([(1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (1, 14), (1, 15), (1, 16), (2, -16)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_69_chain : (named_envelope_615_69.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_69_head : (named_envelope_615_69.map Internal.SnakyRows017.namedCellKey).head? = some (136 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_69_last : (named_envelope_615_69.map Internal.SnakyRows017.namedCellKey).getLast? = some (240 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_70 : List Cell := ([(2, -15), (2, -14), (2, -13), (2, -12), (2, -11), (2, -10), (2, -9), (2, -8), (2, -7), (2, -6), (2, -5)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_70_chain : (named_envelope_615_70.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_70_head : (named_envelope_615_70.map Internal.SnakyRows017.namedCellKey).head? = some (241 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_70_last : (named_envelope_615_70.map Internal.SnakyRows017.namedCellKey).getLast? = some (251 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_68 : List Cell := Internal.SnakyRows017.named_envelope_615_69 ++ Internal.SnakyRows017.named_envelope_615_70
theorem Internal.SnakyRows017.named_envelope_615_68_chain : (named_envelope_615_68.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_69 Internal.SnakyRows017.named_envelope_615_70 (240 : ℤ) (241 : ℤ)
    Internal.SnakyRows017.named_envelope_615_69_chain Internal.SnakyRows017.named_envelope_615_70_chain Internal.SnakyRows017.named_envelope_615_69_last Internal.SnakyRows017.named_envelope_615_70_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_68_head : (named_envelope_615_68.map Internal.SnakyRows017.namedCellKey).head? = some (136 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_69 Internal.SnakyRows017.named_envelope_615_70 (136 : ℤ) Internal.SnakyRows017.named_envelope_615_69_head
theorem Internal.SnakyRows017.named_envelope_615_68_last : (named_envelope_615_68.map Internal.SnakyRows017.namedCellKey).getLast? = some (251 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_69 Internal.SnakyRows017.named_envelope_615_70 (251 : ℤ) Internal.SnakyRows017.named_envelope_615_70_last
def Internal.SnakyRows017.named_envelope_615_72 : List Cell := ([(2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_72_chain : (named_envelope_615_72.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_72_head : (named_envelope_615_72.map Internal.SnakyRows017.namedCellKey).head? = some (252 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_72_last : (named_envelope_615_72.map Internal.SnakyRows017.namedCellKey).getLast? = some (261 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_73 : List Cell := ([(2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (2, 15), (2, 16)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_73_chain : (named_envelope_615_73.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_73_head : (named_envelope_615_73.map Internal.SnakyRows017.namedCellKey).head? = some (262 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_73_last : (named_envelope_615_73.map Internal.SnakyRows017.namedCellKey).getLast? = some (272 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_71 : List Cell := Internal.SnakyRows017.named_envelope_615_72 ++ Internal.SnakyRows017.named_envelope_615_73
theorem Internal.SnakyRows017.named_envelope_615_71_chain : (named_envelope_615_71.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_72 Internal.SnakyRows017.named_envelope_615_73 (261 : ℤ) (262 : ℤ)
    Internal.SnakyRows017.named_envelope_615_72_chain Internal.SnakyRows017.named_envelope_615_73_chain Internal.SnakyRows017.named_envelope_615_72_last Internal.SnakyRows017.named_envelope_615_73_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_71_head : (named_envelope_615_71.map Internal.SnakyRows017.namedCellKey).head? = some (252 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_72 Internal.SnakyRows017.named_envelope_615_73 (252 : ℤ) Internal.SnakyRows017.named_envelope_615_72_head
theorem Internal.SnakyRows017.named_envelope_615_71_last : (named_envelope_615_71.map Internal.SnakyRows017.namedCellKey).getLast? = some (272 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_72 Internal.SnakyRows017.named_envelope_615_73 (272 : ℤ) Internal.SnakyRows017.named_envelope_615_73_last
def Internal.SnakyRows017.named_envelope_615_67 : List Cell := Internal.SnakyRows017.named_envelope_615_68 ++ Internal.SnakyRows017.named_envelope_615_71
theorem Internal.SnakyRows017.named_envelope_615_67_chain : (named_envelope_615_67.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_68 Internal.SnakyRows017.named_envelope_615_71 (251 : ℤ) (252 : ℤ)
    Internal.SnakyRows017.named_envelope_615_68_chain Internal.SnakyRows017.named_envelope_615_71_chain Internal.SnakyRows017.named_envelope_615_68_last Internal.SnakyRows017.named_envelope_615_71_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_67_head : (named_envelope_615_67.map Internal.SnakyRows017.namedCellKey).head? = some (136 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_68 Internal.SnakyRows017.named_envelope_615_71 (136 : ℤ) Internal.SnakyRows017.named_envelope_615_68_head
theorem Internal.SnakyRows017.named_envelope_615_67_last : (named_envelope_615_67.map Internal.SnakyRows017.namedCellKey).getLast? = some (272 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_68 Internal.SnakyRows017.named_envelope_615_71 (272 : ℤ) Internal.SnakyRows017.named_envelope_615_71_last
def Internal.SnakyRows017.named_envelope_615_76 : List Cell := ([(3, -14), (3, -13), (3, -12), (3, -11), (3, -10), (3, -9), (3, -8), (3, -7), (3, -6), (3, -5)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_76_chain : (named_envelope_615_76.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_76_head : (named_envelope_615_76.map Internal.SnakyRows017.namedCellKey).head? = some (370 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_76_last : (named_envelope_615_76.map Internal.SnakyRows017.namedCellKey).getLast? = some (379 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_77 : List Cell := ([(3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_77_chain : (named_envelope_615_77.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_77_head : (named_envelope_615_77.map Internal.SnakyRows017.namedCellKey).head? = some (380 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_77_last : (named_envelope_615_77.map Internal.SnakyRows017.namedCellKey).getLast? = some (390 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_75 : List Cell := Internal.SnakyRows017.named_envelope_615_76 ++ Internal.SnakyRows017.named_envelope_615_77
theorem Internal.SnakyRows017.named_envelope_615_75_chain : (named_envelope_615_75.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_76 Internal.SnakyRows017.named_envelope_615_77 (379 : ℤ) (380 : ℤ)
    Internal.SnakyRows017.named_envelope_615_76_chain Internal.SnakyRows017.named_envelope_615_77_chain Internal.SnakyRows017.named_envelope_615_76_last Internal.SnakyRows017.named_envelope_615_77_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_75_head : (named_envelope_615_75.map Internal.SnakyRows017.namedCellKey).head? = some (370 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_76 Internal.SnakyRows017.named_envelope_615_77 (370 : ℤ) Internal.SnakyRows017.named_envelope_615_76_head
theorem Internal.SnakyRows017.named_envelope_615_75_last : (named_envelope_615_75.map Internal.SnakyRows017.namedCellKey).getLast? = some (390 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_76 Internal.SnakyRows017.named_envelope_615_77 (390 : ℤ) Internal.SnakyRows017.named_envelope_615_77_last
def Internal.SnakyRows017.named_envelope_615_79 : List Cell := ([(3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (3, 15), (3, 16), (4, -14)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_79_chain : (named_envelope_615_79.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_79_head : (named_envelope_615_79.map Internal.SnakyRows017.namedCellKey).head? = some (391 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_79_last : (named_envelope_615_79.map Internal.SnakyRows017.namedCellKey).getLast? = some (498 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_80 : List Cell := ([(4, -13), (4, -12), (4, -11), (4, -10), (4, -9), (4, -8), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_80_chain : (named_envelope_615_80.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_80_head : (named_envelope_615_80.map Internal.SnakyRows017.namedCellKey).head? = some (499 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_80_last : (named_envelope_615_80.map Internal.SnakyRows017.namedCellKey).getLast? = some (509 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_78 : List Cell := Internal.SnakyRows017.named_envelope_615_79 ++ Internal.SnakyRows017.named_envelope_615_80
theorem Internal.SnakyRows017.named_envelope_615_78_chain : (named_envelope_615_78.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_79 Internal.SnakyRows017.named_envelope_615_80 (498 : ℤ) (499 : ℤ)
    Internal.SnakyRows017.named_envelope_615_79_chain Internal.SnakyRows017.named_envelope_615_80_chain Internal.SnakyRows017.named_envelope_615_79_last Internal.SnakyRows017.named_envelope_615_80_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_78_head : (named_envelope_615_78.map Internal.SnakyRows017.namedCellKey).head? = some (391 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_79 Internal.SnakyRows017.named_envelope_615_80 (391 : ℤ) Internal.SnakyRows017.named_envelope_615_79_head
theorem Internal.SnakyRows017.named_envelope_615_78_last : (named_envelope_615_78.map Internal.SnakyRows017.namedCellKey).getLast? = some (509 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_79 Internal.SnakyRows017.named_envelope_615_80 (509 : ℤ) Internal.SnakyRows017.named_envelope_615_80_last
def Internal.SnakyRows017.named_envelope_615_74 : List Cell := Internal.SnakyRows017.named_envelope_615_75 ++ Internal.SnakyRows017.named_envelope_615_78
theorem Internal.SnakyRows017.named_envelope_615_74_chain : (named_envelope_615_74.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_75 Internal.SnakyRows017.named_envelope_615_78 (390 : ℤ) (391 : ℤ)
    Internal.SnakyRows017.named_envelope_615_75_chain Internal.SnakyRows017.named_envelope_615_78_chain Internal.SnakyRows017.named_envelope_615_75_last Internal.SnakyRows017.named_envelope_615_78_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_74_head : (named_envelope_615_74.map Internal.SnakyRows017.namedCellKey).head? = some (370 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_75 Internal.SnakyRows017.named_envelope_615_78 (370 : ℤ) Internal.SnakyRows017.named_envelope_615_75_head
theorem Internal.SnakyRows017.named_envelope_615_74_last : (named_envelope_615_74.map Internal.SnakyRows017.namedCellKey).getLast? = some (509 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_75 Internal.SnakyRows017.named_envelope_615_78 (509 : ℤ) Internal.SnakyRows017.named_envelope_615_78_last
def Internal.SnakyRows017.named_envelope_615_66 : List Cell := Internal.SnakyRows017.named_envelope_615_67 ++ Internal.SnakyRows017.named_envelope_615_74
theorem Internal.SnakyRows017.named_envelope_615_66_chain : (named_envelope_615_66.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_67 Internal.SnakyRows017.named_envelope_615_74 (272 : ℤ) (370 : ℤ)
    Internal.SnakyRows017.named_envelope_615_67_chain Internal.SnakyRows017.named_envelope_615_74_chain Internal.SnakyRows017.named_envelope_615_67_last Internal.SnakyRows017.named_envelope_615_74_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_66_head : (named_envelope_615_66.map Internal.SnakyRows017.namedCellKey).head? = some (136 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_67 Internal.SnakyRows017.named_envelope_615_74 (136 : ℤ) Internal.SnakyRows017.named_envelope_615_67_head
theorem Internal.SnakyRows017.named_envelope_615_66_last : (named_envelope_615_66.map Internal.SnakyRows017.namedCellKey).getLast? = some (509 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_67 Internal.SnakyRows017.named_envelope_615_74 (509 : ℤ) Internal.SnakyRows017.named_envelope_615_74_last
def Internal.SnakyRows017.named_envelope_615_84 : List Cell := ([(4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_84_chain : (named_envelope_615_84.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_84_head : (named_envelope_615_84.map Internal.SnakyRows017.namedCellKey).head? = some (510 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_84_last : (named_envelope_615_84.map Internal.SnakyRows017.namedCellKey).getLast? = some (519 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_85 : List Cell := ([(4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (5, -14), (5, -13), (5, -12), (5, -11)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_85_chain : (named_envelope_615_85.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_85_head : (named_envelope_615_85.map Internal.SnakyRows017.namedCellKey).head? = some (520 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_85_last : (named_envelope_615_85.map Internal.SnakyRows017.namedCellKey).getLast? = some (629 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_83 : List Cell := Internal.SnakyRows017.named_envelope_615_84 ++ Internal.SnakyRows017.named_envelope_615_85
theorem Internal.SnakyRows017.named_envelope_615_83_chain : (named_envelope_615_83.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_84 Internal.SnakyRows017.named_envelope_615_85 (519 : ℤ) (520 : ℤ)
    Internal.SnakyRows017.named_envelope_615_84_chain Internal.SnakyRows017.named_envelope_615_85_chain Internal.SnakyRows017.named_envelope_615_84_last Internal.SnakyRows017.named_envelope_615_85_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_83_head : (named_envelope_615_83.map Internal.SnakyRows017.namedCellKey).head? = some (510 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_84 Internal.SnakyRows017.named_envelope_615_85 (510 : ℤ) Internal.SnakyRows017.named_envelope_615_84_head
theorem Internal.SnakyRows017.named_envelope_615_83_last : (named_envelope_615_83.map Internal.SnakyRows017.namedCellKey).getLast? = some (629 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_84 Internal.SnakyRows017.named_envelope_615_85 (629 : ℤ) Internal.SnakyRows017.named_envelope_615_85_last
def Internal.SnakyRows017.named_envelope_615_87 : List Cell := ([(5, -10), (5, -9), (5, -8), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_87_chain : (named_envelope_615_87.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_87_head : (named_envelope_615_87.map Internal.SnakyRows017.namedCellKey).head? = some (630 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_87_last : (named_envelope_615_87.map Internal.SnakyRows017.namedCellKey).getLast? = some (640 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_88 : List Cell := ([(5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_88_chain : (named_envelope_615_88.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_88_head : (named_envelope_615_88.map Internal.SnakyRows017.namedCellKey).head? = some (641 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_88_last : (named_envelope_615_88.map Internal.SnakyRows017.namedCellKey).getLast? = some (651 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_86 : List Cell := Internal.SnakyRows017.named_envelope_615_87 ++ Internal.SnakyRows017.named_envelope_615_88
theorem Internal.SnakyRows017.named_envelope_615_86_chain : (named_envelope_615_86.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_87 Internal.SnakyRows017.named_envelope_615_88 (640 : ℤ) (641 : ℤ)
    Internal.SnakyRows017.named_envelope_615_87_chain Internal.SnakyRows017.named_envelope_615_88_chain Internal.SnakyRows017.named_envelope_615_87_last Internal.SnakyRows017.named_envelope_615_88_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_86_head : (named_envelope_615_86.map Internal.SnakyRows017.namedCellKey).head? = some (630 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_87 Internal.SnakyRows017.named_envelope_615_88 (630 : ℤ) Internal.SnakyRows017.named_envelope_615_87_head
theorem Internal.SnakyRows017.named_envelope_615_86_last : (named_envelope_615_86.map Internal.SnakyRows017.namedCellKey).getLast? = some (651 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_87 Internal.SnakyRows017.named_envelope_615_88 (651 : ℤ) Internal.SnakyRows017.named_envelope_615_88_last
def Internal.SnakyRows017.named_envelope_615_82 : List Cell := Internal.SnakyRows017.named_envelope_615_83 ++ Internal.SnakyRows017.named_envelope_615_86
theorem Internal.SnakyRows017.named_envelope_615_82_chain : (named_envelope_615_82.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_83 Internal.SnakyRows017.named_envelope_615_86 (629 : ℤ) (630 : ℤ)
    Internal.SnakyRows017.named_envelope_615_83_chain Internal.SnakyRows017.named_envelope_615_86_chain Internal.SnakyRows017.named_envelope_615_83_last Internal.SnakyRows017.named_envelope_615_86_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_82_head : (named_envelope_615_82.map Internal.SnakyRows017.namedCellKey).head? = some (510 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_83 Internal.SnakyRows017.named_envelope_615_86 (510 : ℤ) Internal.SnakyRows017.named_envelope_615_83_head
theorem Internal.SnakyRows017.named_envelope_615_82_last : (named_envelope_615_82.map Internal.SnakyRows017.namedCellKey).getLast? = some (651 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_83 Internal.SnakyRows017.named_envelope_615_86 (651 : ℤ) Internal.SnakyRows017.named_envelope_615_86_last
def Internal.SnakyRows017.named_envelope_615_91 : List Cell := ([(5, 12), (5, 13), (5, 14), (6, -14), (6, -13), (6, -12), (6, -11), (6, -10), (6, -9), (6, -8)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_91_chain : (named_envelope_615_91.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_91_head : (named_envelope_615_91.map Internal.SnakyRows017.namedCellKey).head? = some (652 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_91_last : (named_envelope_615_91.map Internal.SnakyRows017.namedCellKey).getLast? = some (760 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_92 : List Cell := ([(6, -7), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_92_chain : (named_envelope_615_92.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_92_head : (named_envelope_615_92.map Internal.SnakyRows017.namedCellKey).head? = some (761 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_92_last : (named_envelope_615_92.map Internal.SnakyRows017.namedCellKey).getLast? = some (771 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_90 : List Cell := Internal.SnakyRows017.named_envelope_615_91 ++ Internal.SnakyRows017.named_envelope_615_92
theorem Internal.SnakyRows017.named_envelope_615_90_chain : (named_envelope_615_90.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_91 Internal.SnakyRows017.named_envelope_615_92 (760 : ℤ) (761 : ℤ)
    Internal.SnakyRows017.named_envelope_615_91_chain Internal.SnakyRows017.named_envelope_615_92_chain Internal.SnakyRows017.named_envelope_615_91_last Internal.SnakyRows017.named_envelope_615_92_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_90_head : (named_envelope_615_90.map Internal.SnakyRows017.namedCellKey).head? = some (652 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_91 Internal.SnakyRows017.named_envelope_615_92 (652 : ℤ) Internal.SnakyRows017.named_envelope_615_91_head
theorem Internal.SnakyRows017.named_envelope_615_90_last : (named_envelope_615_90.map Internal.SnakyRows017.namedCellKey).getLast? = some (771 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_91 Internal.SnakyRows017.named_envelope_615_92 (771 : ℤ) Internal.SnakyRows017.named_envelope_615_92_last
def Internal.SnakyRows017.named_envelope_615_94 : List Cell := ([(6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_94_chain : (named_envelope_615_94.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_94_head : (named_envelope_615_94.map Internal.SnakyRows017.namedCellKey).head? = some (772 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_94_last : (named_envelope_615_94.map Internal.SnakyRows017.namedCellKey).getLast? = some (782 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_95 : List Cell := ([(7, -12), (7, -11), (7, -10), (7, -9), (7, -8), (7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_95_chain : (named_envelope_615_95.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_95_head : (named_envelope_615_95.map Internal.SnakyRows017.namedCellKey).head? = some (884 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_95_last : (named_envelope_615_95.map Internal.SnakyRows017.namedCellKey).getLast? = some (894 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_93 : List Cell := Internal.SnakyRows017.named_envelope_615_94 ++ Internal.SnakyRows017.named_envelope_615_95
theorem Internal.SnakyRows017.named_envelope_615_93_chain : (named_envelope_615_93.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_94 Internal.SnakyRows017.named_envelope_615_95 (782 : ℤ) (884 : ℤ)
    Internal.SnakyRows017.named_envelope_615_94_chain Internal.SnakyRows017.named_envelope_615_95_chain Internal.SnakyRows017.named_envelope_615_94_last Internal.SnakyRows017.named_envelope_615_95_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_93_head : (named_envelope_615_93.map Internal.SnakyRows017.namedCellKey).head? = some (772 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_94 Internal.SnakyRows017.named_envelope_615_95 (772 : ℤ) Internal.SnakyRows017.named_envelope_615_94_head
theorem Internal.SnakyRows017.named_envelope_615_93_last : (named_envelope_615_93.map Internal.SnakyRows017.namedCellKey).getLast? = some (894 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_94 Internal.SnakyRows017.named_envelope_615_95 (894 : ℤ) Internal.SnakyRows017.named_envelope_615_95_last
def Internal.SnakyRows017.named_envelope_615_89 : List Cell := Internal.SnakyRows017.named_envelope_615_90 ++ Internal.SnakyRows017.named_envelope_615_93
theorem Internal.SnakyRows017.named_envelope_615_89_chain : (named_envelope_615_89.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_90 Internal.SnakyRows017.named_envelope_615_93 (771 : ℤ) (772 : ℤ)
    Internal.SnakyRows017.named_envelope_615_90_chain Internal.SnakyRows017.named_envelope_615_93_chain Internal.SnakyRows017.named_envelope_615_90_last Internal.SnakyRows017.named_envelope_615_93_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_89_head : (named_envelope_615_89.map Internal.SnakyRows017.namedCellKey).head? = some (652 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_90 Internal.SnakyRows017.named_envelope_615_93 (652 : ℤ) Internal.SnakyRows017.named_envelope_615_90_head
theorem Internal.SnakyRows017.named_envelope_615_89_last : (named_envelope_615_89.map Internal.SnakyRows017.namedCellKey).getLast? = some (894 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_90 Internal.SnakyRows017.named_envelope_615_93 (894 : ℤ) Internal.SnakyRows017.named_envelope_615_93_last
def Internal.SnakyRows017.named_envelope_615_81 : List Cell := Internal.SnakyRows017.named_envelope_615_82 ++ Internal.SnakyRows017.named_envelope_615_89
theorem Internal.SnakyRows017.named_envelope_615_81_chain : (named_envelope_615_81.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_82 Internal.SnakyRows017.named_envelope_615_89 (651 : ℤ) (652 : ℤ)
    Internal.SnakyRows017.named_envelope_615_82_chain Internal.SnakyRows017.named_envelope_615_89_chain Internal.SnakyRows017.named_envelope_615_82_last Internal.SnakyRows017.named_envelope_615_89_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_81_head : (named_envelope_615_81.map Internal.SnakyRows017.namedCellKey).head? = some (510 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_82 Internal.SnakyRows017.named_envelope_615_89 (510 : ℤ) Internal.SnakyRows017.named_envelope_615_82_head
theorem Internal.SnakyRows017.named_envelope_615_81_last : (named_envelope_615_81.map Internal.SnakyRows017.namedCellKey).getLast? = some (894 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_82 Internal.SnakyRows017.named_envelope_615_89 (894 : ℤ) Internal.SnakyRows017.named_envelope_615_89_last
def Internal.SnakyRows017.named_envelope_615_65 : List Cell := Internal.SnakyRows017.named_envelope_615_66 ++ Internal.SnakyRows017.named_envelope_615_81
theorem Internal.SnakyRows017.named_envelope_615_65_chain : (named_envelope_615_65.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_66 Internal.SnakyRows017.named_envelope_615_81 (509 : ℤ) (510 : ℤ)
    Internal.SnakyRows017.named_envelope_615_66_chain Internal.SnakyRows017.named_envelope_615_81_chain Internal.SnakyRows017.named_envelope_615_66_last Internal.SnakyRows017.named_envelope_615_81_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_65_head : (named_envelope_615_65.map Internal.SnakyRows017.namedCellKey).head? = some (136 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_66 Internal.SnakyRows017.named_envelope_615_81 (136 : ℤ) Internal.SnakyRows017.named_envelope_615_66_head
theorem Internal.SnakyRows017.named_envelope_615_65_last : (named_envelope_615_65.map Internal.SnakyRows017.namedCellKey).getLast? = some (894 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_66 Internal.SnakyRows017.named_envelope_615_81 (894 : ℤ) Internal.SnakyRows017.named_envelope_615_81_last
def Internal.SnakyRows017.named_envelope_615_100 : List Cell := ([(7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_100_chain : (named_envelope_615_100.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_100_head : (named_envelope_615_100.map Internal.SnakyRows017.namedCellKey).head? = some (895 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_100_last : (named_envelope_615_100.map Internal.SnakyRows017.namedCellKey).getLast? = some (904 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_101 : List Cell := ([(7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (8, -12), (8, -11), (8, -10), (8, -9), (8, -8)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_101_chain : (named_envelope_615_101.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_101_head : (named_envelope_615_101.map Internal.SnakyRows017.namedCellKey).head? = some (905 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_101_last : (named_envelope_615_101.map Internal.SnakyRows017.namedCellKey).getLast? = some (1016 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_99 : List Cell := Internal.SnakyRows017.named_envelope_615_100 ++ Internal.SnakyRows017.named_envelope_615_101
theorem Internal.SnakyRows017.named_envelope_615_99_chain : (named_envelope_615_99.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_100 Internal.SnakyRows017.named_envelope_615_101 (904 : ℤ) (905 : ℤ)
    Internal.SnakyRows017.named_envelope_615_100_chain Internal.SnakyRows017.named_envelope_615_101_chain Internal.SnakyRows017.named_envelope_615_100_last Internal.SnakyRows017.named_envelope_615_101_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_99_head : (named_envelope_615_99.map Internal.SnakyRows017.namedCellKey).head? = some (895 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_100 Internal.SnakyRows017.named_envelope_615_101 (895 : ℤ) Internal.SnakyRows017.named_envelope_615_100_head
theorem Internal.SnakyRows017.named_envelope_615_99_last : (named_envelope_615_99.map Internal.SnakyRows017.namedCellKey).getLast? = some (1016 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_100 Internal.SnakyRows017.named_envelope_615_101 (1016 : ℤ) Internal.SnakyRows017.named_envelope_615_101_last
def Internal.SnakyRows017.named_envelope_615_103 : List Cell := ([(8, -7), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_103_chain : (named_envelope_615_103.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_103_head : (named_envelope_615_103.map Internal.SnakyRows017.namedCellKey).head? = some (1017 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_103_last : (named_envelope_615_103.map Internal.SnakyRows017.namedCellKey).getLast? = some (1027 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_104 : List Cell := ([(8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (9, -12), (9, -11)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_104_chain : (named_envelope_615_104.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_104_head : (named_envelope_615_104.map Internal.SnakyRows017.namedCellKey).head? = some (1028 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_104_last : (named_envelope_615_104.map Internal.SnakyRows017.namedCellKey).getLast? = some (1141 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_102 : List Cell := Internal.SnakyRows017.named_envelope_615_103 ++ Internal.SnakyRows017.named_envelope_615_104
theorem Internal.SnakyRows017.named_envelope_615_102_chain : (named_envelope_615_102.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_103 Internal.SnakyRows017.named_envelope_615_104 (1027 : ℤ) (1028 : ℤ)
    Internal.SnakyRows017.named_envelope_615_103_chain Internal.SnakyRows017.named_envelope_615_104_chain Internal.SnakyRows017.named_envelope_615_103_last Internal.SnakyRows017.named_envelope_615_104_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_102_head : (named_envelope_615_102.map Internal.SnakyRows017.namedCellKey).head? = some (1017 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_103 Internal.SnakyRows017.named_envelope_615_104 (1017 : ℤ) Internal.SnakyRows017.named_envelope_615_103_head
theorem Internal.SnakyRows017.named_envelope_615_102_last : (named_envelope_615_102.map Internal.SnakyRows017.namedCellKey).getLast? = some (1141 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_103 Internal.SnakyRows017.named_envelope_615_104 (1141 : ℤ) Internal.SnakyRows017.named_envelope_615_104_last
def Internal.SnakyRows017.named_envelope_615_98 : List Cell := Internal.SnakyRows017.named_envelope_615_99 ++ Internal.SnakyRows017.named_envelope_615_102
theorem Internal.SnakyRows017.named_envelope_615_98_chain : (named_envelope_615_98.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_99 Internal.SnakyRows017.named_envelope_615_102 (1016 : ℤ) (1017 : ℤ)
    Internal.SnakyRows017.named_envelope_615_99_chain Internal.SnakyRows017.named_envelope_615_102_chain Internal.SnakyRows017.named_envelope_615_99_last Internal.SnakyRows017.named_envelope_615_102_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_98_head : (named_envelope_615_98.map Internal.SnakyRows017.namedCellKey).head? = some (895 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_99 Internal.SnakyRows017.named_envelope_615_102 (895 : ℤ) Internal.SnakyRows017.named_envelope_615_99_head
theorem Internal.SnakyRows017.named_envelope_615_98_last : (named_envelope_615_98.map Internal.SnakyRows017.namedCellKey).getLast? = some (1141 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_99 Internal.SnakyRows017.named_envelope_615_102 (1141 : ℤ) Internal.SnakyRows017.named_envelope_615_102_last
def Internal.SnakyRows017.named_envelope_615_107 : List Cell := ([(9, -10), (9, -9), (9, -8), (9, -7), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_107_chain : (named_envelope_615_107.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_107_head : (named_envelope_615_107.map Internal.SnakyRows017.namedCellKey).head? = some (1142 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_107_last : (named_envelope_615_107.map Internal.SnakyRows017.namedCellKey).getLast? = some (1151 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_108 : List Cell := ([(9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_108_chain : (named_envelope_615_108.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_108_head : (named_envelope_615_108.map Internal.SnakyRows017.namedCellKey).head? = some (1152 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_108_last : (named_envelope_615_108.map Internal.SnakyRows017.namedCellKey).getLast? = some (1162 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_106 : List Cell := Internal.SnakyRows017.named_envelope_615_107 ++ Internal.SnakyRows017.named_envelope_615_108
theorem Internal.SnakyRows017.named_envelope_615_106_chain : (named_envelope_615_106.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_107 Internal.SnakyRows017.named_envelope_615_108 (1151 : ℤ) (1152 : ℤ)
    Internal.SnakyRows017.named_envelope_615_107_chain Internal.SnakyRows017.named_envelope_615_108_chain Internal.SnakyRows017.named_envelope_615_107_last Internal.SnakyRows017.named_envelope_615_108_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_106_head : (named_envelope_615_106.map Internal.SnakyRows017.namedCellKey).head? = some (1142 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_107 Internal.SnakyRows017.named_envelope_615_108 (1142 : ℤ) Internal.SnakyRows017.named_envelope_615_107_head
theorem Internal.SnakyRows017.named_envelope_615_106_last : (named_envelope_615_106.map Internal.SnakyRows017.namedCellKey).getLast? = some (1162 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_107 Internal.SnakyRows017.named_envelope_615_108 (1162 : ℤ) Internal.SnakyRows017.named_envelope_615_108_last
def Internal.SnakyRows017.named_envelope_615_110 : List Cell := ([(9, 11), (9, 12), (10, -10), (10, -9), (10, -8), (10, -7), (10, -6), (10, -5), (10, -4), (10, -3), (10, -2)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_110_chain : (named_envelope_615_110.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_110_head : (named_envelope_615_110.map Internal.SnakyRows017.namedCellKey).head? = some (1163 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_110_last : (named_envelope_615_110.map Internal.SnakyRows017.namedCellKey).getLast? = some (1278 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_111 : List Cell := ([(10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_111_chain : (named_envelope_615_111.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_111_head : (named_envelope_615_111.map Internal.SnakyRows017.namedCellKey).head? = some (1279 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_111_last : (named_envelope_615_111.map Internal.SnakyRows017.namedCellKey).getLast? = some (1289 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_109 : List Cell := Internal.SnakyRows017.named_envelope_615_110 ++ Internal.SnakyRows017.named_envelope_615_111
theorem Internal.SnakyRows017.named_envelope_615_109_chain : (named_envelope_615_109.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_110 Internal.SnakyRows017.named_envelope_615_111 (1278 : ℤ) (1279 : ℤ)
    Internal.SnakyRows017.named_envelope_615_110_chain Internal.SnakyRows017.named_envelope_615_111_chain Internal.SnakyRows017.named_envelope_615_110_last Internal.SnakyRows017.named_envelope_615_111_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_109_head : (named_envelope_615_109.map Internal.SnakyRows017.namedCellKey).head? = some (1163 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_110 Internal.SnakyRows017.named_envelope_615_111 (1163 : ℤ) Internal.SnakyRows017.named_envelope_615_110_head
theorem Internal.SnakyRows017.named_envelope_615_109_last : (named_envelope_615_109.map Internal.SnakyRows017.namedCellKey).getLast? = some (1289 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_110 Internal.SnakyRows017.named_envelope_615_111 (1289 : ℤ) Internal.SnakyRows017.named_envelope_615_111_last
def Internal.SnakyRows017.named_envelope_615_105 : List Cell := Internal.SnakyRows017.named_envelope_615_106 ++ Internal.SnakyRows017.named_envelope_615_109
theorem Internal.SnakyRows017.named_envelope_615_105_chain : (named_envelope_615_105.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_106 Internal.SnakyRows017.named_envelope_615_109 (1162 : ℤ) (1163 : ℤ)
    Internal.SnakyRows017.named_envelope_615_106_chain Internal.SnakyRows017.named_envelope_615_109_chain Internal.SnakyRows017.named_envelope_615_106_last Internal.SnakyRows017.named_envelope_615_109_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_105_head : (named_envelope_615_105.map Internal.SnakyRows017.namedCellKey).head? = some (1142 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_106 Internal.SnakyRows017.named_envelope_615_109 (1142 : ℤ) Internal.SnakyRows017.named_envelope_615_106_head
theorem Internal.SnakyRows017.named_envelope_615_105_last : (named_envelope_615_105.map Internal.SnakyRows017.namedCellKey).getLast? = some (1289 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_106 Internal.SnakyRows017.named_envelope_615_109 (1289 : ℤ) Internal.SnakyRows017.named_envelope_615_109_last
def Internal.SnakyRows017.named_envelope_615_97 : List Cell := Internal.SnakyRows017.named_envelope_615_98 ++ Internal.SnakyRows017.named_envelope_615_105
theorem Internal.SnakyRows017.named_envelope_615_97_chain : (named_envelope_615_97.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_98 Internal.SnakyRows017.named_envelope_615_105 (1141 : ℤ) (1142 : ℤ)
    Internal.SnakyRows017.named_envelope_615_98_chain Internal.SnakyRows017.named_envelope_615_105_chain Internal.SnakyRows017.named_envelope_615_98_last Internal.SnakyRows017.named_envelope_615_105_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_97_head : (named_envelope_615_97.map Internal.SnakyRows017.namedCellKey).head? = some (895 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_98 Internal.SnakyRows017.named_envelope_615_105 (895 : ℤ) Internal.SnakyRows017.named_envelope_615_98_head
theorem Internal.SnakyRows017.named_envelope_615_97_last : (named_envelope_615_97.map Internal.SnakyRows017.namedCellKey).getLast? = some (1289 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_98 Internal.SnakyRows017.named_envelope_615_105 (1289 : ℤ) Internal.SnakyRows017.named_envelope_615_105_last
def Internal.SnakyRows017.named_envelope_615_115 : List Cell := ([(10, 10), (10, 11), (10, 12), (11, -9), (11, -8), (11, -7), (11, -6), (11, -5), (11, -4), (11, -3)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_115_chain : (named_envelope_615_115.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_115_head : (named_envelope_615_115.map Internal.SnakyRows017.namedCellKey).head? = some (1290 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_115_last : (named_envelope_615_115.map Internal.SnakyRows017.namedCellKey).getLast? = some (1405 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_116 : List Cell := ([(11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_116_chain : (named_envelope_615_116.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_116_head : (named_envelope_615_116.map Internal.SnakyRows017.namedCellKey).head? = some (1406 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_116_last : (named_envelope_615_116.map Internal.SnakyRows017.namedCellKey).getLast? = some (1416 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_114 : List Cell := Internal.SnakyRows017.named_envelope_615_115 ++ Internal.SnakyRows017.named_envelope_615_116
theorem Internal.SnakyRows017.named_envelope_615_114_chain : (named_envelope_615_114.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_115 Internal.SnakyRows017.named_envelope_615_116 (1405 : ℤ) (1406 : ℤ)
    Internal.SnakyRows017.named_envelope_615_115_chain Internal.SnakyRows017.named_envelope_615_116_chain Internal.SnakyRows017.named_envelope_615_115_last Internal.SnakyRows017.named_envelope_615_116_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_114_head : (named_envelope_615_114.map Internal.SnakyRows017.namedCellKey).head? = some (1290 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_115 Internal.SnakyRows017.named_envelope_615_116 (1290 : ℤ) Internal.SnakyRows017.named_envelope_615_115_head
theorem Internal.SnakyRows017.named_envelope_615_114_last : (named_envelope_615_114.map Internal.SnakyRows017.namedCellKey).getLast? = some (1416 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_115 Internal.SnakyRows017.named_envelope_615_116 (1416 : ℤ) Internal.SnakyRows017.named_envelope_615_116_last
def Internal.SnakyRows017.named_envelope_615_118 : List Cell := ([(11, 9), (11, 10), (12, -9), (12, -8), (12, -7), (12, -6), (12, -5), (12, -4), (12, -3), (12, -2), (12, -1)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_118_chain : (named_envelope_615_118.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_118_head : (named_envelope_615_118.map Internal.SnakyRows017.namedCellKey).head? = some (1417 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_118_last : (named_envelope_615_118.map Internal.SnakyRows017.namedCellKey).getLast? = some (1535 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_119 : List Cell := ([(12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 9), (13, -6)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_119_chain : (named_envelope_615_119.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_119_head : (named_envelope_615_119.map Internal.SnakyRows017.namedCellKey).head? = some (1536 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_119_last : (named_envelope_615_119.map Internal.SnakyRows017.namedCellKey).getLast? = some (1658 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_117 : List Cell := Internal.SnakyRows017.named_envelope_615_118 ++ Internal.SnakyRows017.named_envelope_615_119
theorem Internal.SnakyRows017.named_envelope_615_117_chain : (named_envelope_615_117.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_118 Internal.SnakyRows017.named_envelope_615_119 (1535 : ℤ) (1536 : ℤ)
    Internal.SnakyRows017.named_envelope_615_118_chain Internal.SnakyRows017.named_envelope_615_119_chain Internal.SnakyRows017.named_envelope_615_118_last Internal.SnakyRows017.named_envelope_615_119_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_117_head : (named_envelope_615_117.map Internal.SnakyRows017.namedCellKey).head? = some (1417 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_118 Internal.SnakyRows017.named_envelope_615_119 (1417 : ℤ) Internal.SnakyRows017.named_envelope_615_118_head
theorem Internal.SnakyRows017.named_envelope_615_117_last : (named_envelope_615_117.map Internal.SnakyRows017.namedCellKey).getLast? = some (1658 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_118 Internal.SnakyRows017.named_envelope_615_119 (1658 : ℤ) Internal.SnakyRows017.named_envelope_615_119_last
def Internal.SnakyRows017.named_envelope_615_113 : List Cell := Internal.SnakyRows017.named_envelope_615_114 ++ Internal.SnakyRows017.named_envelope_615_117
theorem Internal.SnakyRows017.named_envelope_615_113_chain : (named_envelope_615_113.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_114 Internal.SnakyRows017.named_envelope_615_117 (1416 : ℤ) (1417 : ℤ)
    Internal.SnakyRows017.named_envelope_615_114_chain Internal.SnakyRows017.named_envelope_615_117_chain Internal.SnakyRows017.named_envelope_615_114_last Internal.SnakyRows017.named_envelope_615_117_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_113_head : (named_envelope_615_113.map Internal.SnakyRows017.namedCellKey).head? = some (1290 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_114 Internal.SnakyRows017.named_envelope_615_117 (1290 : ℤ) Internal.SnakyRows017.named_envelope_615_114_head
theorem Internal.SnakyRows017.named_envelope_615_113_last : (named_envelope_615_113.map Internal.SnakyRows017.namedCellKey).getLast? = some (1658 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_114 Internal.SnakyRows017.named_envelope_615_117 (1658 : ℤ) Internal.SnakyRows017.named_envelope_615_117_last
def Internal.SnakyRows017.named_envelope_615_122 : List Cell := ([(13, -5), (13, -4), (13, -3), (13, -2), (13, -1), (13, 0), (13, 1), (13, 2), (13, 3), (13, 4)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_122_chain : (named_envelope_615_122.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_122_head : (named_envelope_615_122.map Internal.SnakyRows017.namedCellKey).head? = some (1659 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_122_last : (named_envelope_615_122.map Internal.SnakyRows017.namedCellKey).getLast? = some (1668 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_123 : List Cell := ([(13, 5), (13, 6), (13, 7), (13, 8), (13, 9), (14, -6), (14, -5), (14, -4), (14, -3), (14, -2), (14, -1)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_123_chain : (named_envelope_615_123.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_123_head : (named_envelope_615_123.map Internal.SnakyRows017.namedCellKey).head? = some (1669 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_123_last : (named_envelope_615_123.map Internal.SnakyRows017.namedCellKey).getLast? = some (1791 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_121 : List Cell := Internal.SnakyRows017.named_envelope_615_122 ++ Internal.SnakyRows017.named_envelope_615_123
theorem Internal.SnakyRows017.named_envelope_615_121_chain : (named_envelope_615_121.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_122 Internal.SnakyRows017.named_envelope_615_123 (1668 : ℤ) (1669 : ℤ)
    Internal.SnakyRows017.named_envelope_615_122_chain Internal.SnakyRows017.named_envelope_615_123_chain Internal.SnakyRows017.named_envelope_615_122_last Internal.SnakyRows017.named_envelope_615_123_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_121_head : (named_envelope_615_121.map Internal.SnakyRows017.namedCellKey).head? = some (1659 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_122 Internal.SnakyRows017.named_envelope_615_123 (1659 : ℤ) Internal.SnakyRows017.named_envelope_615_122_head
theorem Internal.SnakyRows017.named_envelope_615_121_last : (named_envelope_615_121.map Internal.SnakyRows017.namedCellKey).getLast? = some (1791 : ℤ) :=
  Internal.SnakyRows017.named_last_append Internal.SnakyRows017.named_envelope_615_122 Internal.SnakyRows017.named_envelope_615_123 (1791 : ℤ) Internal.SnakyRows017.named_envelope_615_123_last
def Internal.SnakyRows017.named_envelope_615_125 : List Cell := ([(14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (14, 5), (14, 6), (15, -2), (15, -1), (15, 0), (15, 1)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_125_chain : (named_envelope_615_125.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_125_head : (named_envelope_615_125.map Internal.SnakyRows017.namedCellKey).head? = some (1792 : ℤ) := by decide
theorem Internal.SnakyRows017.named_envelope_615_125_last : (named_envelope_615_125.map Internal.SnakyRows017.namedCellKey).getLast? = some (1921 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_126 : List Cell := ([(15, 2), (15, 3), (15, 4), (15, 5), (15, 6), (16, -2), (16, 0), (16, 1), (16, 2), (17, 0), (17, 2)] : List Cell)
theorem Internal.SnakyRows017.named_envelope_615_126_chain : (named_envelope_615_126.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows017.named_envelope_615_126_head : (named_envelope_615_126.map Internal.SnakyRows017.namedCellKey).head? = some (1922 : ℤ) := by decide
def Internal.SnakyRows017.named_envelope_615_124 : List Cell := Internal.SnakyRows017.named_envelope_615_125 ++ Internal.SnakyRows017.named_envelope_615_126
theorem Internal.SnakyRows017.named_envelope_615_124_chain : (named_envelope_615_124.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_125 Internal.SnakyRows017.named_envelope_615_126 (1921 : ℤ) (1922 : ℤ)
    Internal.SnakyRows017.named_envelope_615_125_chain Internal.SnakyRows017.named_envelope_615_126_chain Internal.SnakyRows017.named_envelope_615_125_last Internal.SnakyRows017.named_envelope_615_126_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_124_head : (named_envelope_615_124.map Internal.SnakyRows017.namedCellKey).head? = some (1792 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_125 Internal.SnakyRows017.named_envelope_615_126 (1792 : ℤ) Internal.SnakyRows017.named_envelope_615_125_head
def Internal.SnakyRows017.named_envelope_615_120 : List Cell := Internal.SnakyRows017.named_envelope_615_121 ++ Internal.SnakyRows017.named_envelope_615_124
theorem Internal.SnakyRows017.named_envelope_615_120_chain : (named_envelope_615_120.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_121 Internal.SnakyRows017.named_envelope_615_124 (1791 : ℤ) (1792 : ℤ)
    Internal.SnakyRows017.named_envelope_615_121_chain Internal.SnakyRows017.named_envelope_615_124_chain Internal.SnakyRows017.named_envelope_615_121_last Internal.SnakyRows017.named_envelope_615_124_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_120_head : (named_envelope_615_120.map Internal.SnakyRows017.namedCellKey).head? = some (1659 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_121 Internal.SnakyRows017.named_envelope_615_124 (1659 : ℤ) Internal.SnakyRows017.named_envelope_615_121_head
def Internal.SnakyRows017.named_envelope_615_112 : List Cell := Internal.SnakyRows017.named_envelope_615_113 ++ Internal.SnakyRows017.named_envelope_615_120
theorem Internal.SnakyRows017.named_envelope_615_112_chain : (named_envelope_615_112.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_113 Internal.SnakyRows017.named_envelope_615_120 (1658 : ℤ) (1659 : ℤ)
    Internal.SnakyRows017.named_envelope_615_113_chain Internal.SnakyRows017.named_envelope_615_120_chain Internal.SnakyRows017.named_envelope_615_113_last Internal.SnakyRows017.named_envelope_615_120_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_112_head : (named_envelope_615_112.map Internal.SnakyRows017.namedCellKey).head? = some (1290 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_113 Internal.SnakyRows017.named_envelope_615_120 (1290 : ℤ) Internal.SnakyRows017.named_envelope_615_113_head
def Internal.SnakyRows017.named_envelope_615_96 : List Cell := Internal.SnakyRows017.named_envelope_615_97 ++ Internal.SnakyRows017.named_envelope_615_112
theorem Internal.SnakyRows017.named_envelope_615_96_chain : (named_envelope_615_96.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_97 Internal.SnakyRows017.named_envelope_615_112 (1289 : ℤ) (1290 : ℤ)
    Internal.SnakyRows017.named_envelope_615_97_chain Internal.SnakyRows017.named_envelope_615_112_chain Internal.SnakyRows017.named_envelope_615_97_last Internal.SnakyRows017.named_envelope_615_112_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_96_head : (named_envelope_615_96.map Internal.SnakyRows017.namedCellKey).head? = some (895 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_97 Internal.SnakyRows017.named_envelope_615_112 (895 : ℤ) Internal.SnakyRows017.named_envelope_615_97_head
def Internal.SnakyRows017.named_envelope_615_64 : List Cell := Internal.SnakyRows017.named_envelope_615_65 ++ Internal.SnakyRows017.named_envelope_615_96
theorem Internal.SnakyRows017.named_envelope_615_64_chain : (named_envelope_615_64.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_65 Internal.SnakyRows017.named_envelope_615_96 (894 : ℤ) (895 : ℤ)
    Internal.SnakyRows017.named_envelope_615_65_chain Internal.SnakyRows017.named_envelope_615_96_chain Internal.SnakyRows017.named_envelope_615_65_last Internal.SnakyRows017.named_envelope_615_96_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_64_head : (named_envelope_615_64.map Internal.SnakyRows017.namedCellKey).head? = some (136 : ℤ) :=
  Internal.SnakyRows017.named_head_append Internal.SnakyRows017.named_envelope_615_65 Internal.SnakyRows017.named_envelope_615_96 (136 : ℤ) Internal.SnakyRows017.named_envelope_615_65_head
def Internal.SnakyRows017.named_envelope_615_0 : List Cell := Internal.SnakyRows017.named_envelope_615_1 ++ Internal.SnakyRows017.named_envelope_615_64
theorem Internal.SnakyRows017.named_envelope_615_0_chain : (named_envelope_615_0.map Internal.SnakyRows017.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows017.named_chain_append Internal.SnakyRows017.named_envelope_615_1 Internal.SnakyRows017.named_envelope_615_64 (135 : ℤ) (136 : ℤ)
    Internal.SnakyRows017.named_envelope_615_1_chain Internal.SnakyRows017.named_envelope_615_64_chain Internal.SnakyRows017.named_envelope_615_1_last Internal.SnakyRows017.named_envelope_615_64_head (by decide)
theorem Internal.SnakyRows017.named_envelope_615_nodup : (Internal.SnakyRows017.named_envelope_615_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows017.named_nodup_of_chain Internal.SnakyRows017.named_envelope_615_0 Internal.SnakyRows017.named_envelope_615_0_chain
def envelope_615 : Finset Cell := ⟨(Internal.SnakyRows017.named_envelope_615_0 : Multiset Cell), Internal.SnakyRows017.named_envelope_615_nodup⟩
end SnakyConditional

end OAI
