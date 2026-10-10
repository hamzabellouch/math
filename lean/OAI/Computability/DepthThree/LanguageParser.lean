import OAI.Computability.DepthThree.LanguageParameters
import Mathlib.Data.List.GetD

namespace OAI

namespace DepthThreeLowerBound

structure ParsedInput where
  dataSize : ℕ
  ringDegree : ℕ
  coefficientCount : ℕ
  data : Fin dataSize → Bool
  hashSeed : Fin (dataSize + ringDegree - 1) → Bool
  polynomial : Fin ringDegree → Bool
  coefficients : Fin coefficientCount → Fin ringDegree → Bool

def decodeInput (w : List Bool) : ParsedInput where
  dataSize := dataDimension w.length
  ringDegree := hashDimension (dataDimension w.length)
  coefficientCount := independenceOrder (dataDimension w.length)
  data i := w.getD i.val false
  hashSeed i := w.getD (hashOffset (dataDimension w.length) + i.val) false
  polynomial i := w.getD (polynomialOffset (dataDimension w.length) + i.val) false
  coefficients j i :=
    w.getD (coefficientOffset (dataDimension w.length) j.val + i.val) false

def InputFits (w : List Bool) : Prop :=
  0 < dataDimension w.length ∧
    2 ≤ independenceOrder (dataDimension w.length) ∧
      blockLen (dataDimension w.length) ≤ w.length

instance (w : List Bool) : Decidable (InputFits w) := by
  unfold InputFits
  infer_instance

def parseInput (w : List Bool) : Option ParsedInput :=
  if InputFits w then some (decodeInput w) else none

theorem parseInput_of_fits {w : List Bool} (h : InputFits w) :
    parseInput w = some (decodeInput w) := by
  simp only [parseInput, ite_eq_left h]

theorem parseInput_of_not_fits {w : List Bool} (h : ¬InputFits w) :
    parseInput w = none := by
  simp only [parseInput, ite_eq_right h]

theorem parseInput_eq_some_iff (w : List Bool) (q : ParsedInput) :
    parseInput w = some q ↔ InputFits w ∧ decodeInput w = q := by
  by_cases h : InputFits w
  · simp [parseInput, h]
  · simp [parseInput, h]

theorem parseInput_eq_none_iff (w : List Bool) :
    parseInput w = none ↔ ¬InputFits w := by
  by_cases h : InputFits w
  · simp [parseInput, h]
  · simp [parseInput, h]

theorem decodeInput_dataSize (w : List Bool) :
    (decodeInput w).dataSize = dataDimension w.length := rfl

theorem decodeInput_ringDegree (w : List Bool) :
    (decodeInput w).ringDegree = hashDimension (dataDimension w.length) := rfl

theorem decodeInput_coefficientCount (w : List Bool) :
    (decodeInput w).coefficientCount = independenceOrder (dataDimension w.length) := rfl

theorem data_read_lt (w : List Bool) (i : Fin (dataDimension w.length)) :
    i.val < w.length :=
  Nat.lt_of_lt_of_le i.isLt (Nat.div_le_self w.length 5)

theorem hash_read_lt {w : List Bool} (h : InputFits w)
    (i : Fin (dataDimension w.length + hashDimension (dataDimension w.length) - 1)) :
    hashOffset (dataDimension w.length) + i.val < w.length := by
  have hi : hashOffset (dataDimension w.length) + i.val <
      polynomialOffset (dataDimension w.length) :=
    Nat.add_lt_add_left i.isLt _
  exact Nat.lt_of_lt_of_le hi (Nat.le_trans (polynomialOffset_le_coefficientsOffset _)
    (Nat.le_trans (coefficientsOffset_le_blockLen _) h.2.2))

theorem polynomial_read_lt {w : List Bool} (h : InputFits w)
    (i : Fin (hashDimension (dataDimension w.length))) :
    polynomialOffset (dataDimension w.length) + i.val < w.length :=
  Nat.lt_of_lt_of_le (polynomial_index_lt i.isLt)
    (Nat.le_trans (coefficientsOffset_le_blockLen _) h.2.2)

theorem coefficient_read_lt {w : List Bool} (h : InputFits w)
    (j : Fin (independenceOrder (dataDimension w.length)))
    (i : Fin (hashDimension (dataDimension w.length))) :
    coefficientOffset (dataDimension w.length) j.val + i.val < w.length :=
  Nat.lt_of_lt_of_le (coefficient_index_lt j.isLt i.isLt) h.2.2

theorem decoded_ringDegree_pos {w : List Bool} (h : InputFits w) :
    0 < (decodeInput w).ringDegree :=
  hashDimension_pos h.1

theorem decoded_coefficientCount_two_le {w : List Bool} (h : InputFits w) :
    2 ≤ (decodeInput w).coefficientCount :=
  h.2.1

end DepthThreeLowerBound

end OAI
