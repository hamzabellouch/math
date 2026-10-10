import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Matrix.Basic

namespace OAI

section

namespace InternalCatalan

local instance : Fact (Nat.Prime 101) := ⟨by decide +kernel⟩

def fixedGaussianSwap (A : Matrix (Fin 48) (Fin 48) (ZMod 101))
    (i r : Fin 48) : Matrix (Fin 48) (Fin 48) (ZMod 101) :=
  fun j k => A (if j = i then r else if j = r then i else j) k

def fixedGaussianStep (A : Matrix (Fin 48) (Fin 48) (ZMod 101))
    (i r : Fin 48) : Matrix (Fin 48) (Fin 48) (ZMod 101) :=
  let B := fixedGaussianSwap A i r
  fun j k => if i < j then B j k - (B j i / B i i) * B i k else B j k

def fixedGaussianPivot (A : Matrix (Fin 48) (Fin 48) (ZMod 101))
    (i r : Fin 48) (d : ZMod 101) : Prop :=
  i ≤ r ∧ A r i ≠ 0 ∧ (∀ j : Fin 48, i ≤ j → j < r → A j i = 0) ∧ A r i = d

theorem fixedGaussianPivot_unique {A : Matrix (Fin 48) (Fin 48) (ZMod 101)}
    {i r s : Fin 48} {d e : ZMod 101}
    (hr : fixedGaussianPivot A i r d) (hs : fixedGaussianPivot A i s e) : r = s := by
  rcases lt_trichotomy r s with h | h | h
  · exact False.elim (hr.2.1 (hs.2.2.1 r hr.1 h))
  · exact h
  · exact False.elim (hs.2.1 (hr.2.2.1 s hs.1 h))

theorem fixedGaussianStep_pivot_row (A : Matrix (Fin 48) (Fin 48) (ZMod 101))
    (i r k : Fin 48) : fixedGaussianStep A i r i k = A r k := by
  simp [fixedGaussianStep, fixedGaussianSwap]

def fixedGaussianTrace (A : Matrix (Fin 48) (Fin 48) (ZMod 101))
    (states : Fin 49 → Matrix (Fin 48) (Fin 48) (ZMod 101))
    (rows : Fin 48 → Fin 48) (pivots : Fin 48 → ZMod 101) : Prop :=
  states 0 = A ∧ ∀ i : Fin 48,
    fixedGaussianPivot (states i.castSucc) i (rows i) (pivots i) ∧
      states i.succ = fixedGaussianStep (states i.castSucc) i (rows i)

end InternalCatalan

end

section

namespace InternalCatalan

def fixedGaussianZeroPivots (i : Fin 48) : ZMod 101 :=
  match i.val with
  | 0 => 60
  | 1 => 68
  | 2 => 62
  | 3 => 79
  | 4 => 47
  | 5 => 32
  | 6 => 69
  | 7 => 57
  | 8 => 30
  | 9 => 72
  | 10 => 35
  | 11 => 66
  | 12 => 43
  | 13 => 20
  | 14 => 85
  | 15 => 48
  | 16 => 88
  | 17 => 4
  | 18 => 77
  | 19 => 54
  | 20 => 60
  | 21 => 79
  | 22 => 26
  | 23 => 68
  | 24 => 83
  | 25 => 39
  | 26 => 40
  | 27 => 65
  | 28 => 1
  | 29 => 68
  | 30 => 78
  | 31 => 24
  | 32 => 15
  | 33 => 98
  | 34 => 32
  | 35 => 22
  | 36 => 94
  | 37 => 9
  | 38 => 99
  | 39 => 10
  | 40 => 15
  | 41 => 75
  | 42 => 4
  | 43 => 2
  | 44 => 25
  | 45 => 53
  | 46 => 90
  | 47 => 79
  | _ => 0

def fixedGaussianZeroRows (i : Fin 48) : Fin 48 :=
  i

theorem fixedGaussianZeroPivots_nonzero :
    ∀ i : Fin 48, fixedGaussianZeroPivots i ≠ 0 := by
  decide +kernel

def fixedGaussianPlusPivots (i : Fin 48) : ZMod 101 :=
  match i.val with
  | 0 => 38
  | 1 => 51
  | 2 => 90
  | 3 => 70
  | 4 => 5
  | 5 => 21
  | 6 => 88
  | 7 => 55
  | 8 => 45
  | 9 => 20
  | 10 => 35
  | 11 => 41
  | 12 => 77
  | 13 => 10
  | 14 => 18
  | 15 => 25
  | 16 => 76
  | 17 => 14
  | 18 => 38
  | 19 => 72
  | 20 => 6
  | 21 => 66
  | 22 => 56
  | 23 => 35
  | 24 => 83
  | 25 => 58
  | 26 => 56
  | 27 => 11
  | 28 => 17
  | 29 => 20
  | 30 => 30
  | 31 => 24
  | 32 => 28
  | 33 => 11
  | 34 => 25
  | 35 => 70
  | 36 => 79
  | 37 => 99
  | 38 => 66
  | 39 => 38
  | 40 => 4
  | 41 => 41
  | 42 => 63
  | 43 => 91
  | 44 => 63
  | 45 => 17
  | 46 => 90
  | 47 => 98
  | _ => 0

def fixedGaussianPlusRows (i : Fin 48) : Fin 48 :=
  if i = 30 then 31 else if i = 45 then 46 else i

theorem fixedGaussianPlusPivots_nonzero :
    ∀ i : Fin 48, fixedGaussianPlusPivots i ≠ 0 := by
  decide +kernel

def fixedGaussianMinusPivots (i : Fin 48) : ZMod 101 :=
  match i.val with
  | 0 => 82
  | 1 => 92
  | 2 => 26
  | 3 => 87
  | 4 => 21
  | 5 => 74
  | 6 => 87
  | 7 => 88
  | 8 => 88
  | 9 => 3
  | 10 => 14
  | 11 => 23
  | 12 => 38
  | 13 => 58
  | 14 => 36
  | 15 => 20
  | 16 => 26
  | 17 => 33
  | 18 => 94
  | 19 => 74
  | 20 => 78
  | 21 => 45
  | 22 => 93
  | 23 => 86
  | 24 => 73
  | 25 => 66
  | 26 => 45
  | 27 => 30
  | 28 => 61
  | 29 => 3
  | 30 => 88
  | 31 => 27
  | 32 => 20
  | 33 => 58
  | 34 => 69
  | 35 => 48
  | 36 => 78
  | 37 => 39
  | 38 => 48
  | 39 => 1
  | 40 => 66
  | 41 => 18
  | 42 => 86
  | 43 => 93
  | 44 => 52
  | 45 => 92
  | 46 => 39
  | 47 => 77
  | _ => 0

def fixedGaussianMinusRows (i : Fin 48) : Fin 48 :=
  i

theorem fixedGaussianMinusPivots_nonzero :
    ∀ i : Fin 48, fixedGaussianMinusPivots i ≠ 0 := by
  decide +kernel

theorem fixedGaussianPlusRows_swaps :
    ∀ i : Fin 48, fixedGaussianPlusRows i ≠ i ↔ i = 30 ∨ i = 45 := by
  decide +kernel

end InternalCatalan

end

end OAI
