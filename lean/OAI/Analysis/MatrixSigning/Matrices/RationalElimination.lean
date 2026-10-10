import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.NegativeWitness

namespace OAI

section

namespace KS.W17

def trailingMatrix {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) :
    Matrix (Fin n) (Fin n) ℚ := fun i j => M i.succ j.succ

def schurTail {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  fun i j => M i.succ j.succ - M i.succ 0 * M 0 j.succ / M 0 0

theorem trailingMatrix_isSymm {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (hM : M.IsSymm) :
    (trailingMatrix M).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact hM.apply i.succ j.succ

theorem schurTail_isSymm {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (hM : M.IsSymm) :
    (schurTail M).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [schurTail]
  rw [hM.apply i.succ j.succ, hM.apply 0 j.succ, hM.apply 0 i.succ]
  rw [mul_comm (M 0 j.succ) (M 0 i.succ)]

def schurWitnessLift {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (y : Fin n → ℚ) : Fin (n + 1) → ℚ :=
  Fin.cons (-(∑ j, M 0 j.succ * y j) / M 0 0) y

def firstNonzeroOffDiagonal {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) : Option (Fin n) :=
  (List.finRange n).find? (fun j => decide (M 0 j.succ ≠ 0))

theorem firstNonzeroOffDiagonal_some {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (j : Fin n)
    (h : firstNonzeroOffDiagonal M = some j) : M 0 j.succ ≠ 0 := by
  have hj := List.find?_some h
  simpa using hj

theorem firstNonzeroOffDiagonal_none_iff {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) :
    firstNonzeroOffDiagonal M = none ↔ ∀ j : Fin n, M 0 j.succ = 0 := by
  simp [firstNonzeroOffDiagonal, List.find?_eq_none]

def rationalNegativeWitness : (n : ℕ) →
    Matrix (Fin n) (Fin n) ℚ → Option (Fin n → ℚ)
  | 0, _ => none
  | n + 1, M =>
      if M 0 0 < 0 then some (Pi.single 0 1)
      else if M 0 0 = 0 then
        match firstNonzeroOffDiagonal M with
        | some j => some (zeroPivotWitness M 0 j.succ)
        | none => (rationalNegativeWitness n (trailingMatrix M)).map (Fin.cons 0)
      else (rationalNegativeWitness n (schurTail M)).map (schurWitnessLift M)

theorem rationalNegativeWitness_negative_pivot {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (h : M 0 0 < 0) :
    rationalNegativeWitness (n + 1) M = some (Pi.single 0 1) := by
  simp [rationalNegativeWitness, h]

end KS.W17

end

end OAI
