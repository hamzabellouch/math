import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.RationalElimination

namespace OAI

section

namespace KS.W17

@[simp] theorem schurTail_zero_pivot {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (h : M 0 0 = 0) :
    schurTail M = trailingMatrix M := by
  funext i j
  simp [schurTail, trailingMatrix, h]

@[simp] theorem schurWitnessLift_zero_pivot {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (h : M 0 0 = 0)
    (y : Fin n → ℚ) : schurWitnessLift M y = Fin.cons 0 y := by
  simp [schurWitnessLift, h]

def pivotTerminal {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    Option (Fin (n+1) → ℚ) :=
  if M 0 0 < 0 then some (Pi.single 0 1)
  else if M 0 0 = 0 then
    (firstNonzeroOffDiagonal M).map (fun j => zeroPivotWitness M 0 j.succ)
  else none

def uniformNegativeWitness : (n : ℕ) →
    Matrix (Fin n) (Fin n) ℚ → Option (Fin n → ℚ)
  | 0, _ => none
  | n+1, M => match pivotTerminal M with
    | some q => some q
    | none => (uniformNegativeWitness n (schurTail M)).map (schurWitnessLift M)

theorem uniformNegativeWitness_eq (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ) :
    uniformNegativeWitness n M = rationalNegativeWitness n M := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hn : M 0 0 < 0
    · simp [uniformNegativeWitness, pivotTerminal, rationalNegativeWitness, hn]
    · by_cases hz : M 0 0 = 0
      · cases hf : firstNonzeroOffDiagonal M with
        | none =>
          have hl : schurWitnessLift M = (fun y : Fin n → ℚ => Fin.cons (0 : ℚ) y) := by
            funext y
            exact schurWitnessLift_zero_pivot M hz y
          simp [uniformNegativeWitness, pivotTerminal, rationalNegativeWitness,
            hz, hf, ih, hl]
        | some j =>
          simp [uniformNegativeWitness, pivotTerminal, rationalNegativeWitness, hz, hf]
      · simp [uniformNegativeWitness, pivotTerminal, rationalNegativeWitness, hn, hz, ih]

inductive PivotHistory : ℕ → ℕ → Type
  | nil (n : ℕ) : PivotHistory n n
  | push {n N : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
      (rest : PivotHistory (n+1) N) : PivotHistory n N

namespace PivotHistory

def restore : {n N : ℕ} → PivotHistory n N → (Fin n → ℚ) → (Fin N → ℚ)
  | _, _, .nil _, q => q
  | _, _, .push M rest, q => restore rest (schurWitnessLift M q)

def depth : {n N : ℕ} → PivotHistory n N → ℕ
  | _, _, .nil _ => 0
  | _, _, .push _ rest => depth rest + 1

theorem dimension_depth {n N : ℕ} (h : PivotHistory n N) : n + depth h = N := by
  induction h with
  | nil n => simp [depth]
  | @push n N M rest ih => simpa [depth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih

@[simp] theorem restore_push {n N : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (h : PivotHistory (n+1) N) (q : Fin n → ℚ) :
    restore (.push M h) q = restore h (schurWitnessLift M q) := rfl

theorem descent_restore {n N : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (h : PivotHistory (n+1) N) (ht : pivotTerminal M = none) :
    (uniformNegativeWitness n (schurTail M)).map (restore (.push M h)) =
      (uniformNegativeWitness (n+1) M).map (restore h) := by
  simp [uniformNegativeWitness, ht, Option.map_map, Function.comp_def, restore]

end PivotHistory
end KS.W17

end

end OAI
