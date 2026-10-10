import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import OAI.Algebra.FormulaHitting.BitModel
import OAI.Algebra.FormulaHitting.BitRefinement

namespace OAI

namespace NCHittingSpecification

universe u

inductive Formula (F : Type*) (n : ℕ) where
  | scalar : F → Formula F n
  | variable : Fin n → Formula F n
  | add : Formula F n → Formula F n → Formula F n
  | multiply : Formula F n → Formula F n → Formula F n

namespace Formula

def gates {F : Type*} {n : ℕ} : Formula F n → ℕ
  | .scalar _ => 1
  | .variable _ => 1
  | .add f g => gates f + gates g + 1
  | .multiply f g => gates f + gates g + 1

noncomputable def coefficient {F : Type*} {n : ℕ} [Semiring F] :
    Formula F n → List (Fin n) → F
  | .scalar a, w => if w = [] then a else 0
  | .variable i, w => if w = [i] then 1 else 0
  | .add f g, w => coefficient f w + coefficient g w
  | .multiply f g, w =>
      ∑ k ∈ Finset.range (w.length + 1),
        coefficient f (w.take k) * coefficient g (w.drop k)

def evaluate {F : Type*} {n d : ℕ} [Field F]
    (T : Fin n → Matrix (Fin d) (Fin d) F) :
    Formula F n → Matrix (Fin d) (Fin d) F
  | .scalar a => Matrix.scalar (Fin d) a
  | .variable i => T i
  | .add f g => evaluate T f + evaluate T g
  | .multiply f g => evaluate T f * evaluate T g

end Formula

def dimension (n s : ℕ) : ℕ :=
  if n = 1 ∧ s = 1 then 1 else 2 * n * s ^ 2

def expectedEntry (n s : ℕ) (i : Fin n)
    (r q : Fin (dimension n s)) : ℚ :=
  if n = 1 ∧ s = 1 then 1
  else if q.val < r.val then
    (-1 : ℚ) ^ (r.val - q.val - 1) /
      ((r.val : ℚ) * ((i.val + 1 : ℕ) : ℚ) ^ (r.val - q.val))
  else 0

def UniversalHitting (n s d : ℕ)
    (T : Fin n → Matrix (Fin d) (Fin d) ℚ) : Prop :=
  ∀ (F : Type*) [Field F] [CharZero F], ∀ f : Formula F n,
    f.gates ≤ s → (∃ w, f.coefficient w ≠ 0) →
      f.evaluate (fun i r q => (T i r q : F)) ≠ 0

open NCHitting.BitModel

def expectedProgram : Program :=
  .branch (.mul (.equal (.read 0) (.literal 1)) (.equal (.read 1) (.literal 1)))
    (.emit (.literal 0) (.literal 1) (.literal 1))
    (.loop (.read 0)
      (.loop (.mul (.mul (.literal 2) (.read 1)) (.power (.read 2) (.literal 2)))
        (.loop (.mul (.mul (.literal 2) (.read 2)) (.power (.read 3) (.literal 2)))
          (.branch (.less (.read 0) (.read 1))
            (.emit (.odd (.sub (.sub (.read 1) (.read 0)) (.literal 1)))
              (.literal 1)
              (.mul (.read 1) (.power (.add (.read 2) (.literal 1))
                (.sub (.read 1) (.read 0)))))
            (.emit (.literal 0) (.literal 0) (.literal 1))))))

def expectedCode (i r q : ℕ) : NCHitting.BitModel.RationalCode :=
  if q < r then ⟨decide ((r - q - 1) % 2 = 1), 1, r * (i + 1) ^ (r - q)⟩
  else ⟨false, 0, 1⟩

def expectedOutput (n s : ℕ) : List NCHitting.BitModel.RationalCode :=
  if n = 1 ∧ s = 1 then [⟨false, 1, 1⟩]
  else (List.range n).flatMap fun i =>
    (List.range (2 * n * s ^ 2)).flatMap fun r =>
      (List.range (2 * n * s ^ 2)).map fun q => expectedCode i r q

def decode (entry : NCHitting.BitModel.RationalCode) : ℚ :=
  (if entry.negative then -(entry.numerator : ℚ) else entry.numerator) / entry.denominator

def entryBitBound (n d : ℕ) : ℕ := 3 + d.size + d * n.size

def costBound (n s : ℕ) : ℕ :=
  let d := 2 * n * s ^ 2
  let M := n + s + d + 3
  let B := M * M + 4 * M + 10
  let R := 5 * (M + 1) + 6
  let P := 8 * (M * M + 2) * (M + 1) + 4 * (M + 3) + 1
  let E := R + 8 * B * B + 8 * B + (2 + M * P) + 10
  let L := M + 1 + 4 * (M + 3) + 1
  let entryCost := 20 * E + B + 20
  let entryOutput := B + 3
  let rowCost := 7 * E + 1 + d * (entryCost + L + entryOutput)
  let rowOutput := d * entryOutput
  let variableCost := 7 * E + 1 + d * (rowCost + L + rowOutput)
  let variableOutput := d * rowOutput
  2 * (M + 1) + 7 * E + 15 + (R + 1 + n * (variableCost + L + variableOutput)) + 1

def primitiveBitBound (n s : ℕ) : ℕ := 1024 * costBound n s ^ 3

def CompleteClaim (n s : ℕ) : Prop :=
  let d := dimension n s
  let result := execute expectedProgram [n, s]
  0 < d ∧ d ≤ 2 * n * s ^ 2 ∧
  result.output = expectedOutput n s ∧
  result.output.length = n * d * d ∧
  (∀ entry ∈ result.output,
    0 < entry.denominator ∧ entry.numerator ≤ 1 ∧
    entry.denominator.size ≤ entryBitBound n d ∧
    entry.bits ≤ 4 + entryBitBound n d) ∧
  (∀ (i : Fin n) (r q : Fin d),
    decode ((result.output[i.val * d * d + r.val * d + q.val]?).getD ⟨false, 0, 1⟩) =
      expectedEntry n s i r q) ∧
  result.cost ≤ costBound n s ∧
  (NCHitting.BitRefinement.Exec expectedProgram [n, s] result.output
      (NCHitting.BitRefinement.executionSteps expectedProgram [n, s]) ∧
    NCHitting.BitRefinement.executionSteps expectedProgram [n, s] ≤ primitiveBitBound n s) ∧
  UniversalHitting.{u} n s d (expectedEntry n s)

def CompleteTheorem : Prop :=
  ∀ n s : ℕ, 1 ≤ n → 1 ≤ s → CompleteClaim.{u} n s

end NCHittingSpecification

end OAI
