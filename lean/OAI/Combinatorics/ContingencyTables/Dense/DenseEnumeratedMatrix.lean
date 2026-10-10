import OAI.Combinatorics.ContingencyTables.Dense.DenseMatrixWalk
import OAI.Combinatorics.ContingencyTables.Transport.FiniteGridWords

namespace OAI

/-! # Computing every state of the dense transition table -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators

abbrev EnumeratedMatrixInput := CountMatrixContext×List Bool

def enumerationData (z : EnumeratedMatrixInput) : GridEnumerationData :=
  (z.2,4*z.1.2.2^8)

def enumerationDataRealizer : Realizer enumerationData := by
  let d : Realizer (fun z : EnumeratedMatrixInput => z.1.2.2) :=
    composition (composition first second) second
  let K := composition (pair (constant 4) (composition d eighthPower)) multiply
  exact pair second K

lemma polynomial_enumerationData : PolynomialTime enumerationDataRealizer := by
  have hd : PolynomialTime (composition (composition
      (first (A := CountMatrixContext) (B := List Bool)) second) second) :=
    polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_second
  unfold enumerationDataRealizer
  exact polynomial_pair polynomial_second (polynomial_composition
    (polynomial_pair (polynomial_constant 4) (polynomial_composition hd polynomial_eighthPower))
    polynomial_multiply)

def enumeratedMatrixInput (z : EnumeratedMatrixInput) : CountMatrixData :=
  (z.1,gridWords (enumerationData z))

def enumeratedMatrixInputRealizer : Realizer enumeratedMatrixInput :=
  pair first (composition enumerationDataRealizer gridWordsRealizer)

def enumerationMeasure (z : EnumeratedMatrixInput) : ℕ :=
  gridStateCount (enumerationData z)+weight z

lemma work_enumeratedMatrixInput : WorkBound enumeratedMatrixInputRealizer enumerationMeasure := by
  have hp : WorkBound enumerationDataRealizer enumerationMeasure :=
    work_of_polynomial polynomial_enumerationData Polynomial.X (fun z => by
      simp only [enumerationMeasure,Polynomial.eval_X]; omega)
  obtain ⟨p,hp'⟩ := hp
  have hg : WorkBound (composition enumerationDataRealizer gridWordsRealizer)
      enumerationMeasure := by
    apply work_composition ⟨p,hp'⟩ work_gridWords (Polynomial.X+p)
    intro z
    have hw := hp' z
    simp only [enumerationMeasure,Polynomial.eval_add,Polynomial.eval_X]
    change gridStateCount (enumerationData z)+weight (enumerationData z) ≤ _
    change _≤p.eval (enumerationMeasure z) at hw
    unfold enumerationMeasure at hw
    omega
  unfold enumeratedMatrixInputRealizer
  exact work_pair (work_of_polynomial polynomial_first Polynomial.X (fun z => by
    simp only [enumerationMeasure,Polynomial.eval_X]; omega)) hg Polynomial.X
    (fun z => by simp only [enumerationMeasure,Polynomial.eval_X]; omega)

def enumeratedMatrix (z : EnumeratedMatrixInput) : List (List ℕ) :=
  countMatrix (enumeratedMatrixInput z)

def enumeratedMatrixRealizer : Realizer enumeratedMatrix :=
  composition enumeratedMatrixInputRealizer countMatrixRealizer

/-- All states are generated from the dimension marker and grid size.
The work is polynomial in their count and the supplied binary data. -/
theorem work_enumeratedMatrix : WorkBound enumeratedMatrixRealizer enumerationMeasure :=
  work_then_polynomial work_enumeratedMatrixInput polynomial_countMatrix

theorem enumeratedMatrix_actual {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hq : m*n≤d)
    (xs dims : List Bool) (hxs : xs.length=8*d^5) (hdims : dims.length=m*n) :
    enumeratedMatrix ((((xs,2^denseStepBits d),((marginCode R,marginCode P),d)),dims))=
      List.ofFn (fun j => List.ofFn (fun i =>
        denseTransitionCount R P d finProdFinEquiv
          (gridEnumeration (m*n) (4*d^8) i) (gridEnumeration (m*n) (4*d^8) j))) := by
  unfold enumeratedMatrix enumeratedMatrixInput enumerationData
  rw [gridWords_eq_length dims (4*d^8) (m*n) hdims]
  exact countMatrix_actual R P hq (gridEnumeration (m*n) (4*d^8)) xs hxs

end ContingencyTables.DensePrograms

end OAI
