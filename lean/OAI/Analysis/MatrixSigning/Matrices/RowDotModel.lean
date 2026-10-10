import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedDotModel
import OAI.Analysis.MatrixSigning.Matrices.DenseMatrixSerialization

namespace OAI

section

namespace KS.W12.RowDot
open KS.W07 Matrix
open scoped BigOperators

def vectorTape {n : ℕ} (x : Fin n → ℚ) : List Bool :=
  (List.ofFn (fun j => KS.W01.encodeRat (x j))).flatMap KS.W01.frame

def valueTape (xs : List ℚ) : List Bool := xs.flatMap (fun q => KS.W01.frame (KS.W01.encodeRat q))

def indexedVector {n : ℕ} (x : Fin n → ℚ) : List (Fin n × ℚ) := List.ofFn (fun j => (j, x j))

def tailTape {n : ℕ} (xs : List (Fin n × ℚ)) : List Bool := valueTape (xs.map Prod.snd)

def rowPairs {n : ℕ} (M : DenseRatMatrix n) (i : Fin n) (xs : List (Fin n × ℚ)) :
    List (ℚ × ℚ) := xs.map (fun p => (DenseRatMatrix.decode M i p.1, p.2))

def Consecutive {n : ℕ} (k : ℕ) (xs : List (Fin n × ℚ)) : Prop :=
  xs.map (fun p => p.1.val) = List.range' k xs.length

theorem consecutive_cons {n : ℕ} (k : ℕ) (p : Fin n × ℚ) (xs : List (Fin n × ℚ)) :
    Consecutive k (p :: xs) ↔ p.1.val = k ∧ Consecutive (k + 1) xs := by
  simp [Consecutive, List.range'_succ]

theorem consecutive_indexedVector {n : ℕ} (x : Fin n → ℚ) : Consecutive 0 (indexedVector x) := by
  unfold Consecutive indexedVector
  apply List.ext_getElem
  · simp
  · intro j hj hk
    simp

@[simp] theorem tailTape_indexedVector {n : ℕ} (x : Fin n → ℚ) :
    tailTape (indexedVector x) = vectorTape x := by
  simp only [tailTape, indexedVector, valueTape, vectorTape, List.map_ofFn]
  rw [show (List.ofFn (fun j => KS.W01.encodeRat (x j))) =
      (List.ofFn x).map KS.W01.encodeRat by simp [Function.comp_def]]
  rw [List.flatMap_map]
  rfl

@[simp] theorem tailTape_nil {n : ℕ} : tailTape ([] : List (Fin n × ℚ)) = [] := rfl
@[simp] theorem tailTape_cons {n : ℕ} (p : Fin n × ℚ) (xs : List (Fin n × ℚ)) :
    tailTape (p :: xs) = KS.W01.frame (KS.W01.encodeRat p.2) ++ tailTape xs := rfl

@[simp] theorem rowPairs_nil {n : ℕ} (M : DenseRatMatrix n) (i : Fin n) : rowPairs M i [] = [] := rfl
@[simp] theorem rowPairs_cons {n : ℕ} (M : DenseRatMatrix n) (i : Fin n)
    (p : Fin n × ℚ) (xs : List (Fin n × ℚ)) :
    rowPairs M i (p :: xs) = (DenseRatMatrix.decode M i p.1, p.2) :: rowPairs M i xs := rfl

theorem rowPairs_dotValue {n : ℕ} (M : DenseRatMatrix n) (i : Fin n) (x : Fin n → ℚ) :
    FixedDot.dotValue (rowPairs M i (indexedVector x)) = (DenseRatMatrix.decode M *ᵥ x) i := by
  simp [rowPairs, indexedVector, FixedDot.dotValue, Matrix.mulVec, dotProduct, List.sum_ofFn]

def state (matrix vector row dim remaining counter reversed : List Bool) : Fin 29 → List Bool :=
  fun j => if j = 19 then matrix else if j = 20 then vector else if j = 21 then row
    else if j = 22 then dim else if j = 23 then remaining else if j = 24 then counter
    else if j = 25 then reversed else []

def boundary {n : ℕ} (M : DenseRatMatrix n) (x : Fin n → ℚ) (i : Fin n)
    (remaining : List (Fin n × ℚ)) (k : ℕ) (out : List Bool) : Fin 29 → List Bool :=
  state (KS.W08.denseMatrixTape M) (vectorTape x) (Computability.encodeNat i.val)
    (Computability.encodeNat n) (tailTape remaining) (Computability.encodeNat k) out

end KS.W12.RowDot

end

end OAI
