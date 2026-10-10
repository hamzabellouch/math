import Mathlib

namespace OAI

namespace KS.W07

abbrev DenseRatMatrix (n : ℕ) := Vector (Vector ℚ n) n

namespace DenseRatMatrix

def decode {n : ℕ} (M : DenseRatMatrix n) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (M.get i).get j

def ofMatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) : DenseRatMatrix n :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => M i j))

@[simp] theorem decode_ofMatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) :
    decode (ofMatrix M) = M := by
  funext i j
  simp [decode, ofMatrix, Vector.get]
  rfl

@[simp] theorem ofMatrix_decode {n : ℕ} (M : DenseRatMatrix n) :
    ofMatrix (decode M) = M := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [ofMatrix, decode, Vector.get]
  rfl

end DenseRatMatrix

def decodeRatVector {n : ℕ} (v : Vector ℚ n) : Fin n → ℚ := v.get

@[simp] theorem decodeRatVector_ofFn {n : ℕ} (v : Fin n → ℚ) :
    decodeRatVector (Vector.ofFn v) = v := by
  funext i
  simp [decodeRatVector, Vector.get]
  rfl

end KS.W07

end OAI
