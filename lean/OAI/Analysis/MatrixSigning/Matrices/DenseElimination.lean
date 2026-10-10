import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.DenseRatMatrix
import OAI.Analysis.MatrixSigning.Matrices.EliminationCompleteness

namespace OAI

section

namespace KS.W17

open Matrix
open KS.W07

def denseNegativeWitness : (n : ℕ) → DenseRatMatrix n → Option (Vector ℚ n)
  | 0, _ => none
  | n + 1, M =>
      let A := DenseRatMatrix.decode M
      if A 0 0 < 0 then some (Vector.ofFn (Pi.single 0 1))
      else if A 0 0 = 0 then
        match firstNonzeroOffDiagonal A with
        | some j => some (Vector.ofFn (zeroPivotWitness A 0 j.succ))
        | none =>
            (denseNegativeWitness n (DenseRatMatrix.ofMatrix (trailingMatrix A))).map
              (fun y => Vector.ofFn (Fin.cons 0 (decodeRatVector y)))
      else
        (denseNegativeWitness n (DenseRatMatrix.ofMatrix (schurTail A))).map
          (fun y => Vector.ofFn (schurWitnessLift A (decodeRatVector y)))

private theorem map_materialized {n m : ℕ} (o : Option (Vector ℚ n))
    (f : (Fin n → ℚ) → (Fin m → ℚ)) :
    (o.map (fun v => Vector.ofFn (f (decodeRatVector v)))).map decodeRatVector =
      (o.map decodeRatVector).map f := by
  cases o <;> simp

theorem denseNegativeWitness_decode (n : ℕ) (M : DenseRatMatrix n) :
    (denseNegativeWitness n M).map decodeRatVector =
      rationalNegativeWitness n (DenseRatMatrix.decode M) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      let A := DenseRatMatrix.decode M
      have hA : DenseRatMatrix.decode M = A := rfl
      by_cases hnegative : A 0 0 < 0
      · simp [denseNegativeWitness, rationalNegativeWitness, hA, hnegative]
      · by_cases hzero : A 0 0 = 0
        · cases hfind : firstNonzeroOffDiagonal A with
          | some j =>
              simp [denseNegativeWitness, rationalNegativeWitness, hA, hzero, hfind]
          | none =>
              simp only [denseNegativeWitness, rationalNegativeWitness, hA,
                hzero, hfind, lt_self_iff_false, ite_false, ite_true]
              rw [map_materialized, ih, DenseRatMatrix.decode_ofMatrix]
        · simp only [denseNegativeWitness, rationalNegativeWitness, hA,
            hnegative, hzero, ite_false]
          rw [map_materialized, ih, DenseRatMatrix.decode_ofMatrix]

theorem denseNegativeWitness_correct (n : ℕ) (M : DenseRatMatrix n)
    (hM : (DenseRatMatrix.decode M).IsSymm) :
    match denseNegativeWitness n M with
    | none => ((DenseRatMatrix.decode M).map (fun q : ℚ => (q : ℝ))).PosSemidef
    | some q => decodeRatVector q ⬝ᵥ
        (DenseRatMatrix.decode M *ᵥ decodeRatVector q) < 0 := by
  cases hout : denseNegativeWitness n M with
  | none =>
      have hr : rationalNegativeWitness n (DenseRatMatrix.decode M) = none := by
        rw [← denseNegativeWitness_decode, hout]
        rfl
      exact rationalNegativeWitness_none_psd n (DenseRatMatrix.decode M) hM hr
  | some q =>
      have hr : rationalNegativeWitness n (DenseRatMatrix.decode M) =
          some (decodeRatVector q) := by
        rw [← denseNegativeWitness_decode, hout]
        rfl
      exact rationalNegativeWitness_sound n (DenseRatMatrix.decode M) hM
        (decodeRatVector q) hr

end KS.W17

end

end OAI
