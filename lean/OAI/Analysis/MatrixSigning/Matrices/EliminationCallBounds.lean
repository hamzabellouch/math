import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.DenseElimination
import OAI.Analysis.MatrixSigning.Matrices.PivotHistory
import OAI.Analysis.MatrixSigning.Matrices.PivotHistoryBounds

namespace OAI

section

namespace KS.W17

open KS.W07

inductive DenseEliminationCall {N : ℕ} (A : DenseRatMatrix N) :
    {t : ℕ} → DenseRatMatrix t → Prop
  | initial : DenseEliminationCall A A
  | zero {t : ℕ} {S : DenseRatMatrix (t + 1)}
      (previous : DenseEliminationCall A S)
      (hzero : DenseRatMatrix.decode S 0 0 = 0)
      (hrow : firstNonzeroOffDiagonal (DenseRatMatrix.decode S) = none) :
      DenseEliminationCall A
        (DenseRatMatrix.ofMatrix (trailingMatrix (DenseRatMatrix.decode S)))
  | positive {t : ℕ} {S : DenseRatMatrix (t + 1)}
      (previous : DenseEliminationCall A S)
      (hpositive : 0 < DenseRatMatrix.decode S 0 0) :
      DenseEliminationCall A
        (DenseRatMatrix.ofMatrix (schurTail (DenseRatMatrix.decode S)))

theorem denseNegativeWitness_zero_recurse {t : ℕ} (S : DenseRatMatrix (t + 1))
    (hzero : DenseRatMatrix.decode S 0 0 = 0)
    (hrow : firstNonzeroOffDiagonal (DenseRatMatrix.decode S) = none) :
    denseNegativeWitness (t + 1) S =
      (denseNegativeWitness t
        (DenseRatMatrix.ofMatrix (trailingMatrix (DenseRatMatrix.decode S)))).map
          (fun y => Vector.ofFn (Fin.cons 0 (decodeRatVector y))) := by
  simp [denseNegativeWitness, hzero, hrow]

theorem denseNegativeWitness_positive_recurse {t : ℕ} (S : DenseRatMatrix (t + 1))
    (hpositive : 0 < DenseRatMatrix.decode S 0 0) :
    denseNegativeWitness (t + 1) S =
      (denseNegativeWitness t
        (DenseRatMatrix.ofMatrix (schurTail (DenseRatMatrix.decode S)))).map
          (fun y => Vector.ofFn (schurWitnessLift (DenseRatMatrix.decode S)
            (decodeRatVector y))) := by
  simp [denseNegativeWitness, not_lt.mpr hpositive.le, hpositive.ne']

theorem DenseEliminationCall.pivotTrace {N t : ℕ} {A : DenseRatMatrix N}
    {S : DenseRatMatrix t} (h : DenseEliminationCall A S) :
    ∃ k, ∃ p : Fin k → Fin N, ∃ r : Fin t → Fin N,
      PivotTrace (DenseRatMatrix.decode A) p r (DenseRatMatrix.decode S) := by
  induction h with
  | initial => exact ⟨0, (fun i => Fin.elim0 i), id, PivotTrace.initial⟩
  | @zero t S previous hz hrow ih =>
      obtain ⟨k, p, r, ht⟩ := ih
      refine ⟨k, p, (fun i => r i.succ), ?_⟩
      have htrace := PivotTrace.zero ht hz
      have he : schurTail (DenseRatMatrix.decode S) = trailingMatrix (DenseRatMatrix.decode S) := by
        ext i j
        simp [schurTail, trailingMatrix, hz]
      rw [he] at htrace
      simpa only [DenseRatMatrix.decode_ofMatrix] using htrace
  | @positive t S previous hp ih =>
      obtain ⟨k, p, r, ht⟩ := ih
      exact ⟨k + 1, Fin.snoc p (r 0), (fun i => r i.succ), by
        simpa using PivotTrace.positive ht hp⟩

theorem DenseEliminationCall.entry_parts_size_le {N t : ℕ} {A : DenseRatMatrix N}
    {S : DenseRatMatrix t} (h : DenseEliminationCall A S)
    (b : ℕ) (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2 ^ b) (i j : Fin t) :
    Nat.size (DenseRatMatrix.decode S i j).num.natAbs ≤ KS.W30.inverseBitBound N b ∧
      Nat.size (DenseRatMatrix.decode S i j).den ≤ KS.W30.inverseBitBound N b := by
  obtain ⟨k, p, r, ht⟩ := h.pivotTrace
  exact ht.entry_parts_size_le b hnum hden i j

end KS.W17

end

end OAI
