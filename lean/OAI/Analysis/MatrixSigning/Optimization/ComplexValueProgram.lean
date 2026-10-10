import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.FinRealify

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix CurrentKS.HermitianCoordinates
open scoped BigOperators ComplexOrder

variable {d N : ℕ}

lemma scalar_one_psd_iff (r : ℝ) :
    (r • (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosSemidef ↔ 0 ≤ r := by
  constructor
  · intro h
    simpa using h.diag_nonneg (i := (0 : Fin 1))
  · intro hr
    exact (Matrix.PosSemidef.one : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef).smul hr

lemma lowerMatrixPencil_psd (second : Bool) (v : Fin (valueDimension d) → ℝ) :
    ((lowerMatrixPencil d second).realEval v).PosSemidef ↔
    (decode (matrixCoordinate d second v)-(1/400:ℝ) •
      (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef := by
  rw [lowerMatrixPencil_realEval,← finRealify_psd]
  simp only [finRealify_sub,finRealify_smul,finRealify_one,finRealify_decode,
    matrixVariable,LinearMap.comp_apply]
lemma upperMatrixPencil_psd (ε : ℚ) (second : Bool) (v : Fin (valueDimension d) → ℝ) :
    ((upperMatrixPencil d ε second).realEval v).PosSemidef ↔
    ((200/(ε:ℝ)) • (1 : Matrix (Fin d) (Fin d) ℂ)-
      decode (matrixCoordinate d second v)).PosSemidef := by
  rw [upperMatrixPencil_realEval,← finRealify_psd]
  simp only [finRealify_sub,finRealify_smul,finRealify_one,finRealify_decode,
    matrixVariable,LinearMap.comp_apply]

def complexValueProgram (ε : ℝ) (S : Matrix (Fin d) (Fin d) ℂ)
    (η : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
    (t : ℝ) (X Y : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (Matrix.fromBlocks (t • (1 : Matrix (Fin d) (Fin d) ℂ)-S-η Y) 1 1 X).PosSemidef ∧
  (Matrix.fromBlocks (t • (1 : Matrix (Fin d) (Fin d) ℂ)+S-η X) 1 1 Y).PosSemidef ∧
  (X-(1/400:ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef ∧
  ((200/ε) • (1 : Matrix (Fin d) (Fin d) ℂ)-X).PosSemidef ∧
  (Y-(1/400:ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef ∧
  ((200/ε) • (1 : Matrix (Fin d) (Fin d) ℂ)-Y).PosSemidef ∧ 0 ≤ t ∧ t ≤ 100

lemma valuePencil_psd (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ)
    (ε : ℚ) (v : Fin (valueDimension d) → ℝ) :
    ((valuePencil coords x θ ε).realEval v).PosSemidef ↔
    complexValueProgram (ε:ℝ)
      (complexSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ)))
      (complexEta (fun i j => (coords i j:ℝ)) (fun i => (θ i:ℝ)))
      (timeCoordinate d v) (decode (matrixCoordinate d false v))
      (decode (matrixCoordinate d true v)) := by
  simp only [valuePencil,Pencil.blockDiagonal_realEval,blockDiagonal_posSemidef,
    schurPencil_psd,lowerMatrixPencil_psd,upperMatrixPencil_psd,
    lowerTimePencil_realEval,upperTimePencil_realEval,scalar_one_psd_iff,
    Bool.false_eq_true,ite_false,Bool.not_false,ite_true,Bool.not_true,
    complexValueProgram,sub_eq_add_neg]
  simp only [← sub_eq_add_neg,sub_nonneg]
  tauto

lemma trace_decode (x : Fin d × Fin d → ℝ) :
    (Matrix.trace (decode x)).re=∑ i,x (i,i) := by
  simp [Matrix.trace,decode]

lemma valueObjective_complex (ε : ℚ) (v : Fin (valueDimension d) → ℚ) :
    (valueObjective d ε v : ℝ)=timeCoordinate d (fun i => (v i:ℝ))+(ε:ℝ)*
      ((Matrix.trace (decode (matrixCoordinate d false (fun i => (v i:ℝ))))).re+
        (Matrix.trace (decode (matrixCoordinate d true (fun i => (v i:ℝ))))).re) := by
  rw [valueObjective_apply]
  push_cast
  rw [trace_decode,trace_decode,← Finset.sum_add_distrib]
  rfl

end CurrentKS.RationalSDP

end OAI
