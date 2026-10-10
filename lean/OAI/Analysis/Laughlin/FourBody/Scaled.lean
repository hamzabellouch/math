import Mathlib.Analysis.SpecialFunctions.Sqrt
import OAI.Analysis.Laughlin.FourBody.Matrix
import OAI.Analysis.Laughlin.Operators.MatrixCongruence

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

noncomputable def weightSqrtDiagonal (D : ℕ) : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℝ :=
  Matrix.diagonal (fun i => Real.sqrt (copyWeight D i : ℝ))

noncomputable def certificateDiagonal (D : ℕ) : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℝ :=
  (Matrix.diagonal (fun i : Fin ((D+1)/2) =>
    (if copyLabel i = 1 then 2 else 0) + (3/10^6 : ℚ))).map (Rat.castHom ℝ)

noncomputable def scaledError (D : ℕ) : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℝ :=
  weightSqrtDiagonal D * (errorRational D).map (Rat.castHom ℝ) * weightSqrtDiagonal D

noncomputable def scaledGram (D : ℕ) : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℝ :=
  weightSqrtDiagonal D * (gramRational D).map (Rat.castHom ℝ) * weightSqrtDiagonal D

theorem cast_rat_diagonal {n : ℕ} (v : Fin n → ℚ) :
    (Matrix.diagonal v).map (Rat.castHom ℝ) = Matrix.diagonal (fun i => (v i : ℝ)) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.map_apply,h]

theorem cast_rat_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ) :
    (A-B).map (Rat.castHom ℝ) = A.map (Rat.castHom ℝ)-B.map (Rat.castHom ℝ) := by
  ext i j
  simp [Matrix.map_apply,Matrix.sub_apply]

theorem copyWeight_nonneg (D : ℕ) (i : Fin ((D+1)/2)) : 0 ≤ (copyWeight D i : ℝ) := by
  unfold copyWeight
  positivity

theorem weightSqrtDiagonal_sq (D : ℕ) :
    weightSqrtDiagonal D * weightSqrtDiagonal D =
      (Matrix.diagonal (copyWeight D)).map (Rat.castHom ℝ) := by
  rw [weightSqrtDiagonal,Matrix.diagonal_mul_diagonal,cast_rat_diagonal]
  congr 1
  funext i
  simpa [pow_two] using Real.sq_sqrt (copyWeight_nonneg D i)

theorem weightSqrtDiagonal_middle_diagonal (D : ℕ) :
    weightSqrtDiagonal D * certificateDiagonal D * weightSqrtDiagonal D =
      (Matrix.diagonal (fun i => ((if copyLabel i = 1 then 2 else 0) + (3/10^6 : ℚ))*copyWeight D i)).map
        (Rat.castHom ℝ) := by
  simp only [weightSqrtDiagonal,certificateDiagonal,cast_rat_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  change Real.sqrt (copyWeight D i : ℝ) *
    (((if copyLabel i = 1 then 2 else 0) + (3/10^6 : ℚ) : ℚ) : ℝ) * Real.sqrt (copyWeight D i : ℝ) = _
  rw [Rat.cast_mul]
  calc
    _ = (((if copyLabel i = 1 then 2 else 0) + (3/10^6 : ℚ) : ℚ) : ℝ) *
        (Real.sqrt (copyWeight D i : ℝ))^2 := by ring
    _ = _ := by rw [Real.sq_sqrt (copyWeight_nonneg D i)]

theorem scaled_compression_identity (D : ℕ) :
    scaledGram D * (certificateDiagonal D-scaledError D) * scaledGram D =
      weightSqrtDiagonal D * (compressedRational D).map (Rat.castHom ℝ) * weightSqrtDiagonal D := by
  rw [scaledGram,scaledError,compressed_congruence_identity,
    weightSqrtDiagonal_middle_diagonal,weightSqrtDiagonal_sq]
  simp only [compressedRational,middleRational,Matrix.map_mul,cast_rat_sub]

theorem scaled_compression_positive (D : ℕ)
    (hM : ((compressedRational D).map (Rat.castHom ℝ)).PosSemidef) :
    (scaledGram D * (certificateDiagonal D-scaledError D) * scaledGram D).PosSemidef := by
  rw [scaled_compression_identity]
  have hd : (weightSqrtDiagonal D).IsHermitian := by
    simp [weightSqrtDiagonal,Matrix.IsHermitian]
  simpa only [hd.eq] using hM.mul_mul_conjTranspose_same (weightSqrtDiagonal D)

end Laughlin.Certificate

end OAI
