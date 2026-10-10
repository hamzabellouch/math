import OAI.Analysis.Laughlin.FourBody.Basic
import OAI.Analysis.Laughlin.Operators.RationalPSD

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

def copyWeight (D : ℕ) (i : Fin ((D+1)/2)) : ℚ :=
  1 / ((copyLabel i).factorial * (D-copyLabel i).factorial : ℕ)

def middleRational (D : ℕ) : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℚ :=
  Matrix.diagonal (fun i => ((if copyLabel i = 1 then 2 else 0) + (3/10^6 : ℚ)) *
    copyWeight D i) - Matrix.diagonal (copyWeight D) * errorRational D *
      Matrix.diagonal (copyWeight D)

def compressedRational (D : ℕ) : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℚ :=
  gramRational D * middleRational D * gramRational D

theorem compressed_positive_of_gram_zero (D : ℕ) (h : gramRational D = 0) :
    ((compressedRational D).map (Rat.castHom ℝ)).PosSemidef := by
  have he : compressedRational D = 0 := by simp [compressedRational, h]
  rw [he]
  simpa using (Matrix.PosSemidef.zero :
    (0 : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℝ).PosSemidef)


theorem gram_one_zero : gramRational 1 = 0 := by decide +kernel
theorem gram_two_zero : gramRational 2 = 0 := by decide +kernel
theorem gram_three_zero : gramRational 3 = 0 := by decide +kernel
theorem gram_four_zero : gramRational 4 = 0 := by decide +kernel
theorem gram_six_zero : gramRational 6 = 0 := by decide +kernel

theorem zero_blocks_positive (D : ℕ) (hD : D ∈ [1,2,3,4,6]) :
    ((compressedRational D).map (Rat.castHom ℝ)).PosSemidef := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
  rcases hD with rfl | rfl | rfl | rfl | rfl
  · exact compressed_positive_of_gram_zero 1 gram_one_zero
  · exact compressed_positive_of_gram_zero 2 gram_two_zero
  · exact compressed_positive_of_gram_zero 3 gram_three_zero
  · exact compressed_positive_of_gram_zero 4 gram_four_zero
  · exact compressed_positive_of_gram_zero 6 gram_six_zero

end Laughlin.Certificate

end OAI
