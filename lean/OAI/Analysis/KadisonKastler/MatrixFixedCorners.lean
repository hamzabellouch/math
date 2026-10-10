import OAI.Analysis.KadisonKastler.MatrixCorners

namespace OAI

/-! # A matrix automorphism fixing the two diagonal projections

Its off-diagonal coefficient is unitary and conjugates the two corner
actions. This is the finite algebraic step in the modular cocycle argument.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

def matrixSlot (i j : Fin 2) (a : A) : CStarMatrix (Fin 2) (Fin 2) A :=
  CStarMatrix.ofMatrix (Matrix.single i j a)

theorem matrixSlot_injective (i j : Fin 2) : Function.Injective (matrixSlot (A := A) i j) := by
  intro a b hab
  simpa [matrixSlot, Matrix.single_apply] using
    congrArg (fun x : CStarMatrix (Fin 2) (Fin 2) A => x i j) hab

theorem matrixSlot_mul (i j k : Fin 2) (a b : A) :
    matrixSlot i j a * matrixSlot j k b = matrixSlot i k (a * b) :=
  Matrix.single_mul_single_same a i j k b

theorem matrixSlot_star (i j : Fin 2) (a : A) :
    star (matrixSlot i j a) = matrixSlot j i (star a) :=
  Matrix.conjTranspose_single i j a

theorem matrixSlot_sandwich (i j : Fin 2) (x : CStarMatrix (Fin 2) (Fin 2) A) :
    matrixSlot i i 1 * x * matrixSlot j j 1 = matrixSlot i j (x i j) := by
  apply CStarMatrix.ofMatrix.symm.injective
  change Matrix.single i i (1 : A) * CStarMatrix.ofMatrix.symm x * Matrix.single j j 1 =
    Matrix.single i j (x i j)
  simpa only [one_mul, mul_one, CStarMatrix.ofMatrix_symm_apply] using
    Matrix.single_mul_mul_single i i j j (1 : A) (CStarMatrix.ofMatrix.symm x) 1

theorem matrixSlot_reconstruct (i j : Fin 2) (x : CStarMatrix (Fin 2) (Fin 2) A)
    (hl : matrixSlot i i 1 * x = x) (hr : x * matrixSlot j j 1 = x) :
    x = matrixSlot i j (x i j) := by
  calc
    x = matrixSlot i i 1 * x * matrixSlot j j 1 := by rw [hl, hr]
    _ = _ := matrixSlot_sandwich i j x

variable (θ : CStarMatrix (Fin 2) (Fin 2) A ≃⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) A)

theorem matrixSlot_image_reconstruct (i j : Fin 2)
    (hi : θ (matrixSlot i i 1) = matrixSlot i i 1)
    (hj : θ (matrixSlot j j 1) = matrixSlot j j 1) (a : A) :
    θ (matrixSlot i j a) = matrixSlot i j (θ (matrixSlot i j a) i j) := by
  apply matrixSlot_reconstruct
  · rw [← hi, ← map_mul, matrixSlot_mul, one_mul]
  · rw [← hj, ← map_mul, matrixSlot_mul, mul_one]

def matrixOffDiagonalCoefficient : A := θ (matrixSlot 1 0 1) 1 0

theorem matrixOffDiagonalCoefficient_unitary
    (h0 : θ (matrixSlot 0 0 1) = matrixSlot 0 0 1)
    (h1 : θ (matrixSlot 1 1 1) = matrixSlot 1 1 1) :
    matrixOffDiagonalCoefficient θ ∈ unitary A := by
  have he := matrixSlot_image_reconstruct θ 1 0 h1 h0 (1 : A)
  change θ (matrixSlot 1 0 1) = matrixSlot 1 0 (matrixOffDiagonalCoefficient θ) at he
  have hleft : star (θ (matrixSlot 1 0 1)) * θ (matrixSlot 1 0 1) = matrixSlot 0 0 1 := by
    rw [← map_star, ← map_mul, matrixSlot_star, star_one, matrixSlot_mul, one_mul, h0]
  have hright : θ (matrixSlot 1 0 1) * star (θ (matrixSlot 1 0 1)) = matrixSlot 1 1 1 := by
    rw [← map_star, ← map_mul, matrixSlot_star, star_one, matrixSlot_mul, one_mul, h1]
  rw [he, matrixSlot_star, matrixSlot_mul] at hleft hright
  exact ⟨matrixSlot_injective 0 0 hleft, matrixSlot_injective 1 1 hright⟩

theorem matrixCorner_actions_conjugate
    (h0 : θ (matrixSlot 0 0 1) = matrixSlot 0 0 1)
    (h1 : θ (matrixSlot 1 1 1) = matrixSlot 1 1 1) (a : A) :
    θ (matrixSlot 1 1 a) 1 1 = matrixOffDiagonalCoefficient θ *
      (θ (matrixSlot 0 0 a) 0 0) * star (matrixOffDiagonalCoefficient θ) := by
  have he := matrixSlot_image_reconstruct θ 1 0 h1 h0 (1 : A)
  have hx := matrixSlot_image_reconstruct θ 0 0 h0 h0 a
  have hrep : matrixSlot 1 1 a =
      matrixSlot 1 0 1 * matrixSlot 0 0 a * star (matrixSlot 1 0 (1 : A)) := by
    rw [matrixSlot_star, star_one, matrixSlot_mul, matrixSlot_mul, one_mul, mul_one]
  have h := congrArg θ hrep
  rw [map_mul, map_mul, map_star, he, hx, matrixSlot_star,
    matrixSlot_mul, matrixSlot_mul] at h
  have heq := congrArg (fun x : CStarMatrix (Fin 2) (Fin 2) A => x 1 1) h
  simpa [matrixSlot, matrixOffDiagonalCoefficient, Matrix.single_apply] using heq

end

end KadisonKastler

end OAI
