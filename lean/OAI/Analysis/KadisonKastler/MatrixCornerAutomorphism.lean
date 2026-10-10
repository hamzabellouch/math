import OAI.Analysis.KadisonKastler.MatrixFixedCorners

namespace OAI

/-! # Restricting a matrix automorphism to a fixed diagonal corner -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

theorem matrixSlot_add (i j : Fin 2) (a b : A) :
    matrixSlot i j (a + b) = matrixSlot i j a + matrixSlot i j b := by
  ext k l
  by_cases h : i = k ∧ j = l <;> simp [matrixSlot, h]

theorem matrixSlot_smul (i j : Fin 2) (r : ℂ) (a : A) :
    matrixSlot i j (r • a) = r • matrixSlot i j a := by
  ext k l
  simp [matrixSlot, Matrix.single_apply, smul_ite]

theorem matrixSlot_zero (i j : Fin 2) : matrixSlot (A := A) i j 0 = 0 := by
  ext k l
  simp [matrixSlot]

variable (θ : CStarMatrix (Fin 2) (Fin 2) A ≃⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) A)
  (i : Fin 2) (hi : θ (matrixSlot i i 1) = matrixSlot i i 1)

def matrixCornerValue (a : A) : A := θ (matrixSlot i i a) i i

include hi in
theorem matrixCornerValue_reconstruct (a : A) :
    θ (matrixSlot i i a) = matrixSlot i i (matrixCornerValue θ i a) :=
  matrixSlot_image_reconstruct θ i i hi hi a

def matrixCornerHom : A →⋆ₐ[ℂ] A where
  toFun := matrixCornerValue θ i
  map_one' := by
    have h := congrArg (fun x : CStarMatrix (Fin 2) (Fin 2) A => x i i) hi
    simpa [matrixCornerValue, matrixSlot, Matrix.single_apply] using h
  map_mul' a b := by
    apply matrixSlot_injective i i
    calc
      matrixSlot i i (matrixCornerValue θ i (a * b)) = θ (matrixSlot i i (a * b)) :=
        (matrixCornerValue_reconstruct θ i hi _).symm
      _ = θ (matrixSlot i i a) * θ (matrixSlot i i b) := by
        rw [← matrixSlot_mul i i i a b, map_mul]
      _ = matrixSlot i i (matrixCornerValue θ i a * matrixCornerValue θ i b) := by
        rw [matrixCornerValue_reconstruct θ i hi, matrixCornerValue_reconstruct θ i hi,
          matrixSlot_mul]
  map_zero' := by
    change θ (matrixSlot i i 0) i i = 0
    rw [matrixSlot_zero, map_zero]
    rfl
  map_add' a b := by
    change θ (matrixSlot i i (a + b)) i i = _
    rw [matrixSlot_add, map_add, CStarMatrix.add_apply]
    rfl
  commutes' r := by
    change θ (matrixSlot i i (algebraMap ℂ A r)) i i = algebraMap ℂ A r
    rw [Algebra.algebraMap_eq_smul_one, matrixSlot_smul, map_smul, hi,
      CStarMatrix.smul_apply]
    simp [matrixSlot]
  map_star' a := by
    apply matrixSlot_injective i i
    calc
      matrixSlot i i (matrixCornerValue θ i (star a)) = θ (matrixSlot i i (star a)) :=
        (matrixCornerValue_reconstruct θ i hi _).symm
      _ = star (θ (matrixSlot i i a)) := by rw [← matrixSlot_star, map_star]
      _ = matrixSlot i i (star (matrixCornerValue θ i a)) := by
        rw [matrixCornerValue_reconstruct θ i hi, matrixSlot_star]

theorem matrixCornerHom_injective : Function.Injective (matrixCornerHom θ i hi) := by
  intro a b hab
  apply matrixSlot_injective i i
  apply θ.injective
  change θ (matrixSlot i i a) = θ (matrixSlot i i b)
  rw [matrixCornerValue_reconstruct θ i hi, matrixCornerValue_reconstruct θ i hi]
  exact congrArg (matrixSlot i i) hab

theorem matrixCornerHom_surjective : Function.Surjective (matrixCornerHom θ i hi) := by
  have hs : θ.symm (matrixSlot i i 1) = matrixSlot i i 1 := by
    calc
      _ = θ.symm (θ (matrixSlot i i 1)) := congrArg θ.symm hi.symm
      _ = _ := θ.symm_apply_apply _
  intro a
  refine ⟨matrixCornerValue θ.symm i a, ?_⟩
  apply matrixSlot_injective i i
  change matrixSlot i i (matrixCornerValue θ i (matrixCornerValue θ.symm i a)) = _
  rw [← matrixCornerValue_reconstruct θ i hi, ← matrixCornerValue_reconstruct θ.symm i hs,
    θ.apply_symm_apply]

def matrixCornerAut : A ≃⋆ₐ[ℂ] A :=
  StarAlgEquiv.ofBijective (matrixCornerHom θ i hi)
    ⟨matrixCornerHom_injective θ i hi, matrixCornerHom_surjective θ i hi⟩

theorem matrixCornerAut_apply (a : A) :
    matrixCornerAut θ i hi a = θ (matrixSlot i i a) i i := rfl

end

end KadisonKastler

end OAI
