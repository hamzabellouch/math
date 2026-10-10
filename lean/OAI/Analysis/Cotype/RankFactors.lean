import OAI.Analysis.Cotype.FrameOrbit
import Mathlib.LinearAlgebra.Matrix.Rank

namespace OAI

noncomputable section

open scoped BigOperators Matrix
namespace Cotype
variable {𝕜 : Type*} [Field 𝕜] {m : ℕ}

theorem exists_rank_pairing_factors (P : Matrix (Fin m) (Fin m) 𝕜) :
    ∃ I J : Matrix (Fin m) (Fin P.rank) 𝕜,
      ∀ l t, (∑ i, ∑ j, I i l * P i j * J j t) = if l = t then 1 else 0 := by
  obtain ⟨V,U,e,hV,hU,h⟩ := Matrix.exists_rank_normal_form P
  let I : Matrix (Fin m) (Fin P.rank) 𝕜 := fun i l => V (e.symm (Sum.inl l)) i
  let J : Matrix (Fin m) (Fin P.rank) 𝕜 := fun j t => U j (e.symm (Sum.inl t))
  refine ⟨I,J,?_⟩
  intro l t
  have hh := congrArg (fun A : Matrix (Fin m) (Fin m) 𝕜 =>
    A (e.symm (Sum.inl l)) (e.symm (Sum.inl t))) h
  simp only [Matrix.mul_apply, Finset.sum_mul] at hh
  rw [Finset.sum_comm] at hh
  simpa [I,J,Matrix.submatrix, Matrix.fromBlocks, Matrix.one_apply] using hh

theorem exists_rank_pairing_matrix (P : Matrix (Fin m) (Fin m) 𝕜) :
    ∃ I J : Matrix (Fin m) (Fin P.rank) 𝕜, I.transpose * P * J = 1 := by
  obtain ⟨I,J,h⟩ := exists_rank_pairing_factors P
  refine ⟨I,J,?_⟩
  ext l t
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Matrix.one_apply]
  rw [Finset.sum_comm]
  exact h l t

theorem rank_pairing_contract {r : ℕ} (P : Matrix (Fin m) (Fin m) 𝕜)
    (I J : Matrix (Fin m) (Fin r) 𝕜) (h : I.transpose * P * J = 1)
    (x y : Fin r → 𝕜) :
    coordinateDual (I.mulVec x) (P.mulVec (J.mulVec y)) = coordinateDual x y := by
  change (I *ᵥ x) ⬝ᵥ (P *ᵥ (J *ᵥ y)) = x ⬝ᵥ y
  rw [← Matrix.vecMul_transpose I x, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

end Cotype

end

end OAI
