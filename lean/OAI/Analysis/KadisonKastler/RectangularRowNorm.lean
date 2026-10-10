import OAI.Analysis.KadisonKastler.FiniteMatrixBounds

namespace OAI

/-! Rectangular row norm estimates on finite Hilbert C-star modules. -/

namespace KadisonKastler

noncomputable section

open scoped WithCStarModule InnerProductSpace
open CStarModule

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The C-star norm lower bound holds for rectangular matrices. -/
theorem rectangular_norm_sq_le (X : CStarMatrix ι κ A) :
    ‖X‖ ^ 2 ≤ ‖X * X.conjTranspose‖ := by
  have hmain : ‖X‖ ≤ Real.sqrt ‖X * X.conjTranspose‖ := by
    change ‖CStarMatrix.toCLM X‖ ≤ _
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro v
    rw [norm_eq_sqrt_norm_inner_self (A := A),
      ← CStarMatrix.inner_toCLM_conjTranspose_right]
    have h : ‖⟪v, (CStarMatrix.toCLM X.conjTranspose) (CStarMatrix.toCLM X v)⟫_A‖ ≤
        ‖X * X.conjTranspose‖ * ‖v‖ ^ 2 := by
      calc
        _ ≤ ‖v‖ * ‖(CStarMatrix.toCLM X.conjTranspose) (CStarMatrix.toCLM X v)‖ :=
          norm_inner_le (C⋆ᵐᵒᵈ(A, ι → A))
        _ = ‖v‖ * ‖CStarMatrix.toCLM (X * X.conjTranspose) v‖ := by
          rw [rectangular_toCLM_mul_finite]
          rfl
        _ ≤ ‖v‖ * (‖X * X.conjTranspose‖ * ‖v‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg v)
        _ = _ := by ring
    calc
      _ ≤ Real.sqrt (‖X * X.conjTranspose‖ * ‖v‖ ^ 2) := Real.sqrt_le_sqrt h
      _ = Real.sqrt ‖X * X.conjTranspose‖ * ‖v‖ := by
        rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg v)]
  exact (sq_le_sq₀ (norm_nonneg X) (Real.sqrt_nonneg _)).2 hmain |>.trans_eq
    (Real.sq_sqrt (norm_nonneg _))

/-- A contractive row has a contractive adjoint column. -/
theorem rectangular_row_and_column_contract (X : CStarMatrix ι κ A)
    (h : ‖X * X.conjTranspose‖ ≤ 1) : ‖X‖ ≤ 1 ∧ ‖X.conjTranspose‖ ≤ 1 := by
  have hX : ‖X‖ ≤ 1 := by nlinarith [rectangular_norm_sq_le X, norm_nonneg X]
  have hs := rectangular_norm_sq_le X.conjTranspose
  have he : X.conjTranspose.conjTranspose = X := by ext i j; simp
  rw [he] at hs
  have hm := rectangular_norm_mul_le_finite X.conjTranspose X
  have hm' : ‖X.conjTranspose * X‖ ≤ ‖X.conjTranspose‖ :=
    hm.trans (by nlinarith [norm_nonneg X.conjTranspose])
  exact ⟨hX, by nlinarith [norm_nonneg X.conjTranspose]⟩


/-- Transposition to the adjoint column does not increase the rectangular norm. -/
theorem norm_conjTranspose_le_finite (Y : CStarMatrix ι κ A) :
    ‖Y.conjTranspose‖ ≤ ‖Y‖ := by
  have hs := rectangular_norm_sq_le Y.conjTranspose
  have he : Y.conjTranspose.conjTranspose = Y := by ext i j; simp
  rw [he] at hs
  have hm := rectangular_norm_mul_le_finite Y.conjTranspose Y
  nlinarith [norm_nonneg Y, norm_nonneg Y.conjTranspose]

/-- Conjugate transpose preserves every rectangular matrix norm. -/
theorem norm_conjTranspose_finite (X : CStarMatrix ι κ A) : ‖X.conjTranspose‖ = ‖X‖ := by
  apply le_antisymm (norm_conjTranspose_le_finite X)
  have h := norm_conjTranspose_le_finite X.conjTranspose
  have he : X.conjTranspose.conjTranspose = X := by ext i j; simp
  rwa [he] at h

end

end KadisonKastler

end OAI
