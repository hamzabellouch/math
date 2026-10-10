import Mathlib
import OAI.Analysis.Commutator.PaulsenDilation

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators CStarAlgebra

namespace Kadison.CbFactor

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def HasMatrixBound (f : A →ₗ[ℂ] (H →L[ℂ] H)) (c : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (X : CStarMatrix ι ι A),‖CStarMatrix.mapₗ f X‖≤c*‖X‖

lemma normalized_contracts (f : A →ₗ[ℂ] (H →L[ℂ] H)) {c : ℝ} (hc : 0<c)
    (hf : HasMatrixBound f c) : Paulsen.IsCompletelyContractive ((c⁻¹ : ℂ) • f) := by
  intro ι _ X
  have he : CStarMatrix.mapₗ ((c⁻¹ : ℂ) • f) X=(c⁻¹ : ℂ) • CStarMatrix.mapₗ f X := by
    ext i j
    rfl
  rw [he,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc]
  calc
    c⁻¹*‖CStarMatrix.mapₗ f X‖≤c⁻¹*(c*‖X‖) :=
      mul_le_mul_of_nonneg_left (hf ι X) (inv_nonneg.mpr hc.le)
    _ = ‖X‖ := by rw [←mul_assoc,inv_mul_cancel₀ hc.ne',one_mul]

variable [Nontrivial A] (f : A →ₗ[ℂ] (H →L[ℂ] H)) (c : ℝ) (hc : 0<c) (hf : HasMatrixBound f c)

abbrev Space := Paulsen.DilationSpace ((c⁻¹ : ℂ) • f) (normalized_contracts f hc hf)

def representation : A →⋆ₐ[ℂ] (Space f c hc hf →L[ℂ] Space f c hc hf) :=
  Paulsen.dilationRepresentation ((c⁻¹ : ℂ) • f) (normalized_contracts f hc hf)

def leftOperator : H →L[ℂ] Space f c hc hf :=
  Paulsen.leftOperator ((c⁻¹ : ℂ) • f) (normalized_contracts f hc hf)

def rightOperator : H →L[ℂ] Space f c hc hf :=
  (c : ℂ) • Paulsen.rightOperator ((c⁻¹ : ℂ) • f) (normalized_contracts f hc hf)

lemma factorization (a : A) :
    f a=(leftOperator f c hc hf).adjoint.comp
      ((representation f c hc hf a).comp (rightOperator f c hc hf)) := by
  dsimp only [leftOperator,representation,rightOperator]
  rw [ContinuousLinearMap.comp_smul,ContinuousLinearMap.comp_smul,
    ←Paulsen.dilation_factorization]
  simp only [LinearMap.smul_apply,smul_smul]
  rw [mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne'),one_smul]

lemma leftOperator_norm_le : ‖leftOperator f c hc hf‖≤1 :=
  Paulsen.leftOperator_norm_le_one _ _

lemma rightOperator_norm_le : ‖rightOperator f c hc hf‖≤c := by
  unfold rightOperator
  have h := ContinuousLinearMap.opNorm_smul_le (c : ℂ)
    (Paulsen.rightOperator ((c⁻¹ : ℂ) • f) (normalized_contracts f hc hf))
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (Paulsen.rightOperator_norm_le_one _ _) hc.le).trans_eq (mul_one c))

end Kadison.CbFactor

end

end
end

end OAI
