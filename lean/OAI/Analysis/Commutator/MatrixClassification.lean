import Mathlib
import OAI.Analysis.Commutator.MatrixModules

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.MatrixModules

open Matrix

variable {𝕜 I K R : Type*} [Field 𝕜]
  [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
  [Fintype R] [DecidableEq R]

variable (φ : Matrix I I 𝕜 →ₐ[𝕜] Matrix K K 𝕜) (o : I)

abbrev matrixRepresentation : Matrix I I 𝕜 →ₐ[𝕜] Module.End 𝕜 (K → 𝕜) :=
  Matrix.toLinAlgEquiv'.toAlgHom.comp φ

noncomputable def coordinateEquiv
    (b : Module.Basis R 𝕜 (corner (matrixRepresentation φ) o)) :
    (I × R → 𝕜) ≃ₗ[𝕜] (K → 𝕜) := representationEquiv (matrixRepresentation φ) o b

noncomputable def forwardMatrix
    (b : Module.Basis R 𝕜 (corner (matrixRepresentation φ) o)) : Matrix K (I × R) 𝕜 :=
  LinearMap.toMatrix' (coordinateEquiv φ o b).toLinearMap

noncomputable def backwardMatrix
    (b : Module.Basis R 𝕜 (corner (matrixRepresentation φ) o)) : Matrix (I × R) K 𝕜 :=
  LinearMap.toMatrix' (coordinateEquiv φ o b).symm.toLinearMap

lemma backward_forward
    (b : Module.Basis R 𝕜 (corner (matrixRepresentation φ) o)) :
    backwardMatrix φ o b * forwardMatrix φ o b = 1 := by
  unfold backwardMatrix forwardMatrix
  rw [← LinearMap.toMatrix'_comp]
  have h : (coordinateEquiv φ o b).symm.toLinearMap.comp
      (coordinateEquiv φ o b).toLinearMap = LinearMap.id := by ext x; simp
  rw [h, LinearMap.toMatrix'_id]

lemma forward_backward
    (b : Module.Basis R 𝕜 (corner (matrixRepresentation φ) o)) :
    forwardMatrix φ o b * backwardMatrix φ o b = 1 := by
  unfold backwardMatrix forwardMatrix
  rw [← LinearMap.toMatrix'_comp]
  have h : (coordinateEquiv φ o b).toLinearMap.comp
      (coordinateEquiv φ o b).symm.toLinearMap = LinearMap.id := by ext x; simp
  rw [h, LinearMap.toMatrix'_id]

lemma classification
    (b : Module.Basis R 𝕜 (corner (matrixRepresentation φ) o)) (a : Matrix I I 𝕜) :
    φ a = (HMul.hMul (self := Matrix.instHMulOfFintypeOfMulOfAddCommMonoid)
      (forwardMatrix φ o b) (inflate (R := R) a) : Matrix K (I × R) 𝕜) * backwardMatrix φ o b := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, forwardMatrix, backwardMatrix,
    Matrix.toLin'_toMatrix', LinearEquiv.coe_coe]
  change (matrixRepresentation φ a) x = _
  have h := representationEquiv_intertwines (matrixRepresentation φ) o b a
    ((coordinateEquiv φ o b).symm x)
  simpa only [coordinateEquiv, LinearEquiv.apply_symm_apply, Matrix.toLin'_apply] using h

omit [DecidableEq R] in
lemma dimensions
    (b : Module.Basis R 𝕜 (corner (matrixRepresentation φ) o)) :
    Fintype.card I * Fintype.card R = Fintype.card K := by
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod] using
    (coordinateEquiv φ o b).finrank_eq

omit [DecidableEq R] in
lemma multiplicity_nonempty [Nonempty K]
    (b : Module.Basis R 𝕜 (corner (matrixRepresentation φ) o)) : Nonempty R := by
  apply Fintype.card_pos_iff.mp
  have h := dimensions φ o b
  have hK := Fintype.card_pos (α := K)
  nlinarith

end Kadison.MatrixModules
end

end OAI
