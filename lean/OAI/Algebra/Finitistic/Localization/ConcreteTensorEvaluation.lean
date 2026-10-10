import OAI.Algebra.Finitistic.Localization.SourceVerdier
import OAI.Algebra.Finitistic.Rectification.VertexTensorEvaluation
import OAI.Algebra.Finitistic.Localization.TensorEvaluationFunctor

namespace OAI
noncomputable section
open CategoryTheory Limits Category
namespace LittleFinitistic.ConcreteTensorEvaluation
open QuadraticEncoding
universe u
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type u} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

/-- Match the opposite-regular presentation of eB to the fixed-point presentation. -/
def idealEquiv (e : B P) (he : e*e=e) :
    VertexProjectives.ideal e ≃ₗ[(B P)ᵐᵒᵖ] IdempotentTensor.rightIdeal e where
  toFun x := ⟨x.val.unop, by
    exact congrArg MulOpposite.unop (VertexProjectives.fixed e he x)⟩
  invFun x := ⟨MulOpposite.op x.val, ⟨MulOpposite.op x.val, by
    change MulOpposite.op x.val * MulOpposite.op e = MulOpposite.op x.val
    exact congrArg MulOpposite.op x.property⟩⟩
  left_inv x := by rfl
  right_inv x := by rfl
  map_add' x y := rfl
  map_smul' a x := rfl

section TensorCongr
variable {A : Type u} [Ring A] [Algebra k A]
variable {M M' N : Type u} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N]
variable [Module k M] [Module k M'] [Module k N]
variable [Module Aᵐᵒᵖ M] [Module Aᵐᵒᵖ M'] [Module A N]
variable [IsScalarTower k Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M']

/-- Balanced tensor respects actual right-module equivalences. -/
def tensorCongr (e : M ≃ₗ[Aᵐᵒᵖ] M') :
    BalancedTensor.Tensor k A M N ≃ₗ[k] BalancedTensor.Tensor k A M' N where
  __ := BalancedTensor.mapLeft (k := k) N e.toLinearMap
  invFun := BalancedTensor.mapLeft (k := k) N e.symm.toLinearMap
  left_inv z := by
    change BalancedTensor.mapLeft (k := k) N e.symm.toLinearMap
      (BalancedTensor.mapLeft (k := k) N e.toLinearMap z) = z
    induction z using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => simp
    | ha a b ha hb =>
      simp only [map_add]
      exact congrArg₂ (· + ·) ha hb
  right_inv z := by
    change BalancedTensor.mapLeft (k := k) N e.toLinearMap
      (BalancedTensor.mapLeft (k := k) N e.symm.toLinearMap z) = z
    induction z using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => simp
    | ha a b ha hb =>
      simp only [map_add]
      exact congrArg₂ (· + ·) ha hb
end TensorCongr

/-- Actual tensor evaluation on projectives. -/
abbrev moduleEvaluation : SourceVerdier.Proj P ⥤ ModuleCat.{u} k :=
  (ProjectiveComplexes.finiteProjective (B P)).ι ⋙
    BalancedTensor.tensorFunctor k (B P) X.Evaluation

instance vertexScalarTower (i : Fin 3) :
    IsScalarTower k (B P)ᵐᵒᵖ (BalancedTensor.ScalarModule k (B P) (SourceVerdier.E P i).obj) :=
  BalancedTensor.scalarModuleTower k (B P) (SourceVerdier.E P i).obj

/-- The exact natural vertex identification E_i tensor_B M(Y) = Y. -/
def vertexIso (i : Fin 3) : (moduleEvaluation X).obj (SourceVerdier.E P i) ≅ ModuleCat.of k Y :=
  ((@tensorCongr k _ (B P) _ _
    (BalancedTensor.ScalarModule k (B P) (SourceVerdier.E P i).obj)
    (IdempotentTensor.rightIdeal (SourceVerdier.vertex P i)) X.Evaluation
    _ _ _ (BalancedTensor.ScalarModule k (B P) (SourceVerdier.E P i).obj).isModule _ _
    _ _ _ (vertexScalarTower (P := P) i) inferInstance
    (idealEquiv (SourceVerdier.vertex P i) (SourceVerdier.vertex_idem P i))).trans
      (X.vertexTensorEquiv i)).toModuleIso

@[simp] theorem vertexIso_mk (i : Fin 3)
    (m : BalancedTensor.ScalarModule k (B P) (SourceVerdier.E P i).obj) (y : X.Evaluation) :
    (vertexIso X i).hom.hom
      (BalancedTensor.mk k (B P) _ X.Evaluation m y) = X.projection i (m.val.unop • y) := rfl

/-- The two actual identity-arrow tensor maps become identities on Y. -/
theorem s_naturality :
    (moduleEvaluation X).map (SourceVerdier.arrow01 P 0) ≫ (vertexIso X 1).hom =
      (vertexIso X 0).hom := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.ext
  intro m y
  change X.projection 1 ((m.val * MulOpposite.op (QuadraticEncoding.arrow01 P 0)).unop • y) =
    X.projection 0 (m.val.unop • y)
  rw [MulOpposite.unop_mul, MulOpposite.unop_op, mul_smul, X.arrow01_smul]
  simp [Representation.projection]

theorem s'_naturality :
    (moduleEvaluation X).map (SourceVerdier.arrow12 P 0) ≫ (vertexIso X 2).hom =
      (vertexIso X 1).hom := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.ext
  intro m y
  change X.projection 2 ((m.val * MulOpposite.op (QuadraticEncoding.arrow12 P 0)).unop • y) =
    X.projection 1 (m.val.unop • y)
  rw [MulOpposite.unop_mul, MulOpposite.unop_op, mul_smul, X.arrow12_smul]
  simp [Representation.projection]

instance s_inverted : IsIso ((moduleEvaluation X).map (SourceVerdier.arrow01 P 0)) := by
  have : IsIso ((moduleEvaluation X).map (SourceVerdier.arrow01 P 0) ≫ (vertexIso X 1).hom) := by
    rw [s_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (vertexIso X 1).hom

instance s'_inverted : IsIso ((moduleEvaluation X).map (SourceVerdier.arrow12 P 0)) := by
  have : IsIso ((moduleEvaluation X).map (SourceVerdier.arrow12 P 0) ≫ (vertexIso X 2).hom) := by
    rw [s'_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (vertexIso X 2).hom

end LittleFinitistic.ConcreteTensorEvaluation

end

end OAI
