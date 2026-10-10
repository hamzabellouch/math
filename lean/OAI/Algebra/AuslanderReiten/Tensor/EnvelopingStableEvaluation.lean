import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingBalancedProjective
import OAI.Algebra.AuslanderReiten.Stable.StableHom
import Mathlib.Algebra.Category.ModuleCat.Algebra

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace ArExplicit.EnvelopingBimodule
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (X : ModuleCat.{u} R) [Module k X] [IsScalarTower k R X]
variable {M N P : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)}
variable [Module k M] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) M]
variable [Module k N] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) N]
variable [Module k P] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) P]

omit [IsScalarTower k R X] in
theorem tensorMap_smul_linear (c : k) (f : M →ₗ[R ⊗[k] Rᵐᵒᵖ] N) :
    tensorMap X (ModuleCat.ofHom (c • f)) = c • tensorMap X (ModuleCat.ofHom f) := by
  have hm : map (ModuleCat.ofHom (c • f)) = c • map (ModuleCat.ofHom f) := by
    apply LinearMap.ext
    intro z
    rfl
  apply LinearMap.ext
  intro z
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | add z w hz hw => simp_all
  | tmul m x => simp only [tensorMap_tmul, hm, LinearMap.smul_apply,
      BalancedTensor.scalar_tmul]

def tensorHom : (M →ₗ[R ⊗[k] Rᵐᵒᵖ] N) →ₗ[k]
    (BalancedTensor k R (EnvelopingBimodule k R M) X →ₗ[R]
      BalancedTensor k R (EnvelopingBimodule k R N) X) where
  toFun f := tensorMap X (ModuleCat.ofHom f)
  map_add' _ _ := tensorMap_add X _ _
  map_smul' := tensorMap_smul_linear X

variable [Module.Finite k R] [Module.Finite k X]

theorem tensorHom_projective {f : M →ₗ[R ⊗[k] Rᵐᵒᵖ] N}
    (hf : FactorsThroughFiniteProjective (R ⊗[k] Rᵐᵒᵖ) M N f) :
    FactorsThroughFiniteProjective R
      (BalancedTensor k R (EnvelopingBimodule k R M) X)
      (BalancedTensor k R (EnvelopingBimodule k R N) X) (tensorHom X f) := by
  obtain ⟨Q, hQ, hAQ, hp, hfin, i, p, rfl⟩ := hf
  let Q' : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ) := ModuleCat.of _ Q
  let : Module k Q := ModuleCat.moduleOfAlgebraModule Q'
  let : IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) Q := ModuleCat.isScalarTower_of_algebra_moduleCat Q'
  let : Module.Finite k Q := Module.Finite.trans (R ⊗[k] Rᵐᵒᵖ) Q
  let : Module.Finite k (BalancedTensor k R (EnvelopingBimodule k R Q') X) := inferInstance
  let : Module.Finite R (BalancedTensor k R (EnvelopingBimodule k R Q') X) :=
    Module.Finite.of_restrictScalars_finite k R _
  refine ⟨BalancedTensor k R (EnvelopingBimodule k R Q') X,
    inferInstance, inferInstance, tensor_projective X Q', inferInstance,
    tensorMap X (ModuleCat.ofHom i), tensorMap X (ModuleCat.ofHom p), ?_⟩
  exact (tensorMap_comp X (ModuleCat.ofHom i) (ModuleCat.ofHom p)).symm

def stableEvaluation : StableHom (R ⊗[k] Rᵐᵒᵖ) M N →+
    StableHom R (BalancedTensor k R (EnvelopingBimodule k R M) X)
      (BalancedTensor k R (EnvelopingBimodule k R N) X) :=
  QuotientAddGroup.map _ _ (tensorHom (k := k) (M := M) (N := N) X).toAddMonoidHom (by
    intro f hf
    exact (factorsThroughFiniteFree_iff_projective _).mpr
      (tensorHom_projective X ((factorsThroughFiniteFree_iff_projective _).mp hf)))

@[simp]
theorem stableEvaluation_classOf (f : M →ₗ[R ⊗[k] Rᵐᵒᵖ] N) :
    stableEvaluation X (StableHom.classOf _ _ _ f) =
      StableHom.classOf R _ _ (tensorMap X (ModuleCat.ofHom f)) :=
  QuotientAddGroup.map_mk' _ _ _ _ _

def stableEvaluationLinear : StableHom (R ⊗[k] Rᵐᵒᵖ) M N →ₗ[k]
    StableHom R (BalancedTensor k R (EnvelopingBimodule k R M) X)
      (BalancedTensor k R (EnvelopingBimodule k R N) X) where
  __ := stableEvaluation X
  map_smul' c f := by
    obtain ⟨f, rfl⟩ := StableHom.classOf_surjective f
    change stableEvaluation X (c • StableHom.classOf _ _ _ f) =
      c • stableEvaluation X (StableHom.classOf _ _ _ f)
    rw [← StableHom.classOf_smul, stableEvaluation_classOf, stableEvaluation_classOf,
      tensorMap_smul_linear, StableHom.classOf_smul]

@[simp]
theorem stableEvaluation_id : stableEvaluation X
    (StableHom.classOf _ M M LinearMap.id) =
      StableHom.classOf R _ _ LinearMap.id := by
  rw [stableEvaluation_classOf]
  exact congrArg (StableHom.classOf R _ _) (tensorMap_id X)

theorem stableEvaluation_comp (f : StableHom (R ⊗[k] Rᵐᵒᵖ) M N)
    (g : StableHom (R ⊗[k] Rᵐᵒᵖ) N P) :
    stableEvaluation X (StableHom.comp g f) =
      StableHom.comp (stableEvaluation X g) (stableEvaluation X f) := by
  obtain ⟨f, rfl⟩ := StableHom.classOf_surjective f
  obtain ⟨g, rfl⟩ := StableHom.classOf_surjective g
  rw [StableHom.comp_classOf, stableEvaluation_classOf, stableEvaluation_classOf,
    stableEvaluation_classOf, StableHom.comp_classOf]
  exact congrArg (StableHom.classOf R _ _)
    (tensorMap_comp X (ModuleCat.ofHom f) (ModuleCat.ofHom g))

end ArExplicit.EnvelopingBimodule

end

end OAI
