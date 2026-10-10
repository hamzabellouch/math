import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorExactness
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.QuasiIso

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BalancedTensor
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]

abbrev ScalarLeftModule (N : ModuleCat.{u} A) :=
  (ModuleCat.restrictScalars (algebraMap k A)).obj N

instance scalarLeftTower (N : ModuleCat.{u} A) : IsScalarTower k A (ScalarLeftModule k A N) where
  smul_assoc r a n := by
    change (r • a) • (n : N) = algebraMap k A r • (a • (n : N))
    rw [Algebra.smul_def,mul_smul]

variable (M : Type u) [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]

/-- Tensor by a fixed actual right module on every left module. -/
def fixedTensorFunctor : ModuleCat.{u} A ⥤ ModuleCat.{u} k where
  obj N := ModuleCat.of k (Tensor k A M (ScalarLeftModule k A N))
  map {N N'} f := ModuleCat.ofHom
    (mapRightTo (k := k) (M := M) (N := ScalarLeftModule k A N) (N' := ScalarLeftModule k A N') f.hom)
  map_id N := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.ext
    intro m n
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.ext
    intro m n
    rfl

instance fixedTensorFunctor_additive : (fixedTensorFunctor k A M).Additive where
  map_add {N N'} {f g} := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.ext
    intro m n
    exact (mk k A M (ScalarLeftModule k A N') m).map_add (f.hom n) (g.hom n)

variable (e : A) (he : e*e=e)

include he in
theorem idempotentTensor_mapsExact (S : ShortComplex (ModuleCat.{u} A)) (hS : S.Exact) :
    (S.map (fixedTensorFunctor k A (IdempotentTensor.rightIdeal e))).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  have h : Function.Exact
      (S.f.hom : ScalarLeftModule k A S.X₁ →ₗ[A] ScalarLeftModule k A S.X₂)
      (S.g.hom : ScalarLeftModule k A S.X₂ →ₗ[A] ScalarLeftModule k A S.X₃) := by
    intro n
    constructor
    · exact (ShortComplex.moduleCat_exact_iff S).mp hS n
    · rintro ⟨m,rfl⟩
      exact congrArg (fun f => f.hom m) S.zero
  have ht := @IdempotentTensor.tensor_exact k A
    (ScalarLeftModule k A S.X₁) (ScalarLeftModule k A S.X₂) (ScalarLeftModule k A S.X₃)
    _ _ _ _ _ _ (scalarLeftTower k A S.X₁)
    _ _ _ (scalarLeftTower k A S.X₂) _ _ _ (scalarLeftTower k A S.X₃)
    e he S.f.hom S.g.hom h
  intro z hz
  exact (ht z).mp hz

include he in
/-- Derived input complexes remain arbitrary: this functor preserves homology. -/
theorem idempotentTensor_preservesHomology :
    (fixedTensorFunctor k A (IdempotentTensor.rightIdeal e)).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (idempotentTensor_mapsExact k A e he)

include he in
/-- No boundedness, dimension, projectivity, or flatness hypothesis on either input complex. -/
theorem idempotentTensor_quasiIso
    {Z Z' : CochainComplex (ModuleCat.{u} A) ℤ} (f : Z ⟶ Z') [QuasiIso f] :
    QuasiIso (((fixedTensorFunctor k A (IdempotentTensor.rightIdeal e)).mapHomologicalComplex (.up ℤ)).map f) := by
  let := idempotentTensor_preservesHomology k A e he
  infer_instance
end LittleFinitistic.BalancedTensor

end

end OAI
