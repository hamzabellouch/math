import OAI.Algebra.Finitistic.Ordinary.OrdinaryFreeTensorExactness
import OAI.Algebra.Finitistic.Ordinary.OrdinaryFixedTensorFunctor
import OAI.Algebra.Finitistic.Tensor.BalancedTensorMaps
import Mathlib.Algebra.Module.Projective

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BalancedTensor
universe u
variable {k A M M' : Type u} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
variable [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M'] [IsScalarTower k Aᵐᵒᵖ M']
variable {N N' N'' : Type u}
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable [AddCommGroup N'] [Module k N'] [Module A N'] [IsScalarTower k A N']
variable [AddCommGroup N''] [Module k N''] [Module A N''] [IsScalarTower k A N'']

theorem mapLeft_mapRightTo (i : M →ₗ[Aᵐᵒᵖ] M') (f : N →ₗ[A] N') (z : Tensor k A M N) :
    mapLeft N' i (mapRightTo f z) = mapRightTo f (mapLeft N i z) := by
  induction z using BalancedTensor.induction_on with
  | hz => simp only [map_zero]
  | ht m n => rfl
  | ha x y hx hy => simp only [map_add,hx,hy]

omit [IsScalarTower k A N] in
theorem mapLeft_split (i : M →ₗ[Aᵐᵒᵖ] M') (p : M' →ₗ[Aᵐᵒᵖ] M)
    (hp : p.comp i = LinearMap.id) (z : Tensor k A M N) :
    mapLeft N p (mapLeft N i z) = z := by
  have hm := congrArg (fun f : Tensor k A M N →ₗ[k] Tensor k A M N => f z)
    (mapLeft_comp (k := k) N i p).symm
  simpa only [hp,mapLeft_id,LinearMap.id_apply,LinearMap.comp_apply] using hm

/-- Exactness descends through an actual split right-module retract. -/
theorem tensor_exact_of_split (i : M →ₗ[Aᵐᵒᵖ] M') (p : M' →ₗ[Aᵐᵒᵖ] M)
    (hp : p.comp i = LinearMap.id) (f : N →ₗ[A] N') (g : N' →ₗ[A] N'')
    (h : Function.Exact f g)
    (h' : Function.Exact (mapRightTo (k := k) (M := M') f) (mapRightTo (k := k) (M := M') g)) :
    Function.Exact (mapRightTo (k := k) (M := M) f) (mapRightTo (k := k) (M := M) g) := by
  intro z
  constructor
  · intro hz
    have hi : mapRightTo g (mapLeft N' i z) = 0 := by
      rw [← mapLeft_mapRightTo,hz,map_zero]
    obtain ⟨y,hy⟩ := (h' _).mp hi
    refine ⟨mapLeft N p y, ?_⟩
    rw [← mapLeft_mapRightTo,hy,mapLeft_split i p hp]
  · rintro ⟨y,rfl⟩
    induction y using BalancedTensor.induction_on with
    | hz => simp only [map_zero]
    | ht m n => rw [mapRightTo_mk,mapRightTo_mk,(h (f n)).mpr ⟨n,rfl⟩,map_zero]
    | ha x y hx hy => simp only [map_add,hx,hy,add_zero]

/-- Projectivity of the actual right module suffices, with no hypothesis on the left modules. -/
theorem projectiveTensor_exact [Module.Projective Aᵐᵒᵖ M]
    (f : N →ₗ[A] N') (g : N' →ₗ[A] N'') (h : Function.Exact f g) :
    Function.Exact (mapRightTo (k := k) (M := M) f) (mapRightTo (k := k) (M := M) g) := by
  obtain ⟨i,hi⟩ := (Module.projective_def' (R := Aᵐᵒᵖ) (P := M)).mp inferInstance
  exact tensor_exact_of_split i (Finsupp.linearCombination Aᵐᵒᵖ id) hi f g h
    (Free.tensor_exact (k := k) M f g h)

variable (k A M)

theorem projectiveTensor_mapsExact [Module.Projective Aᵐᵒᵖ M]
    (S : ShortComplex (ModuleCat.{u} A)) (hS : S.Exact) :
    (S.map (fixedTensorFunctor k A M)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  have h : Function.Exact
      (S.f.hom : ScalarLeftModule k A S.X₁ →ₗ[A] ScalarLeftModule k A S.X₂)
      (S.g.hom : ScalarLeftModule k A S.X₂ →ₗ[A] ScalarLeftModule k A S.X₃) := by
    intro n
    constructor
    · exact (ShortComplex.moduleCat_exact_iff S).mp hS n
    · rintro ⟨m,rfl⟩
      exact congrArg (fun f => f.hom m) S.zero
  have ht := @projectiveTensor_exact k A M _ _ _ _ _ _ _
    (ScalarLeftModule k A S.X₁) (ScalarLeftModule k A S.X₂) (ScalarLeftModule k A S.X₃)
    _ _ _ (scalarLeftTower k A S.X₁)
    _ _ _ (scalarLeftTower k A S.X₂) _ _ _ (scalarLeftTower k A S.X₃)
    _ S.f.hom S.g.hom h
  intro z hz
  exact (ht z).mp hz

theorem projectiveTensor_preservesHomology [Module.Projective Aᵐᵒᵖ M] :
    (fixedTensorFunctor k A M).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (projectiveTensor_mapsExact k A M)

/-- Degree-zero projective tensor preserves quasi-isomorphisms of arbitrary complexes. -/
theorem projectiveTensor_quasiIso [Module.Projective Aᵐᵒᵖ M]
    {Z Z' : CochainComplex (ModuleCat.{u} A) ℤ} (f : Z ⟶ Z') [QuasiIso f] :
    QuasiIso (((fixedTensorFunctor k A M).mapHomologicalComplex (.up ℤ)).map f) := by
  let := projectiveTensor_preservesHomology k A M
  infer_instance
end LittleFinitistic.BalancedTensor

end

end OAI
