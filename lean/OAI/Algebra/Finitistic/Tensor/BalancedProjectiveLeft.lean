import OAI.Algebra.Finitistic.Tensor.BalancedFreeLeft
import OAI.Algebra.Finitistic.Ordinary.OrdinaryProjectiveTensor
import OAI.Algebra.Finitistic.Bimodule.BimoduleTensorFunctor

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BalancedTensor
universe u
variable {k A M M' M'' N N' : Type u} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
variable [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M'] [IsScalarTower k Aᵐᵒᵖ M']
variable [AddCommGroup M''] [Module k M''] [Module Aᵐᵒᵖ M''] [IsScalarTower k Aᵐᵒᵖ M'']
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable [AddCommGroup N'] [Module k N'] [Module A N'] [IsScalarTower k A N']

omit [IsScalarTower k Aᵐᵒᵖ M] in
theorem mapRightTo_split (i : N →ₗ[A] N') (p : N' →ₗ[A] N)
    (hp : p.comp i = LinearMap.id) (z : Tensor k A M N) :
    mapRightTo p (mapRightTo i z) = z := by
  induction z using BalancedTensor.induction_on with
  | hz => simp
  | ht m n =>
    rw [mapRightTo_mk,mapRightTo_mk]
    exact congrArg (mk k A M N m) (LinearMap.congr_fun hp n)
  | ha x y hx hy => simp only [map_add,hx,hy]

theorem leftTensor_exact_of_split (i : N →ₗ[A] N') (p : N' →ₗ[A] N)
    (hp : p.comp i = LinearMap.id) (f : M →ₗ[Aᵐᵒᵖ] M') (g : M' →ₗ[Aᵐᵒᵖ] M'')
    (h : Function.Exact f g)
    (h' : Function.Exact (mapLeft (k := k) N' f) (mapLeft (k := k) N' g)) :
    Function.Exact (mapLeft (k := k) N f) (mapLeft (k := k) N g) := by
  intro z
  constructor
  · intro hz
    have hi : mapLeft N' g (mapRightTo i z) = 0 := by
      rw [mapLeft_mapRightTo,hz,map_zero]
    obtain ⟨y,hy⟩ := (h' _).mp hi
    refine ⟨mapRightTo p y, ?_⟩
    rw [mapLeft_mapRightTo,hy,mapRightTo_split i p hp]
  · rintro ⟨y,rfl⟩
    induction y using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => rw [mapLeft_mk,mapLeft_mk,(h (f m)).mpr ⟨m,rfl⟩,map_zero,LinearMap.zero_apply]
    | ha x y hx hy => simp only [map_add,hx,hy,add_zero]

/-- Projectivity of the left input preserves every exact sequence in the right variable. -/
theorem projectiveLeftTensor_exact [Module.Projective A N]
    (f : M →ₗ[Aᵐᵒᵖ] M') (g : M' →ₗ[Aᵐᵒᵖ] M'') (h : Function.Exact f g) :
    Function.Exact (mapLeft (k := k) N f) (mapLeft (k := k) N g) := by
  obtain ⟨i,hi⟩ := (Module.projective_def' (R := A) (P := N)).mp inferInstance
  exact leftTensor_exact_of_split i (Finsupp.linearCombination A id) hi f g h
    (FreeLeft.tensor_exact (k := k) N f g h)
end LittleFinitistic.BalancedTensor

namespace LittleFinitistic.BimoduleBalancedTensor
open ExternalTensor.Section4
universe u
variable (k B N : Type u) [Field k] [Ring B] [Algebra k B]
variable [AddCommGroup N] [Module k N] [Module B N] [IsScalarTower k B N]
variable [Module.Projective B N]

/-- Exactness of tensoring genuine bimodules with a projective left module,
with the result still in B-Mod. -/
theorem projectiveInput_mapsExact
    (S : ShortComplex (ModuleCat.{u} (Enveloping k B))) (hS : S.Exact) :
    (S.map (functor k B N)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  have h : Function.Exact
      (((forgetRight k B).map S.f).hom : Input k B S.X₁ →ₗ[Bᵐᵒᵖ] Input k B S.X₂)
      (((forgetRight k B).map S.g).hom : Input k B S.X₂ →ₗ[Bᵐᵒᵖ] Input k B S.X₃) := by
    intro x
    constructor
    · exact (ShortComplex.moduleCat_exact_iff S).mp hS x
    · rintro ⟨y,rfl⟩
      exact congrArg (fun t => t.hom y) S.zero
  intro z hz
  exact ((BalancedTensor.projectiveLeftTensor_exact (k := k) (N := N)
    (((forgetRight k B).map S.f).hom : Input k B S.X₁ →ₗ[Bᵐᵒᵖ] Input k B S.X₂)
    (((forgetRight k B).map S.g).hom : Input k B S.X₂ →ₗ[Bᵐᵒᵖ] Input k B S.X₃) h) z).mp hz

theorem projectiveInput_preservesHomology : (functor k B N).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (projectiveInput_mapsExact k B N)

/-- An actual bimodule augmentation quasi-isomorphism remains one on each projective input row. -/
theorem projectiveInput_quasiIso {P Q : BiComplex k B} (ε : P ⟶ Q) [QuasiIso ε] :
    QuasiIso (((functor k B N).mapHomologicalComplex (.up ℤ)).map ε) := by
  have := projectiveInput_preservesHomology k B N
  infer_instance
end LittleFinitistic.BimoduleBalancedTensor

end

end OAI
