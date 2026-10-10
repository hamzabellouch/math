import OAI.Algebra.AuslanderReiten.Stable.StableHomEquiv
import OAI.Algebra.AuslanderReiten.Modules.SplitModules
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Exact.Basic

namespace OAI

namespace ArExplicit

universe u

variable (R M N : Type u) [Ring R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

structure StableIsomorphism where
  hom : StableHom R M N
  inv : StableHom R N M
  hom_inv_id : StableHom.comp inv hom = StableHom.identity
  inv_hom_id : StableHom.comp hom inv = StableHom.identity

namespace StableIsomorphism

variable {R M N}
variable {P : Type u} [AddCommGroup P] [Module R P]

def refl : StableIsomorphism R M M where
  hom := StableHom.identity
  inv := StableHom.identity
  hom_inv_id := StableHom.identity_comp _
  inv_hom_id := StableHom.identity_comp _

def symm (e : StableIsomorphism R M N) : StableIsomorphism R N M where
  hom := e.inv
  inv := e.hom
  hom_inv_id := e.inv_hom_id
  inv_hom_id := e.hom_inv_id

def ofLinearEquiv (e : M ≃ₗ[R] N) : StableIsomorphism R M N where
  hom := StableHom.classOf R _ _ e.toLinearMap
  inv := StableHom.classOf R _ _ e.symm.toLinearMap
  hom_inv_id := by simp [StableHom.identity]
  inv_hom_id := by simp [StableHom.identity]

def trans (e : StableIsomorphism R M N) (f : StableIsomorphism R N P) :
    StableIsomorphism R M P where
  hom := StableHom.comp f.hom e.hom
  inv := StableHom.comp e.inv f.inv
  hom_inv_id := by
    rw [← StableHom.comp_assoc, StableHom.comp_assoc f.inv,
      f.hom_inv_id, StableHom.identity_comp, e.hom_inv_id]
  inv_hom_id := by
    rw [← StableHom.comp_assoc, StableHom.comp_assoc e.hom,
      e.inv_hom_id, StableHom.identity_comp, f.inv_hom_id]

def targetAddEquiv (e : StableIsomorphism R M N) : StableHom R P M ≃+ StableHom R P N where
  toFun := StableHom.comp e.hom
  invFun := StableHom.comp e.inv
  left_inv f := by rw [StableHom.comp_assoc, e.hom_inv_id, StableHom.identity_comp]
  right_inv f := by rw [StableHom.comp_assoc, e.inv_hom_id, StableHom.identity_comp]
  map_add' := map_add _

def sourceAddEquiv (e : StableIsomorphism R M N) : StableHom R N P ≃+ StableHom R M P where
  toFun f := StableHom.comp f e.hom
  invFun f := StableHom.comp f e.inv
  left_inv f := by
    change StableHom.comp (StableHom.comp f e.hom) e.inv = f
    rw [← StableHom.comp_assoc, e.inv_hom_id, StableHom.comp_identity]
  right_inv f := by
    change StableHom.comp (StableHom.comp f e.inv) e.hom = f
    rw [← StableHom.comp_assoc, e.hom_inv_id, StableHom.comp_identity]
  map_add' f g := by
    exact congrArg (fun a : StableHom R M N →+ StableHom R M P => a e.hom)
      (map_add (StableHom.comp (R := R) (M := M)) f g)

noncomputable def ofExactProjectiveKernel
    [Module.Finite R P] [Module.Projective R P] [Module.Injective R P]
    (i : P →ₗ[R] M) (q : M →ₗ[R] N) (hi : Function.Injective i)
    (hq : Function.Surjective q) (hex : Function.Exact i q) :
    StableIsomorphism R M N := by
  let r := Classical.choose (Module.Injective.extension_property R P P M i hi (LinearMap.id : P →ₗ[R] P))
  have hr := Classical.choose_spec (Module.Injective.extension_property R P P M i hi (LinearMap.id : P →ₗ[R] P))
  let t : M →ₗ[R] M := LinearMap.id - i.comp r
  have ht : LinearMap.ker q ≤ LinearMap.ker t := by
    intro x hx
    obtain ⟨p, rfl⟩ := (hex x).mp hx
    change i p - i (r (i p)) = 0
    rw [show r (i p) = p from DFunLike.congr_fun hr p, sub_self]
  let s : N →ₗ[R] M := ((LinearMap.ker q).liftQ t ht).comp
    (q.quotKerEquivOfSurjective hq).symm.toLinearMap
  have hs (x : M) : s (q x) = x - i (r x) := by
    simp only [s, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
    rfl
  have hqi (p : P) : q (i p) = 0 := (hex (i p)).mpr ⟨p, rfl⟩
  have hqs : q.comp s = LinearMap.id := by
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := hq y
    change q (s (q x)) = q x
    rw [hs, map_sub, hqi, sub_zero]
  refine ⟨StableHom.classOf R _ _ q, StableHom.classOf R _ _ s, ?_, ?_⟩
  · rw [StableHom.comp_classOf]
    change StableHom.classOf R M M (s.comp q) = StableHom.classOf R M M LinearMap.id
    rw [StableHom.classOf_eq_iff, factorsThroughFiniteFree_iff_projective]
    refine ⟨P, inferInstance, inferInstance, inferInstance, inferInstance, r, -i, ?_⟩
    apply LinearMap.ext
    intro x
    change -i (r x) = s (q x) - x
    rw [hs]
    abel
  · rw [StableHom.comp_classOf, hqs]
    rfl

@[simp]
theorem ofExactProjectiveKernel_hom
    [Module.Finite R P] [Module.Projective R P] [Module.Injective R P]
    (i : P →ₗ[R] M) (q : M →ₗ[R] N) (hi : Function.Injective i)
    (hq : Function.Surjective q) (hex : Function.Exact i q) :
    (ofExactProjectiveKernel i q hi hq hex).hom = StableHom.classOf R _ _ q := by
  rfl

end StableIsomorphism
end ArExplicit

end OAI
