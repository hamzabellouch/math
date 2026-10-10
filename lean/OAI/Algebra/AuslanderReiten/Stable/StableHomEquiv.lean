import OAI.Algebra.AuslanderReiten.Stable.StableHom

namespace OAI

namespace ArExplicit.StableHom

universe u

variable {k R : Type u} [CommRing k] [Ring R] [Algebra k R]
variable {M M' N N' : Type u}
variable [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
variable [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
variable [AddCommGroup N'] [Module R N'] [Module k N'] [IsScalarTower k R N']

def sourceEquiv (e : M ≃ₗ[R] M') : StableHom R M' N ≃ₗ[k] StableHom R M N where
  toFun := precomp e.toLinearMap
  invFun := precomp e.symm.toLinearMap
  left_inv f := by
    obtain ⟨f, rfl⟩ := classOf_surjective f
    simp only [precomp_classOf]
    congr 1
    ext x
    simp
  right_inv f := by
    obtain ⟨f, rfl⟩ := classOf_surjective f
    simp only [precomp_classOf]
    congr 1
    ext x
    simp
  map_add' := map_add _
  map_smul' c f := by
    obtain ⟨f, rfl⟩ := classOf_surjective f
    rw [← classOf_smul k, precomp_classOf, precomp_classOf, ← classOf_smul k]
    rfl

def targetEquiv (e : N ≃ₗ[R] N') : StableHom R M N ≃ₗ[k] StableHom R M N' where
  toFun := postcomp e.toLinearMap
  invFun := postcomp e.symm.toLinearMap
  left_inv f := by
    obtain ⟨f, rfl⟩ := classOf_surjective f
    simp only [postcomp_classOf]
    congr 1
    ext x
    simp
  right_inv f := by
    obtain ⟨f, rfl⟩ := classOf_surjective f
    simp only [postcomp_classOf]
    congr 1
    ext x
    simp
  map_add' := map_add _
  map_smul' c f := by
    obtain ⟨f, rfl⟩ := classOf_surjective f
    rw [← classOf_smul k, postcomp_classOf, postcomp_classOf, ← classOf_smul k]
    congr 1
    exact LinearMap.comp_smul _ _ _

@[simp]
theorem sourceEquiv_classOf (e : M ≃ₗ[R] M') (f : M' →ₗ[R] N) :
    sourceEquiv (k := k) e (classOf R M' N f) = classOf R M N (f.comp e.toLinearMap) :=
  precomp_classOf _ _

@[simp]
theorem targetEquiv_classOf (e : N ≃ₗ[R] N') (f : M →ₗ[R] N) :
    targetEquiv (k := k) e (classOf R M N f) = classOf R M N' (e.toLinearMap.comp f) :=
  postcomp_classOf _ _

end ArExplicit.StableHom

end OAI
