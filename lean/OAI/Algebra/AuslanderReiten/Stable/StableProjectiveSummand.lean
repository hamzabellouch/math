import OAI.Algebra.AuslanderReiten.Stable.StableIsomorphism

namespace OAI

namespace ArExplicit.StableIsomorphism
universe u
variable {R M P : Type u} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]

def dropRight : StableIsomorphism R (M × P) M where
  hom := StableHom.classOf R _ _ (LinearMap.fst R M P)
  inv := StableHom.classOf R _ _ (LinearMap.inl R M P)
  hom_inv_id := by
    rw [StableHom.comp_classOf]
    change StableHom.classOf R _ _ ((LinearMap.inl R M P).comp (LinearMap.fst R M P)) =
      StableHom.classOf R _ _ LinearMap.id
    rw [StableHom.classOf_eq_iff, factorsThroughFiniteFree_iff_projective]
    refine ⟨P, inferInstance, inferInstance, inferInstance, inferInstance,
      LinearMap.snd R M P, -(LinearMap.inr R M P), ?_⟩
    ext x <;> simp
  inv_hom_id := by
    rw [StableHom.comp_classOf]
    congr 1

@[simp] theorem dropRight_hom :
    (dropRight (R := R) (M := M) (P := P)).hom =
      StableHom.classOf R _ _ (LinearMap.fst R M P) := rfl

end ArExplicit.StableIsomorphism

end OAI
