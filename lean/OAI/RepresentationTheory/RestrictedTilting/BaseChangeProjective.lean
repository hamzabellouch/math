import Mathlib

namespace OAI

namespace FiberFunctorProof
open scoped TensorProduct
variable {R S M F : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup F] [Module R F]

 

theorem projective_baseChange_of_split_smul [Module.Projective R F]
    (f : M →ₗ[R] F) (g : F →ₗ[R] M) (a : R)
    (h : g.comp f = a • LinearMap.id) (ha : IsUnit (algebraMap R S a)) :
    Module.Projective S (S ⊗[R] M) := by
  have hb : (g.baseChange S).comp (f.baseChange S) =
      algebraMap R S a • LinearMap.id := by
    rw [← LinearMap.baseChange_comp, h, LinearMap.baseChange_smul,
      LinearMap.baseChange_id, algebraMap_smul]
  obtain ⟨u,hu⟩ := ha
  refine Module.Projective.of_split ((↑u⁻¹ : S) • f.baseChange S) (g.baseChange S) ?_
  rw [LinearMap.comp_smul, hb, ← hu, smul_smul]
  simp

end FiberFunctorProof

end OAI
