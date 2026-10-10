import OAI.GroupTheory.PolycyclicRecognition.Algebra.RankOneRepresentation

namespace OAI

/-! # Integral endomorphisms of a rank-one representation -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] (D : Rep ℤ G) (e : D.V ≃ₗ[ℤ] ℤ)

def rankOneEndomorphismsEquiv : (D ⟶ D) ≃ₗ[ℤ] ℤ := by
  let a : (D ⟶ D) ≃+ ℤ := {
    toFun := fun f => e (f.hom (e.symm 1))
    invFun := fun z => z • (𝟙 D : D ⟶ D)
    left_inv := fun f => by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      ext x
      apply e.injective
      have hf := integralEnd_apply (e.conj f.hom.toLinearMap) (e x)
      change e (e (f.hom (e.symm 1)) • x) = e (f.hom x)
      rw [map_zsmul]
      change e (f.hom.toLinearMap (e.symm 1)) * e x = e (f.hom.toLinearMap x)
      simpa only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply,
        mul_comm] using hf.symm
    right_inv := fun z => by
      change e (z • e.symm 1) = z
      rw [map_zsmul, LinearEquiv.apply_symm_apply]
      exact mul_one z
    map_add' := fun f g => e.map_add _ _ }
  exact { a with map_smul' := fun r x => map_intCast_smul a ℤ ℤ r x }

end PolycyclicRecognition

end

end OAI
