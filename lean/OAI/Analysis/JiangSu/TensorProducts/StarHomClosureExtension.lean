import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CStarAlgebras.FourEdgeGroupSurgery

namespace OAI


noncomputable section

namespace StarHomClosure
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
variable (S : StarSubalgebra ℂ A) (f : S →⋆ₐ[ℂ] B) (hf : ∀ x,‖f x‖≤‖x‖)
 def inclusion : S →⋆ₐ[ℂ] S.topologicalClosure := StarSubalgebra.inclusion S.le_topologicalClosure
lemma inclusion_dense : DenseRange (inclusion S) := by
  change DenseRange (Set.inclusion S.le_topologicalClosure)
  exact (denseRange_inclusion_iff S.le_topologicalClosure).mpr subset_rfl
 def extensionLinear : S.topologicalClosure →L[ℂ] B :=
  f.toAlgHom.toLinearMap.extendOfNorm (inclusion S).toAlgHom.toLinearMap
include hf
lemma extensionLinear_eq (x : S) : extensionLinear S f (inclusion S x)=f x := by
  apply LinearMap.extendOfNorm_eq (inclusion_dense S)
  refine ⟨1,fun x => ?_⟩
  change ‖f x‖≤(1:ℝ)*‖(x:A)‖
  rw [one_mul, ← AddSubgroupClass.coe_norm S x]
  exact hf x
 def extension : S.topologicalClosure →⋆ₐ[ℂ] B where
  toFun := extensionLinear S f
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    have he := extensionLinear_eq S f hf (1:S)
    simpa only [map_one] using he
  map_mul' x y := by
    refine (inclusion_dense S).induction_on₂ ?_ ?_ x y
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro a b
      rw [←map_mul (inclusion S),extensionLinear_eq _ _ hf,map_mul,
        extensionLinear_eq _ _ hf,extensionLinear_eq _ _ hf]
  commutes' z := by
    calc
      extensionLinear S f (algebraMap ℂ S.topologicalClosure z)=
          extensionLinear S f (inclusion S (algebraMap ℂ S z)) :=
        congrArg (extensionLinear S f) ((inclusion S).commutes z).symm
      _=f (algebraMap ℂ S z) := extensionLinear_eq S f hf _
      _=algebraMap ℂ B z := f.commutes z
  map_star' x := by
    refine (inclusion_dense S).induction_on x ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro a
      rw [←map_star (inclusion S),extensionLinear_eq _ _ hf,map_star,extensionLinear_eq _ _ hf]
lemma extension_eq (x : S) : extension S f hf (inclusion S x)=f x :=
  extensionLinear_eq S f hf x
lemma extension_continuous : Continuous (extension S f hf) := (extensionLinear S f).continuous
lemma extension_norm (x : S.topologicalClosure) : ‖extension S f hf x‖≤‖x‖ := by
  change ‖extensionLinear S f x‖≤‖x‖
  simpa only [one_mul,extensionLinear] using LinearMap.norm_extendOfNorm_apply_le (f := f.toAlgHom.toLinearMap)
    (e := (inclusion S).toAlgHom.toLinearMap) (inclusion_dense S) 1
    (fun a => by
      change ‖f a‖≤(1:ℝ)*‖(a:A)‖
      rw [one_mul, ← AddSubgroupClass.coe_norm S a]
      exact hf a) x
end StarHomClosure

end

end OAI
