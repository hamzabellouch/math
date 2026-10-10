import OAI.Geometry.Relativity.CKS.SourceExteriorDefinitions

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma orientation_map_trans {V W Z : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup Z] [Module ℝ Z]
    (f : V ≃ₗ[ℝ] W) (g : W ≃ₗ[ℝ] Z) (o : Orientation ℝ V (Fin 3)) :
    Orientation.map (Fin 3) g (Orientation.map (Fin 3) f o) =
      Orientation.map (Fin 3) (f.trans g) o := by
  induction o using Module.Ray.ind with | h a ha =>
  rfl

lemma orientation_map_inverse_eq (f g : E3 ≃L[ℝ] E3)
    (h : 0 < f.toContinuousLinearMap.det * g.toContinuousLinearMap.det)
    (o : Orientation ℝ E3 (Fin 3)) :
    Orientation.map (Fin 3) f.symm.toLinearEquiv o =
      Orientation.map (Fin 3) g.symm.toLinearEquiv o := by
  apply (Orientation.map (Fin 3) g.toLinearEquiv).injective
  rw [orientation_map_trans,orientation_map_trans]
  have he : g.symm.toLinearEquiv.trans g.toLinearEquiv = LinearEquiv.refl ℝ E3 := by ext; simp
  rw [he,Orientation.map_refl,Equiv.refl_apply]
  apply (Orientation.map_eq_iff_det_pos o _ (by simp [E3])).mpr
  change 0 < LinearMap.det (g.toLinearEquiv.toLinearMap.comp f.symm.toLinearEquiv.toLinearMap)
  rw [LinearMap.det_comp]
  have hf : f.toContinuousLinearMap.det ≠ 0 := f.toLinearEquiv.isUnit_det'.ne_zero
  have hi : LinearMap.det f.symm.toLinearEquiv.toLinearMap = (f.toContinuousLinearMap.det)⁻¹ := by
    exact (LinearEquiv.coe_inv_det f.toLinearEquiv).symm.trans (by simp only [Units.val_inv_eq_inv_val,LinearEquiv.coe_det]; rfl)
  rw [hi]
  apply (mul_lt_mul_iff_of_pos_right (sq_pos_of_ne_zero hf)).mp
  have hc : (g.toContinuousLinearMap.det * (f.toContinuousLinearMap.det)⁻¹) *
      (f.toContinuousLinearMap.det)^2 = f.toContinuousLinearMap.det * g.toContinuousLinearMap.det := by
    field_simp
  change 0 * _ < (g.toContinuousLinearMap.det * (f.toContinuousLinearMap.det)⁻¹) * (f.toContinuousLinearMap.det)^2
  rwa [zero_mul,hc]

def positionTangentEquiv (p : Exterior) : TangentSpace I3 p ≃L[ℝ] E3 := by
  exact (LinearEquiv.ofBijective (ambientDerivative (position 1) p).toLinearMap
    ⟨position_derivative_injective (by norm_num) p,
      LinearMap.injective_iff_surjective.mp (position_derivative_injective (by norm_num) p)⟩).toContinuousLinearEquiv

lemma positionTangentEquiv_apply (p : Exterior) (v : TangentSpace I3 p) :
    positionTangentEquiv p v = ambientDerivative (position 1) p v := rfl

theorem source_orientable : CKSSourceExterior.Orientable (N := Exterior) := by
  let O : Orientation ℝ E3 (Fin 3) := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation
  let o := fun p : Exterior => Orientation.map (Fin 3) (positionTangentEquiv p).symm.toLinearEquiv O
  refine ⟨o,?_⟩
  intro x
  let e := trivializationAt E3 (TangentSpace I3) x
  let A : Exterior → E3 →L[ℝ] E3 := fun y =>
    (positionTangentEquiv y).toContinuousLinearMap.comp (e.symmL ℝ y)
  have hs : ContinuousAt A x := by
    convert (CKSSpatialManifold.mfderiv_gauge_smooth (I := I3) (position_smooth 1 x)).continuousAt using 1
    funext y
    ext v
    rfl
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E3 (TangentSpace I3) x
  let B := fun y (hy : y ∈ e.baseSet) => (e.continuousLinearEquivAt ℝ y hy).symm.trans (positionTangentEquiv y)
  have hB : ∀ y hy, (B y hy).toContinuousLinearMap = A y := by
    intro y hy
    ext v
    simp only [B,A,ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.trans_apply,ContinuousLinearMap.comp_apply]
    rw [Trivialization.symmL_apply e hy]
    rfl
  have hd : (A x).det ≠ 0 := by
    rw [← hB x hx]
    exact (B x hx).toLinearEquiv.isUnit_det'.ne_zero
  have hc := (ContinuousLinearMap.continuous_det.continuousAt.comp hs).mul_const (A x).det
  have hev : ∀ᶠ y in 𝓝 x, 0 < (A y).det * (A x).det :=
    hc.eventually (lt_mem_nhds (mul_self_pos.mpr hd))
  obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp (hev.and (e.open_baseSet.mem_nhds hx))
  refine ⟨V,hVo,hxV,fun y hy => (hV hy).2,?_⟩
  intro y hy
  change Orientation.map (Fin 3) (e.continuousLinearEquivAt ℝ y (hV hy).2).toLinearEquiv
      (Orientation.map (Fin 3) (positionTangentEquiv y).symm.toLinearEquiv O) =
    Orientation.map (Fin 3) (e.continuousLinearEquivAt ℝ x (hV hxV).2).toLinearEquiv
      (Orientation.map (Fin 3) (positionTangentEquiv x).symm.toLinearEquiv O)
  rw [orientation_map_trans,orientation_map_trans]
  exact orientation_map_inverse_eq (B y (hV hy).2) (B x (hV hxV).2)
    (by rw [hB,hB]; exact (hV hy).1) O
end CKSSchwarzschild

end

end OAI
