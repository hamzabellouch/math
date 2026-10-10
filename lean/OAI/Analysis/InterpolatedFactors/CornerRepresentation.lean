import OAI.Analysis.InterpolatedFactors.Basic

namespace OAI

universe u_1 u_2 u_3

noncomputable section

namespace FreeGroupFactorMain.Amplification
variable {E : Type u_3} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (K : Submodule ℂ E) [CompleteSpace K]

abbrev RangeCorner := Corner K.starProjection isStarProjection_starProjection

def cornerRestrict (x : RangeCorner K) : K →L[ℂ] K :=
  K.orthogonalProjectionOnto.comp ((x : E →L[ℂ] E).comp K.subtypeL)

def cornerExtend (x : K →L[ℂ] K) : RangeCorner K :=
  ⟨K.subtypeL.comp (x.comp K.orthogonalProjectionOnto),by
    constructor
    · ext ξ
      exact K.starProjection_mem_subspace_eq_self (x (K.orthogonalProjectionOnto ξ))
    · ext ξ
      change (x (K.orthogonalProjectionOnto (K.starProjection ξ)) : E)=_
      rw [K.orthogonalProjectionOnto_starProjection_of_le le_rfl]
      rfl⟩

theorem cornerRestrict_extend (x : K →L[ℂ] K) : cornerRestrict K (cornerExtend K x)=x := by
  ext ξ
  simp only [cornerRestrict,cornerExtend,ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

theorem cornerExtend_restrict (x : RangeCorner K) : cornerExtend K (cornerRestrict K x)=x := by
  apply Subtype.ext
  change K.starProjection*(x : E →L[ℂ] E)*K.starProjection=(x : E →L[ℂ] E)
  rw [x.property.1,x.property.2]

theorem cornerRestrict_apply (x : RangeCorner K) (ξ : K) :
    (cornerRestrict K x ξ : E)=(x : E →L[ℂ] E) ξ := by
  change K.starProjection ((x : E →L[ℂ] E) ξ)=_
  exact DFunLike.congr_fun x.property.1 (ξ:E)

def cornerRepresentation : RangeCorner K ≃⋆ₐ[ℂ] (K →L[ℂ] K) where
  toFun := cornerRestrict K
  invFun := cornerExtend K
  left_inv := cornerExtend_restrict K
  right_inv := cornerRestrict_extend K
  map_mul' x y := by
    ext ξ
    simp only [cornerRestrict_apply,mul_apply_eq_comp]
    rfl
  map_add' x y := by
    ext ξ
    simp only [cornerRestrict_apply,add_apply,Submodule.coe_add]
    rfl
  map_smul' c x := by
    ext ξ
    simp only [cornerRestrict_apply,smul_apply,SetLike.val_smul]
  map_star' x := by
    apply ContinuousLinearMap.ext
    intro ξ
    apply ext_inner_right ℂ
    intro η
    rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
    change inner ℂ (cornerRestrict K (star x) ξ : E) (η:E)=
      inner ℂ (ξ:E) (cornerRestrict K x η : E)
    rw [cornerRestrict_apply,cornerRestrict_apply]
    exact ContinuousLinearMap.adjoint_inner_left (x : E →L[ℂ] E) η ξ
end FreeGroupFactorMain.Amplification

end

end OAI
