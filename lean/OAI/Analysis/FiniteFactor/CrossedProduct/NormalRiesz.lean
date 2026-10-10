import OAI.Analysis.FiniteFactor.CrossedProduct.VectorFunctionalRelations

namespace OAI

namespace FiniteFactor
noncomputable section

def sourceNormalRieszLinear (θ : SourceCoordinate → ℝ)
    (F : StrongDual ℂ (SourceNormalPredualSpace θ)) (η : SourceHilbert SourceCoordinate) :
    SourceHilbert SourceCoordinate →ₗ[ℂ] ℂ where
  toFun ξ := star (F (sourceVectorInSpace θ ξ η))
  map_add' ξ ξ' := by
    exact (congrArg (fun v : SourceNormalPredualSpace θ => star (F v))
      (sourceVectorInSpace_add_left θ ξ ξ' η)).trans
        ((congrArg star (F.map_add _ _)).trans (star_add _ _))
  map_smul' c ξ := by
    calc
      _ = star (F (star c • sourceVectorInSpace θ ξ η)) :=
        congrArg (fun v : SourceNormalPredualSpace θ => star (F v))
          (sourceVectorInSpace_smul_left θ c ξ η)
      _ = star (star c * F (sourceVectorInSpace θ ξ η)) := congrArg star (F.map_smul (star c) _)
      _ = c * star (F (sourceVectorInSpace θ ξ η)) := by simp [star_mul,mul_comm]

theorem sourceNormalRieszLinear_bound (θ : SourceCoordinate → ℝ)
    (F : StrongDual ℂ (SourceNormalPredualSpace θ)) (η ξ : SourceHilbert SourceCoordinate) :
    ‖sourceNormalRieszLinear θ F η ξ‖ ≤ (‖F‖*‖η‖)*‖ξ‖ := by
  change ‖star (F (sourceVectorInSpace θ ξ η))‖ ≤ _
  rw [norm_star]
  calc
    _ ≤ ‖F‖*‖sourceVectorInSpace θ ξ η‖ := F.le_opNorm _
    _ ≤ ‖F‖*(‖ξ‖*‖η‖) := mul_le_mul_of_nonneg_left (sourceVectorFunctional_norm θ ξ η) (norm_nonneg _)
    _ = (‖F‖*‖η‖)*‖ξ‖ := by ring

def sourceNormalRieszFunctional (θ : SourceCoordinate → ℝ)
    (F : StrongDual ℂ (SourceNormalPredualSpace θ)) (η : SourceHilbert SourceCoordinate) :
    StrongDual ℂ (SourceHilbert SourceCoordinate) :=
  (sourceNormalRieszLinear θ F η).mkContinuous (‖F‖*‖η‖) (sourceNormalRieszLinear_bound θ F η)

def sourceNormalRieszVector (θ : SourceCoordinate → ℝ)
    (F : StrongDual ℂ (SourceNormalPredualSpace θ)) (η : SourceHilbert SourceCoordinate) :
    SourceHilbert SourceCoordinate :=
  (InnerProductSpace.toDual ℂ (SourceHilbert SourceCoordinate)).symm (sourceNormalRieszFunctional θ F η)

theorem sourceNormalRieszVector_inner (θ : SourceCoordinate → ℝ)
    (F : StrongDual ℂ (SourceNormalPredualSpace θ)) (ξ η : SourceHilbert SourceCoordinate) :
    inner ℂ ξ (sourceNormalRieszVector θ F η) = F (sourceVectorInSpace θ ξ η) := by
  have he := congrArg (fun f : StrongDual ℂ (SourceHilbert SourceCoordinate) => f ξ)
    ((InnerProductSpace.toDual ℂ (SourceHilbert SourceCoordinate)).apply_symm_apply
      (sourceNormalRieszFunctional θ F η))
  change inner ℂ (sourceNormalRieszVector θ F η) ξ = star (F (sourceVectorInSpace θ ξ η)) at he
  have hs := congrArg star he
  calc
    _ = star (inner ℂ (sourceNormalRieszVector θ F η) ξ) := (inner_conj_symm ξ _).symm
    _ = _ := by simpa only [star_star] using hs

theorem sourceNormalRieszVector_norm (θ : SourceCoordinate → ℝ)
    (F : StrongDual ℂ (SourceNormalPredualSpace θ)) (η : SourceHilbert SourceCoordinate) :
    ‖sourceNormalRieszVector θ F η‖ ≤ ‖F‖*‖η‖ := by
  rw [sourceNormalRieszVector,LinearIsometryEquiv.norm_map]
  exact LinearMap.mkContinuous_norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _

/-- Every functional on the constructed Banach space gives an actual bounded
operator by Riesz representation. Membership in the source algebra is proved
separately by commutation, not assumed here. -/
def sourceNormalRieszOperator (θ : SourceCoordinate → ℝ)
    (F : StrongDual ℂ (SourceNormalPredualSpace θ)) :
    SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate :=
  LinearMap.mkContinuous
    { toFun := sourceNormalRieszVector θ F
      map_add' := fun η η' => by
        apply ext_inner_left ℂ
        intro ξ
        rw [inner_add_right,sourceNormalRieszVector_inner,sourceNormalRieszVector_inner,
          sourceNormalRieszVector_inner,sourceVectorInSpace_add_right,map_add]
      map_smul' := fun c η => by
        apply ext_inner_left ℂ
        intro ξ
        rw [inner_smul_right,sourceNormalRieszVector_inner,sourceNormalRieszVector_inner,
          sourceVectorInSpace_smul_right,map_smul]
        rfl }
    ‖F‖ (sourceNormalRieszVector_norm θ F)

theorem sourceNormalRieszOperator_inner (θ : SourceCoordinate → ℝ)
    (F : StrongDual ℂ (SourceNormalPredualSpace θ)) (ξ η : SourceHilbert SourceCoordinate) :
    inner ℂ ξ (sourceNormalRieszOperator θ F η) = F (sourceVectorInSpace θ ξ η) :=
  sourceNormalRieszVector_inner θ F ξ η

theorem sourceNormalRieszOperator_norm (θ : SourceCoordinate → ℝ)
    (F : StrongDual ℂ (SourceNormalPredualSpace θ)) : ‖sourceNormalRieszOperator θ F‖ ≤ ‖F‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

end
end FiniteFactor

end OAI
