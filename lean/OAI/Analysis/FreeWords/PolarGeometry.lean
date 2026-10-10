import Mathlib

namespace OAI

noncomputable section

namespace KKPolarSupport

open scoped InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def closedRange (S : H →L[ℂ] H) : Submodule ℂ H := S.toLinearMap.range.topologicalClosure

instance closedRange_complete (S : H →L[ℂ] H) : CompleteSpace (closedRange S) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

def closedRangeMap (S : H →L[ℂ] H) : H →L[ℂ] closedRange S :=
  S.codRestrict _ (fun x => Submodule.le_topologicalClosure _ ⟨x, rfl⟩)

omit [CompleteSpace H] in
@[simp] theorem closedRangeMap_val (S : H →L[ℂ] H) (x : H) :
    (closedRangeMap S x).1 = S x := rfl

omit [CompleteSpace H] in
theorem closedRangeMap_dense (S : H →L[ℂ] H) : DenseRange (closedRangeMap S) := by
  change DenseRange (Set.inclusion subset_closure ∘ Set.rangeFactorization S)
  exact ((denseRange_inclusion_iff subset_closure).2 subset_rfl).comp
    Set.rangeFactorization_surjective.denseRange (continuous_inclusion subset_closure)

def polarOnRange (a S : H →L[ℂ] H) : closedRange S →L[ℂ] H :=
  a.toLinearMap.extendOfNorm (closedRangeMap S).toLinearMap

theorem polarOnRange_apply (a S : H →L[ℂ] H) (hAS : ∀ x, ‖a x‖ = ‖S x‖) (x : H) :
    polarOnRange a S (closedRangeMap S x) = a x := by
  apply LinearMap.extendOfNorm_eq (closedRangeMap_dense S)
  exact ⟨1, fun x => by
    change ‖a x‖ ≤ 1 * ‖S x‖
    simpa only [one_mul] using (hAS x).le⟩

theorem polarOnRange_norm (a S : H →L[ℂ] H) (hAS : ∀ x, ‖a x‖ = ‖S x‖)
    (x : closedRange S) : ‖polarOnRange a S x‖ = ‖x‖ := by
  refine (closedRangeMap_dense S).induction_on (p := fun x => ‖polarOnRange a S x‖ = ‖x‖) x ?_ ?_
  · exact isClosed_eq (by fun_prop) continuous_norm
  · intro y
    rw [polarOnRange_apply a S hAS]
    exact hAS y

def polarOp (a S : H →L[ℂ] H) : H →L[ℂ] H :=
  (polarOnRange a S).comp (closedRange S).orthogonalProjectionOnto

theorem polarOp_apply_range (a S : H →L[ℂ] H) (hAS : ∀ x, ‖a x‖ = ‖S x‖) (x : H) :
    polarOp a S (S x) = a x := by
  change polarOnRange a S ((closedRange S).orthogonalProjectionOnto (S x)) = _
  have he : (closedRange S).orthogonalProjectionOnto (S x) = closedRangeMap S x := by
    apply Subtype.ext
    exact Submodule.starProjection_eq_self_iff.mpr (Submodule.le_topologicalClosure _ ⟨x, rfl⟩)
  rw [he, polarOnRange_apply a S hAS]

theorem polarOp_mul (a S : H →L[ℂ] H) (hAS : ∀ x, ‖a x‖ = ‖S x‖) :
    polarOp a S * S = a := by
  ext x
  exact polarOp_apply_range a S hAS x

theorem polarOp_star_mul (a S : H →L[ℂ] H) (hAS : ∀ x, ‖a x‖ = ‖S x‖) :
    star (polarOp a S) * polarOp a S = (closedRange S).starProjection := by
  let V : closedRange S →ₗᵢ[ℂ] H :=
    { toLinearMap := (polarOnRange a S).toLinearMap
      norm_map' := polarOnRange_norm a S hAS }
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  change ⟪x, (polarOp a S).adjoint (polarOp a S y)⟫_ℂ = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change ⟪V ((closedRange S).orthogonalProjectionOnto x),
      V ((closedRange S).orthogonalProjectionOnto y)⟫_ℂ = _
  rw [V.inner_map_map]
  change ⟪(closedRange S).starProjection x, (closedRange S).starProjection y⟫_ℂ = _
  rw [Submodule.inner_starProjection_left_eq_right]
  congr 1
  exact Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)

theorem polarOp_projection (a S : H →L[ℂ] H) (hAS : ∀ x, ‖a x‖ = ‖S x‖) :
    IsStarProjection (star (polarOp a S)*polarOp a S) := by
  rw [polarOp_star_mul a S hAS]
  exact isStarProjection_starProjection

theorem polarOp_partial (a S : H →L[ℂ] H) (hAS : ∀ x, ‖a x‖ = ‖S x‖) :
    polarOp a S*star (polarOp a S)*polarOp a S = polarOp a S := by
  rw [mul_assoc, polarOp_star_mul a S hAS]
  ext x
  change polarOnRange a S ((closedRange S).orthogonalProjectionOnto ((closedRange S).starProjection x)) =
    polarOnRange a S ((closedRange S).orthogonalProjectionOnto x)
  congr 1
  apply Subtype.ext
  exact (Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _))

end

end KKPolarSupport
end

end OAI
