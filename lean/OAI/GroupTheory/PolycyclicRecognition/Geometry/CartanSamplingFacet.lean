import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightSamplingSupport
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTemplateSupports

namespace OAI

/-! # The actual contact pivot and active constraints of the sampling cell -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set

theorem exists_sampling_contact_facet
    {W I : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [Fintype I]
    (α : I → W →L[ℝ] ℝ) (hne : ∀ i, α i ≠ 0) (i : I) :
    ∃ p : W, p ∈ weightSamplingPolytope α ∧ α i p = ‖α i‖ ∧
      ∀ j, α j p = ‖α j‖ → ∃ t : ℝ, 0 < t ∧ α j = t • α i := by
  obtain ⟨p, hp, hval, hstrict⟩ := exists_weight_contact_point (α i) (hne i)
  refine ⟨p, closedBall_subset_weightSamplingPolytope α (by simpa only
    [Metric.mem_closedBall, dist_zero_right, hp] using le_refl (1 : ℝ)), hval, ?_⟩
  intro j hj
  by_contra hn
  exact (ne_of_lt (hstrict (α j) (hne j) hn)) hj

namespace CartanWordModel

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- Every generator facet has a concrete Cartan pivot. All constraints
active there are positive multiples of that generator's height weight. -/
theorem exists_sampling_contact_pivot (i : Fin M.letterCount) :
    let D := M.supportIn T hunimod eW
    let α := fun j => (D.weight j).toContinuousLinearMap
    ∃ p : H, eW (heightProjection T.character (p : L)) ∈ weightSamplingPolytope α ∧
      M.weight i p = ‖α i‖ ∧
      ∀ j, α j (eW (heightProjection T.character (p : L))) = ‖α j‖ →
        ∃ t : ℝ, 0 < t ∧ D.weight j = t • D.weight i := by
  dsimp only
  let D := M.supportIn T hunimod eW
  let α := fun j => (D.weight j).toContinuousLinearMap
  have hweight j (v : H) : α j (eW (heightProjection T.character (v : L))) = M.weight j v := by
    change cartanHeightWeight T H (M.weight j)
      (eW.symm (eW (heightProjection T.character (v : L)))) = _
    rw [eW.symm_apply_apply, cartanHeightWeight_projection]
  have hne j : α j ≠ 0 := by
    intro hz
    apply M.weight_nonzero j
    funext v
    change M.weight j v = 0
    have hv := congrArg (fun q : W →L[ℝ] ℝ => q (eW (heightProjection T.character (v : L)))) hz
    change α j (eW (heightProjection T.character (v : L))) = 0 at hv
    rwa [hweight] at hv
  obtain ⟨w, hw, hval, hactive⟩ := exists_sampling_contact_facet α hne i
  let p := cartanHeightSection T H (eW.symm w)
  have hp : eW (heightProjection T.character (p : L)) = w := by
    simp only [p, cartanHeightSection_height, eW.apply_symm_apply]
  refine ⟨p, hp ▸ hw, ?_, ?_⟩
  · rw [← hweight i p, hp]
    exact hval
  · intro j hj
    rw [hp] at hj
    obtain ⟨t, ht, he⟩ := hactive j hj
    exact ⟨t, ht, congrArg ContinuousLinearMap.toLinearMap he⟩

end CartanWordModel
end PolycyclicRecognition

end

end OAI
