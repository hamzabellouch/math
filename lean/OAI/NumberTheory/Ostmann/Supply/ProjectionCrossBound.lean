import OAI.NumberTheory.Ostmann.Supply.CenteredProjection

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (U V W : Submodule ℂ H)
variable [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]

theorem projection_cross_norm_le_half (hUV : U ⟂ V) :
    ‖U.starProjection ∘L W.starProjection ∘L V.starProjection‖ ≤ (1/2 : ℝ) := by
  refine (U.starProjection ∘L W.starProjection ∘L V.starProjection).opNorm_le_bound
    (by norm_num) (fun x => ?_)
  have hz : U.starProjection (V.starProjection x) = 0 := by
    exact DFunLike.congr_fun hUV.starProjection_comp_starProjection x
  have he : U.starProjection (W.starProjection (V.starProjection x)) =
      (1/2 : ℂ) • U.starProjection (W.reflection (V.starProjection x)) := by
    rw [Submodule.reflection_apply, two_smul, map_sub, map_add, hz, sub_zero]
    module
  change ‖U.starProjection (W.starProjection (V.starProjection x))‖ ≤ _
  rw [he, norm_smul]
  have hn : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
  rw [hn]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (U.norm_starProjection_apply_le _).trans
    ((W.reflection.norm_map _).trans_le (V.norm_starProjection_apply_le x))
end Hilbert

section Centered
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem centeredSpace_isOrtho_of_disjoint (S T : Finset ι) (hST : Disjoint S T) :
    centeredSpace S ⟂ centeredSpace T := by
  intro f hf g hg
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro x hx
  by_cases hxs : x ∈ S
  · have hxt : x ∉ T := fun hxt => Finset.disjoint_left.mp hST hxs hxt
    simp [hg.1 x hxt]
  · simp [hf.1 x hxs]

theorem centeredProjection_cross_norm_le_half (S T : Finset ι) (hST : Disjoint S T)
    (W : Submodule ℂ (EuclideanSpace ℂ ι)) :
    ‖centeredProjection S ∘L W.starProjection ∘L centeredProjection T‖ ≤ (1/2 : ℝ) :=
  projection_cross_norm_le_half _ _ _ (centeredSpace_isOrtho_of_disjoint S T hST)
end Centered
end Ostmann.Supply

end

end OAI
