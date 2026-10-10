import OAI.Analysis.Pureness.Tensor.SpatialSubgroupPolynomial
import OAI.Analysis.Pureness.Operators.DenseOperatorConvergence

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped Classical
local instance spatialSubgroupRestrictionDecidableEq {X : Type*} : DecidableEq X := Classical.decEq X
open scoped TensorProduct
open Filter Topology
variable {A H G : Type*} [Group G] [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hα : Function.Injective α)

def spatialSubgroupRestriction (U : Subgroup G) :
    representedSpatialTensor α (reducedGroupAlgebra G).subtype →L[ℂ]
      representedSpatialTensor α (reducedGroupAlgebra G).subtype :=
  ((spatialGroupPolynomialMap (G := G) α).comp (groupPolynomialMask U)).extendOfNorm
    (spatialGroupPolynomialMap (G := G) α)

include hα in
lemma spatialSubgroupRestriction_polynomial (U : Subgroup G) (a : G →₀ A) :
    spatialSubgroupRestriction α U (spatialGroupPolynomialMap (G := G) α a) =
      spatialGroupPolynomialMap (G := G) α (groupPolynomialMask U a) :=
  LinearMap.extendOfNorm_eq (spatialGroupPolynomialMap_denseRange (G := G) α)
    ⟨1, fun a => by simpa only [one_mul, LinearMap.comp_apply] using
      spatialGroupPolynomialMask_norm_le α hα U a⟩ a

include hα in
lemma spatialSubgroupRestriction_norm_le (U : Subgroup G)
    (x : representedSpatialTensor α (reducedGroupAlgebra G).subtype) :
    ‖spatialSubgroupRestriction α U x‖ ≤ ‖x‖ := by
  have hb : ∀ a, ‖((spatialGroupPolynomialMap (G := G) α).comp (groupPolynomialMask U)) a‖ ≤
      1 * ‖spatialGroupPolynomialMap (G := G) α a‖ := fun a => by
    simpa only [one_mul, LinearMap.comp_apply] using spatialGroupPolynomialMask_norm_le α hα U a
  simpa only [spatialSubgroupRestriction, one_mul] using LinearMap.norm_extendOfNorm_apply_le
    (spatialGroupPolynomialMap_denseRange (G := G) α) 1 hb x

include hα in
lemma spatialSubgroupRestriction_generator (U : Subgroup G) (a : A) (g : G) :
    spatialSubgroupRestriction α U (spatialCompletionMap α (reducedGroupAlgebra G).subtype
      (a ⊗ₜ[ℂ] (reducedGroupUnitary G g : reducedGroupAlgebra G))) =
    if g ∈ U then spatialCompletionMap α (reducedGroupAlgebra G).subtype
      (a ⊗ₜ[ℂ] (reducedGroupUnitary G g : reducedGroupAlgebra G)) else 0 := by
  have he := spatialSubgroupRestriction_polynomial α hα U (Finsupp.single g a)
  refine (congrArg (spatialSubgroupRestriction α U)
    (spatialGroupPolynomialMap_single α g a)).symm.trans (he.trans ?_)
  change spatialGroupPolynomialMap (G := G) α ((Finsupp.single g a).filter (fun g => g ∈ U)) = _
  by_cases hg : g ∈ U
  · exact (congrArg (spatialGroupPolynomialMap (G := G) α)
      (Finsupp.filter_single_of_pos (fun k => k ∈ U) hg)).trans
        ((spatialGroupPolynomialMap_single α g a).trans (ite_eq_left hg).symm)
  · exact (congrArg (spatialGroupPolynomialMap (G := G) α)
      (Finsupp.filter_single_of_neg (fun k => k ∈ U) hg)).trans ((map_zero _).trans (ite_eq_right hg).symm)

include hα in
lemma spatialSubgroupRestriction_fourier (U : Subgroup G) (g : G)
    (x : representedSpatialTensor α (reducedGroupAlgebra G).subtype) :
    spatialGroupFourier α g (spatialSubgroupRestriction α U x) =
      if g ∈ U then spatialGroupFourier α g x else 0 := by
  refine (spatialGroupPolynomialMap_denseRange (G := G) α).induction_on x ?_ ?_
  · apply isClosed_eq
    · exact (spatialGroupFourier α g).continuous.comp (spatialSubgroupRestriction α U).continuous
    · split_ifs
      · exact (spatialGroupFourier α g).continuous
      · exact continuous_const
  · intro a
    have he := (congrArg (spatialGroupFourier α g)
      (spatialSubgroupRestriction_polynomial α hα U a)).trans
        (spatialGroupPolynomialMap_fourier α hα (groupPolynomialMask U a) g)
    refine he.trans ?_
    change (if g ∈ U then a g else 0) = _
    rw [spatialGroupPolynomialMap_fourier α hα a g]

include hα in

theorem spatialSubgroupRestriction_tendsto (U : ℕ → Subgroup G)
    (hU : ∀ g, ∀ᶠ n in atTop, g ∈ U n)
    (x : representedSpatialTensor α (reducedGroupAlgebra G).subtype) :
    Tendsto (fun n => spatialSubgroupRestriction α (U n) x) atTop (nhds x) := by
  apply boundedOperators_tendsto_of_dense_span
    (fun p : A × G => spatialCompletionMap α (reducedGroupAlgebra G).subtype
      (p.1 ⊗ₜ[ℂ] (reducedGroupUnitary G p.2 : reducedGroupAlgebra G)))
    (spatialGroupPolynomial_dense (G := G) α) (fun n => spatialSubgroupRestriction α (U n)) 1
    (fun n x => (spatialSubgroupRestriction_norm_le α hα (U n) x).trans_eq (one_mul _).symm)
  intro p
  apply tendsto_const_nhds.congr'
  filter_upwards [hU p.2] with n hn
  exact ((spatialSubgroupRestriction_generator α hα (U n) p.1 p.2).trans (ite_eq_left hn)).symm
end CuntzPureness

end

end OAI
