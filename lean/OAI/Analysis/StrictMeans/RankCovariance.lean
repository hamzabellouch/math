import OAI.Analysis.StrictMeans.CriticalCovariance

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma signedCriticalFiber_rebase (k : ℝ) (f : DiskFamily) (ξ : ℂ)
    (z : UpperHalfPlane) (positive : Bool) :
    signedCriticalFiber k (rebase f z) (targetRebase f z ξ) positive =
      (affineUpperHomeomorph z) ⁻¹' signedCriticalFiber k f ξ positive := by
  ext w
  simp only [signedCriticalFiber,mem_ofPred_eq,mem_preimage,affineUpperHomeomorph_apply,
    criticalMap_rebase_eq_iff,jacobianExpression_rebase,coe_affineProduct]

lemma criticalRank_rebase (k : ℝ) (f : DiskFamily) (ξ : ℂ)
    (z w : UpperHalfPlane) (positive : Bool) :
    criticalRank k (rebase f z) (targetRebase f z ξ) positive w =
      criticalRank k f ξ positive (affineProduct z w) := by
  unfold criticalRank descendingRank
  have he : {v | v ∈ signedCriticalFiber k (rebase f z) (targetRebase f z ξ) positive ∧
      criticalHeight k (halfPlaneFunction (rebase f z)) w <
        criticalHeight k (halfPlaneFunction (rebase f z)) v} =
      (affineUpperHomeomorph z) ⁻¹' {v | v ∈ signedCriticalFiber k f ξ positive ∧
        criticalHeight k (halfPlaneFunction f) (affineProduct z w) <
          criticalHeight k (halfPlaneFunction f) v} := by
    ext v
    simp only [signedCriticalFiber_rebase,mem_ofPred_eq,mem_preimage,
      affineUpperHomeomorph_apply,criticalHeight_rebase,
      mul_lt_mul_iff_right₀ (heightRebaseScale_pos k f z)]
  rw [he]
  exact Set.ncard_preimage_of_injective_subset_range (affineUpperHomeomorph z).injective
    (by rw [(affineUpperHomeomorph z).surjective.range_eq]; exact subset_univ _)

lemma rankPairRelation_rebase_iff {k : ℝ} {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) (z w v : UpperHalfPlane) :
    RankPairRelation k ⟨((rebase f z,targetRebase f z ξ),w),goodPair_rebase hg z⟩ v ↔
      RankPairRelation k ⟨((f,ξ),affineProduct z w),hg⟩ (affineProduct z v) := by
  simp only [RankPairRelation,signedCriticalFiber_rebase,mem_preimage,
    affineUpperHomeomorph_apply,criticalRank_rebase,criticalHeight_rebase,
    mul_lt_mul_iff_right₀ (heightRebaseScale_pos k f z)]

lemma rankPairingDomain_rebase_iff {k : ℝ} {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) (z w : UpperHalfPlane) :
    (⟨((rebase f z,targetRebase f z ξ),w),goodPair_rebase hg z⟩ : RankParameters k) ∈
      rankPairingDomain k ↔
    (⟨((f,ξ),affineProduct z w),hg⟩ : RankParameters k) ∈ rankPairingDomain k := by
  change (∃ v, RankPairRelation k _ v) ↔ ∃ v, RankPairRelation k _ v
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨affineProduct z v,(rankPairRelation_rebase_iff hg z w v).mp hv⟩
  · rintro ⟨v,hv⟩
    obtain ⟨a,ha⟩ := (affineUpperHomeomorph z).surjective v
    change affineProduct z a = v at ha
    refine ⟨a,(rankPairRelation_rebase_iff hg z w a).mpr ?_⟩
    rw [ha]
    exact hv

lemma availableRankPartner_rebase {k : ℝ} (hk : 0 < k) {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) (z w : UpperHalfPlane)
    (hp : (⟨((rebase f z,targetRebase f z ξ),w),goodPair_rebase hg z⟩ : RankParameters k) ∈
      rankPairingDomain k) :
    availableRankPartner k ⟨⟨((f,ξ),affineProduct z w),hg⟩,
      (rankPairingDomain_rebase_iff hg z w).mp hp⟩ =
    affineProduct z (availableRankPartner k ⟨⟨((rebase f z,targetRebase f z ξ),w),
      goodPair_rebase hg z⟩,hp⟩) := by
  let p : AvailableRankPair k :=
    ⟨⟨((rebase f z,targetRebase f z ξ),w),goodPair_rebase hg z⟩,hp⟩
  let q : AvailableRankPair k := ⟨⟨((f,ξ),affineProduct z w),hg⟩,
    (rankPairingDomain_rebase_iff hg z w).mp hp⟩
  change availableRankPartner k q = affineProduct z (availableRankPartner k p)
  have hp' := availableRankPartner_spec k p
  have hq' := availableRankPartner_spec k q
  have hr : RankPairRelation k q.1 (affineProduct z (availableRankPartner k p)) :=
    (rankPairRelation_rebase_iff hg z w (availableRankPartner k p)).mp hp'
  exact rankPairRelation_unique hk hq' hr

end
end StrictInverseFirstPower

end

end OAI
